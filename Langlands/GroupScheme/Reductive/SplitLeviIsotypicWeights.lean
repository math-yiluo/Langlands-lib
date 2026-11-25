import Langlands.GroupScheme.Reductive.SplitLeviComparison
import Langlands.GroupScheme.MatrixRepresentation.CentralizerCharacterSpaces
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterRepresentation
import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation
import Langlands.GroupScheme.MatrixRepresentation.CharacterIntertwiners
import Langlands.GroupScheme.Chevalley.ActualRepresentationExtension
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedRepresentation

/-! # Weights of the split-isotypic part of a representation on a Levi comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Let `V` be an independent spanning family of subspaces, and let `W` and `X` be independent
families such that every `V i` lies in `W (π i)` and in `X (κ i)`. Then `W a ⊓ X c` lies in
the sum of the `V i` with `π i = a` and `κ i = c`. -/
theorem inf_le_iSup_of_iSupIndep {R M ι α β : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {V : ι → Submodule R M} {W : α → Submodule R M} {X : β → Submodule R M}
    (hV : (⨆ i, V i) = ⊤) (hW : iSupIndep W) (hX : iSupIndep X)
    (π : ι → α) (κ : ι → β) (hVW : ∀ i, V i ≤ W (π i)) (hVX : ∀ i, V i ≤ X (κ i))
    (a : α) (c : β) :
    W a ⊓ X c ≤ ⨆ (i) (_ : π i = a ∧ κ i = c), V i := by
  classical
  rintro w ⟨hwW, hwX⟩
  have hw : w ∈ ⨆ i, V i := by rw [hV]; trivial
  obtain ⟨f, hf, hfw⟩ := (Submodule.mem_iSup_iff_exists_finsupp V w).mp hw
  set s := f.support
  set u := ∑ i ∈ s.filter (fun i => π i = a ∧ κ i = c), f i with hu_def
  set A1 := ∑ i ∈ s.filter (fun i => ¬ π i = a), f i with hA1_def
  set A2 := ∑ i ∈ s.filter (fun i => π i = a ∧ ¬ κ i = c), f i with hA2_def
  have hsplit : w = u + A1 + A2 := by
    rw [← hfw, Finsupp.sum]
    rw [← Finset.sum_filter_add_sum_filter_not s (fun i => π i = a)]
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter fun i => π i = a)
      (fun i => κ i = c)]
    simp only [Finset.filter_filter, hu_def, hA1_def, hA2_def]
    abel
  have hu : u ∈ ⨆ (i) (_ : π i = a ∧ κ i = c), V i :=
    Submodule.sum_mem _ fun i hi =>
      Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem (Finset.mem_filter.mp hi).2 (hf i))
  have huW : u ∈ W a := Submodule.sum_mem _ fun i hi => by
    have := (Finset.mem_filter.mp hi).2.1
    exact this ▸ hVW i (hf i)
  have huX : u ∈ X c := Submodule.sum_mem _ fun i hi => by
    have := (Finset.mem_filter.mp hi).2.2
    exact this ▸ hVX i (hf i)
  have hA2W : A2 ∈ W a := Submodule.sum_mem _ fun i hi => by
    have := (Finset.mem_filter.mp hi).2.1
    exact this ▸ hVW i (hf i)
  have hA2X : A2 ∈ ⨆ (c') (_ : c' ≠ c), X c' := Submodule.sum_mem _ fun i hi =>
    Submodule.mem_iSup_of_mem (κ i)
      (Submodule.mem_iSup_of_mem (Finset.mem_filter.mp hi).2.2 (hVX i (hf i)))
  have hA1 : A1 ∈ ⨆ (a') (_ : a' ≠ a), W a' := Submodule.sum_mem _ fun i hi =>
    Submodule.mem_iSup_of_mem (π i)
      (Submodule.mem_iSup_of_mem (Finset.mem_filter.mp hi).2 (hVW i (hf i)))
  have hA1W : A1 ∈ W a := by
    have : A1 = w - u - A2 := by rw [hsplit]; abel
    rw [this]
    exact sub_mem (sub_mem hwW huW) hA2W
  have hA10 : A1 = 0 := (Submodule.disjoint_def.mp (hW a)) A1 hA1W hA1
  have hA2X' : A2 ∈ X c := by
    have : A2 = w - u := by rw [hsplit, hA10]; abel
    rw [this]
    exact sub_mem hwX huX
  have hA20 : A2 = 0 := (Submodule.disjoint_def.mp (hX c)) A2 hA2X' hA2X
  rw [hsplit, hA10, hA20, add_zero, add_zero]
  exact hu

namespace SplitPinning

open MatrixRepresentation

variable {F : Type u} [Field F] {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom H.X.hom] {n : Type} [Fintype n] [DecidableEq n]

/-- The weight space of the coordinate subrepresentation on a stable subspace `V` is
identified, by the coordinate inclusion, with the weight space of the ambient representation
intersected with `V`. -/
def representationWeightSpaceRestrictCoordinatesEquiv (q : SplitPinning H)
    (ρ : MatrixRepresentation H n) (V : Submodule F (n → F)) {m : ℕ}
    (B : Matrix n (Fin m) F) (C : Matrix (Fin m) n F) (hCB : C * B = 1)
    (hcols : ∀ j, (fun r => B r j) ∈ V) (hproj : ∀ v, v ∈ V → (B * C) *ᵥ v = v)
    (hst : ρ.IsStableCoordinates B C) (ν : characterLattice q.torus) :
    q.representationWeightSpace (restrictCoordinates ρ B C hCB hst) ν ≃ₗ[F]
      (q.representationWeightSpace ρ ν ⊓ V : Submodule F (n → F)) := by
  have := q.isSplitTorus.isAffineHom
  have hrange : ∀ w, B *ᵥ w ∈ V := fun w => by
    rw [← range_coordinateInclusion_eq V B C hcols hproj]
    exact ⟨w, rfl⟩
  have hint := (intertwines_restrictCoordinates ρ B C hCB hst).restrict q.inclusion
  let f : q.representationWeightSpace (restrictCoordinates ρ B C hCB hst) ν →ₗ[F]
      (q.representationWeightSpace ρ ν ⊓ V : Submodule F (n → F)) :=
    { toFun := fun w => ⟨B *ᵥ (w : Fin m → F),
        ⟨Intertwines.mem_characterSpace hint w.2, hrange _⟩⟩
      map_add' := fun w w' => by ext1; simp [Matrix.mulVec_add]
      map_smul' := fun c w => by ext1; simp [Matrix.mulVec_smul] }
  refine LinearEquiv.ofBijective f ⟨fun w w' hww' => ?_, fun v => ?_⟩
  · apply Subtype.ext
    exact coordinateInclusion_injective (R := CommRingCat.of F) B C hCB
      (show B *ᵥ (w : Fin m → F) = B *ᵥ (w' : Fin m → F) from congrArg Subtype.val hww')
  · have hv := v.2
    refine ⟨⟨C *ᵥ (v : n → F), ?_⟩, ?_⟩
    · exact characterSpace_restrictCoordinates ρ q.inclusion B C hCB hst hv.1 (hproj _ hv.2)
    · apply Subtype.ext
      change B *ᵥ (C *ᵥ (v : n → F)) = v
      rw [Matrix.mulVec_mulVec, hproj _ hv.2]

theorem finrank_representationWeightSpace_restrictCoordinates (q : SplitPinning H)
    (ρ : MatrixRepresentation H n) (V : Submodule F (n → F)) {m : ℕ}
    (B : Matrix n (Fin m) F) (C : Matrix (Fin m) n F) (hCB : C * B = 1)
    (hcols : ∀ j, (fun r => B r j) ∈ V) (hproj : ∀ v, v ∈ V → (B * C) *ᵥ v = v)
    (hst : ρ.IsStableCoordinates B C) (ν : characterLattice q.torus) :
    Module.finrank F (q.representationWeightSpace (restrictCoordinates ρ B C hCB hst) ν) =
      Module.finrank F (q.representationWeightSpace ρ ν ⊓ V : Submodule F (n → F)) :=
  (q.representationWeightSpaceRestrictCoordinatesEquiv ρ V B C hCB hcols hproj hst ν).finrank_eq

theorem inf_ne_bot_of_representationWeightSpace_restrictCoordinates_ne_bot
    (q : SplitPinning H)
    (ρ : MatrixRepresentation H n) (V : Submodule F (n → F)) {m : ℕ}
    (B : Matrix n (Fin m) F) (C : Matrix (Fin m) n F) (hCB : C * B = 1)
    (hcols : ∀ j, (fun r => B r j) ∈ V) (hproj : ∀ v, v ∈ V → (B * C) *ᵥ v = v)
    (hst : ρ.IsStableCoordinates B C) {ν : characterLattice q.torus}
    (hν : q.representationWeightSpace (restrictCoordinates ρ B C hCB hst) ν ≠ ⊥) :
    (q.representationWeightSpace ρ ν ⊓ V : Submodule F (n → F)) ≠ ⊥ := by
  intro h
  apply hν
  let e := q.representationWeightSpaceRestrictCoordinatesEquiv ρ V B C hCB hcols hproj hst ν
  rw [Submodule.eq_bot_iff]
  intro w hw
  have h0 : e ⟨w, hw⟩ = 0 := by
    apply Subtype.ext
    exact (Submodule.mem_bot F).mp (h.le (e ⟨w, hw⟩).2)
  have := e.injective (h0.trans e.map_zero.symm)
  exact congrArg Subtype.val this

end SplitPinning
namespace GaloisPinningData

open MatrixRepresentation

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {G D : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom D.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

namespace SplitTorusDatum

variable {d : GaloisPinningData F K G}

/-- The base change of the split torus is affine. -/
theorem isAffineHom_baseChange (s : d.SplitTorusDatum) :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F K)).obj s.splitTorus.toGrp).X.hom :=
  (s.isSplitTorus.baseChange _).isAffineHom

/-- The character of the base-changed split torus obtained by restricting an absolute
character along the base-changed torus map. -/
def splitCharacter (s : d.SplitTorusDatum) (μ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)) :
    rationalCharacters ((GroupScheme.baseChange (algebraBaseMap F K)).obj s.splitTorus.toGrp) :=
  characterPrecompInt ((CommGroupScheme.baseChange (algebraBaseMap F K)).map s.torusMap) μ

/-- The isotypic subspace of a representation of `G_K` for the restriction of an absolute
character `μ` to the base-changed split torus. -/
def isotypicSubspace (s : d.SplitTorusDatum) (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n) (μ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)) :
    Submodule K (n → K) :=
  letI := s.isAffineHom_baseChange
  (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map
    s.splitInclusion)).characterSpace (s.splitCharacter μ)

/-- Every absolute weight space lies in the isotypic subspace of its restriction to the
split torus. -/
theorem representationWeightSpace_le_isotypicSubspace (s : d.SplitTorusDatum) (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n)
    (μ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)) : d.toSplitPinning.representationWeightSpace ρ μ ≤ s.isotypicSubspace ρ μ := by
  have := s.isAffineHom_baseChange
  have := d.toSplitPinning.isSplitTorus.isAffineHom
  have hsq : (GroupScheme.baseChange (algebraBaseMap F K)).map s.splitInclusion =
      (GroupScheme.baseChange (algebraBaseMap F K)).map
        (CommGroupScheme.groupHom s.torusMap) ≫ d.toSplitPinning.inclusion := by
    rw [← s.square, Functor.map_comp]
    rfl
  unfold isotypicSubspace SplitPinning.representationWeightSpace
  rw [hsq, ← restrict_comp]
  exact characterSpace_le_restrict _ _ _

theorem splitCharacter_sub (s : d.SplitTorusDatum) (μ μ' : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)) :
    s.splitCharacter (μ - μ') = s.splitCharacter μ - s.splitCharacter μ' :=
  map_sub (characterPrecompInt
    ((CommGroupScheme.baseChange (algebraBaseMap F K)).map s.torusMap)) μ μ'

theorem restriction_eq_zero_of_splitCharacter_eq (s : d.SplitTorusDatum) {μ μ' : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)}
    (h : s.splitCharacter μ = s.splitCharacter μ') : s.restriction (μ - μ') = 0 := by
  have h0 : s.splitCharacter (μ - μ') = 0 := by rw [splitCharacter_sub, h, sub_self]
  change (characterLattice.baseChangeEquiv (algebraBaseMap F K) s.splitTorus
    s.isSplitTorus).symm (s.splitCharacter (μ - μ')) = 0
  rw [h0, AddEquiv.map_zero]

end SplitTorusDatum

namespace LeviComparison

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType D.X.hom]
  {d : GaloisPinningData F K G} {s : d.SplitTorusDatum} {ι : D ⟶ G}
  {e : GaloisPinningData F K D}

/-- Every absolute weight space of `G_K` lies in the weight space of the restricted
representation of `D_K` at the restricted weight. -/
theorem representationWeightSpace_le_restrict (L : d.LeviComparison s ι e) (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n)
    (μ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)) :
    d.toSplitPinning.representationWeightSpace ρ μ ≤
      e.toSplitPinning.representationWeightSpace
        (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι))
        (L.weightRestriction μ) := by
  have := d.toSplitPinning.isSplitTorus.isAffineHom
  have := e.toSplitPinning.isSplitTorus.isAffineHom
  have hsq : e.toSplitPinning.inclusion ≫ (GroupScheme.baseChange (algebraBaseMap F K)).map ι =
      (GroupScheme.baseChange (algebraBaseMap F K)).map
        (CommGroupScheme.groupHom L.kernelTorusMap) ≫ d.toSplitPinning.inclusion := by
    change (GroupScheme.baseChange (algebraBaseMap F K)).map e.inclusion ≫ _ = _
    rw [← Functor.map_comp, ← L.kernelSquare, Functor.map_comp]
    rfl
  unfold SplitPinning.representationWeightSpace
  rw [restrict_comp, hsq, ← restrict_comp]
  exact characterSpace_le_restrict _ _ _

/-- The weight spaces of `D_K` inside an isotypic subspace are spanned by the absolute weight
spaces with the prescribed restrictions to the torus of `D` and to the split torus. -/
theorem representationWeightSpace_inf_isotypicSubspace_le (L : d.LeviComparison s ι e)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n) (ν : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj e.torus)) (μ₀ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)) :
    e.toSplitPinning.representationWeightSpace
        (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι)) ν ⊓
      s.isotypicSubspace ρ μ₀ ≤
      ⨆ (μ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)) (_ : L.weightRestriction μ = ν ∧ s.splitCharacter μ = s.splitCharacter μ₀),
        d.toSplitPinning.representationWeightSpace ρ μ := by
  have := s.isAffineHom_baseChange
  have := d.toSplitPinning.isSplitTorus.isAffineHom
  have := e.toSplitPinning.isSplitTorus.isAffineHom
  have hV : (⨆ μ, d.toSplitPinning.representationWeightSpace ρ μ) = ⊤ :=
    iSup_characterSpace_eq_top_of_isSplitTorus d.toSplitPinning.isSplitTorus
      (ρ.restrict d.toSplitPinning.inclusion)
  have hW : iSupIndep (fun ν => e.toSplitPinning.representationWeightSpace
      (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι)) ν) :=
    characterSpace_iSupIndep _
  have hX : iSupIndep (fun χ => (ρ.restrict ((GroupScheme.baseChange
      (algebraBaseMap F K)).map s.splitInclusion)).characterSpace χ) :=
    characterSpace_iSupIndep _
  exact inf_le_iSup_of_iSupIndep hV hW hX L.weightRestriction s.splitCharacter
    (L.representationWeightSpace_le_restrict ρ)
    (s.representationWeightSpace_le_isotypicSubspace ρ) ν (s.splitCharacter μ₀)

/-- For a representation of highest weight `λ`, an absolute weight with nonzero weight space
and the same restriction to the split torus differs from `λ` by an element of the zero-vertex
root monoid. -/
theorem sub_mem_zeroRootMonoid (L : d.LeviComparison s ι e) {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n} {lam : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)}
    (hρ : d.toSplitPinning.IsHighestWeight ρ lam) {μ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)}
    (hμ : d.toSplitPinning.representationWeightSpace ρ μ ≠ ⊥)
    (hS : s.splitCharacter μ = s.splitCharacter lam) :
    lam - μ ∈ s.zeroRootMonoid :=
  L.mem_zeroRootMonoid (hρ.2.2.2 μ hμ) (s.restriction_eq_zero_of_splitCharacter_eq hS.symm)

/-- Inside the isotypic subspace of a representation of highest weight `λ`, the weight space
of `D_K` at `λ|T_D` is exactly the highest weight line. -/
theorem representationWeightSpace_inf_isotypicSubspace_eq (L : d.LeviComparison s ι e)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n} {lam : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)} (hρ : d.toSplitPinning.IsHighestWeight ρ lam) :
    e.toSplitPinning.representationWeightSpace
        (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι))
        (L.weightRestriction lam) ⊓ s.isotypicSubspace ρ lam =
      d.toSplitPinning.representationWeightSpace ρ lam := by
  apply le_antisymm
  · refine (L.representationWeightSpace_inf_isotypicSubspace_le ρ _ lam).trans ?_
    refine iSup_le fun μ => iSup_le fun hμ => ?_
    by_cases h0 : d.toSplitPinning.representationWeightSpace ρ μ = ⊥
    · rw [h0]; exact bot_le
    · have hmem := L.sub_mem_zeroRootMonoid hρ h0 hμ.2
      have hz : L.weightRestriction (lam - μ) = 0 := by rw [map_sub, hμ.1, sub_self]
      have := L.eq_zero_of_weightRestriction_eq_zero hmem hz
      rw [sub_eq_zero] at this
      rw [this]
  · exact le_inf (L.representationWeightSpace_le_restrict ρ lam)
      (s.representationWeightSpace_le_isotypicSubspace ρ lam)

/-- Inside the isotypic subspace of a representation of highest weight `λ`, the weight
`λ|T_D` of `D_K` has multiplicity one. -/
theorem finrank_representationWeightSpace_inf_isotypicSubspace (L : d.LeviComparison s ι e)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n} {lam : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)} (hρ : d.toSplitPinning.IsHighestWeight ρ lam) :
    Module.finrank K
      (e.toSplitPinning.representationWeightSpace
        (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι))
        (L.weightRestriction lam) ⊓ s.isotypicSubspace ρ lam : Submodule _ _) = 1 := by
  rw [L.representationWeightSpace_inf_isotypicSubspace_eq hρ]
  exact hρ.2.2.1

/-- Inside the isotypic subspace of a representation of highest weight `λ`, every weight of
`D_K` lies below `λ|T_D`. -/
theorem sub_mem_positiveRootMonoid_of_inf_ne_bot (L : d.LeviComparison s ι e)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n} {lam : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)} (hρ : d.toSplitPinning.IsHighestWeight ρ lam) {ν : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj e.torus)}
    (hne : e.toSplitPinning.representationWeightSpace
        (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι))
        ν ⊓ s.isotypicSubspace ρ lam ≠ ⊥) :
    L.weightRestriction lam - ν ∈ e.toSplitPinning.positiveRootMonoid := by
  by_contra hnot
  apply hne
  refine eq_bot_iff.mpr ((L.representationWeightSpace_inf_isotypicSubspace_le ρ ν lam).trans ?_)
  refine iSup_le fun μ => iSup_le fun hμ => ?_
  by_cases h0 : d.toSplitPinning.representationWeightSpace ρ μ = ⊥
  · rw [h0]
  · exfalso
    apply hnot
    have hmem := L.sub_mem_zeroRootMonoid hρ h0 hμ.2
    have := L.weightRestriction_mem_positiveRootMonoid hmem
    rwa [map_sub, hμ.1] at this

/-- Inside the isotypic subspace of a representation of highest weight `λ`, the weight
`λ|T_D` is maximal: no other weight of `D_K` there lies above it. -/
theorem eq_of_inf_ne_bot_of_sub_mem (L : d.LeviComparison s ι e)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n} {lam : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)} (hρ : d.toSplitPinning.IsHighestWeight ρ lam) {ν : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj e.torus)}
    (hne : e.toSplitPinning.representationWeightSpace
        (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι))
        ν ⊓ s.isotypicSubspace ρ lam ≠ ⊥)
    (hle : ν - L.weightRestriction lam ∈ e.toSplitPinning.positiveRootMonoid) :
    ν = L.weightRestriction lam := by
  have h1 := L.sub_mem_positiveRootMonoid_of_inf_ne_bot hρ hne
  have h2 : -(L.weightRestriction lam - ν) ∈ e.toSplitPinning.positiveRootMonoid := by
    rwa [neg_sub]
  have := e.toSplitPinning.eq_zero_of_mem_positiveRootMonoid_of_neg_mem h1 h2
  rw [sub_eq_zero] at this
  exact this.symm

/-- The isotypic subspaces of a representation of `G_K` are stable under `D_K`. -/
theorem isStableSubspace_isotypicSubspace (L : d.LeviComparison s ι e) (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n) (μ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)) :
    (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι)).IsStableSubspace
      (s.isotypicSubspace ρ μ) := by
  have : IsAffineHom ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj
      s.splitTorus).toGrp.X.hom := s.isAffineHom_baseChange
  exact isStableSubspace_characterSpace_of_centralizes
    (T := (CommGroupScheme.baseChange (algebraBaseMap F K)).obj s.splitTorus) _ _
    (L.centralizes_baseChange K) ρ (s.splitCharacter μ)

/-- Split coordinates of an isotypic subspace are stable coordinates for `D_K`. -/
theorem exists_isotypicCoordinates (L : d.LeviComparison s ι e) (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n) (μ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)) :
    ∃ (m : ℕ) (B : Matrix n (Fin m) K) (C : Matrix (Fin m) n K),
      C * B = 1 ∧ (∀ j, (fun r => B r j) ∈ s.isotypicSubspace ρ μ) ∧
      (∀ v, v ∈ s.isotypicSubspace ρ μ → (B * C) *ᵥ v = v) ∧
      (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι)).IsStableCoordinates
        B C := by
  obtain ⟨m, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates (s.isotypicSubspace ρ μ)
  exact ⟨m, B, C, hCB, hcols, hproj,
    (L.isStableSubspace_isotypicSubspace ρ μ).isStableCoordinates B C hcols hproj⟩

section Coordinates

variable (L : d.LeviComparison s ι e) {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n} {lam : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)}
  (hρ : d.toSplitPinning.IsHighestWeight ρ lam)
  {m : ℕ} (B : Matrix n (Fin m) K) (C : Matrix (Fin m) n K)
  (hCB : C * B = 1) (hcols : ∀ j, (fun r => B r j) ∈ s.isotypicSubspace ρ lam)
  (hproj : ∀ v, v ∈ s.isotypicSubspace ρ lam → (B * C) *ᵥ v = v)
  (hst : (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι)).IsStableCoordinates
    B C)

include hρ hcols hproj in
/-- On split coordinates of the isotypic subspace of a representation of highest weight `λ`,
the coordinate representation of `D_K` has the weight `λ|T_D` with multiplicity one. -/
theorem finrank_representationWeightSpace_isotypicCoordinates :
    Module.finrank K
      (e.toSplitPinning.representationWeightSpace
        (restrictCoordinates (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι))
          B C hCB hst)
        (L.weightRestriction lam)) = 1 := by
  rw [e.toSplitPinning.finrank_representationWeightSpace_restrictCoordinates _ _ B C
    hCB hcols hproj hst]
  exact L.finrank_representationWeightSpace_inf_isotypicSubspace hρ

include hρ hcols hproj in
/-- On split coordinates of the isotypic subspace of a representation of highest weight `λ`,
every weight `ν` of the coordinate representation of `D_K` satisfies `λ|T_D - ν ∈ Q⁺`. -/
theorem sub_mem_positiveRootMonoid_isotypicCoordinates {ν : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj e.torus)}
    (hν : e.toSplitPinning.representationWeightSpace
        (restrictCoordinates (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι))
          B C hCB hst) ν ≠ ⊥) :
    L.weightRestriction lam - ν ∈ e.toSplitPinning.positiveRootMonoid :=
  L.sub_mem_positiveRootMonoid_of_inf_ne_bot hρ
    (e.toSplitPinning.inf_ne_bot_of_representationWeightSpace_restrictCoordinates_ne_bot
      _ _ B C hCB hcols hproj hst hν)

include hρ hcols hproj in
/-- On split coordinates of the isotypic subspace of a representation of highest weight `λ`,
the weight `λ|T_D` of the coordinate representation of `D_K` is maximal. -/
theorem eq_of_representationWeightSpace_isotypicCoordinates_ne_bot {ν : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj e.torus)}
    (hν : e.toSplitPinning.representationWeightSpace
        (restrictCoordinates (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι))
          B C hCB hst) ν ≠ ⊥)
    (hle : ν - L.weightRestriction lam ∈ e.toSplitPinning.positiveRootMonoid) :
    ν = L.weightRestriction lam :=
  L.eq_of_inf_ne_bot_of_sub_mem hρ
    (e.toSplitPinning.inf_ne_bot_of_representationWeightSpace_restrictCoordinates_ne_bot
      _ _ B C hCB hcols hproj hst hν) hle

end Coordinates

end LeviComparison

end GaloisPinningData

namespace TitsIndexData.AnisotropicKernelIndex

open MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData G} {n : Type} [Fintype n] [DecidableEq n]

/-- For the actual anisotropic kernel and a representation of `G_K` of highest weight `λ`,
there are split coordinates of the `S`-isotypic subspace of `λ` on which the actual kernel
acts by an actual representation in which `λ|T_H` has multiplicity one and dominates every
weight. -/
theorem exists_isotypicCoordinates_highestWeight (p : d.AnisotropicKernelIndex)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).obj G) n}
    {lam : characterLattice ((CommGroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).obj d.pinning.torus)}
    (hρ : d.pinning.toSplitPinning.IsHighestWeight ρ lam) :
    ∃ (m : ℕ) (B : Matrix n (Fin m) (SeparableClosure k))
      (C : Matrix (Fin m) n (SeparableClosure k)) (hCB : C * B = 1)
      (hst : (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map
        (p.derived ≫ p.inclusion))).IsStableCoordinates B C),
      (∀ j, (fun r => B r j) ∈ d.splitTorusDatum.isotypicSubspace ρ lam) ∧
      (∀ v, v ∈ d.splitTorusDatum.isotypicSubspace ρ lam → (B * C) *ᵥ v = v) ∧
      Module.finrank (SeparableClosure k)
        (p.index.pinning.toSplitPinning.representationWeightSpace
          (restrictCoordinates (ρ.restrict ((GroupScheme.baseChange
            (algebraBaseMap k (SeparableClosure k))).map (p.derived ≫ p.inclusion))) B C hCB hst)
          (p.comparison.weightRestriction lam)) = 1 ∧
      ∀ ν : characterLattice ((CommGroupScheme.baseChange
          (algebraBaseMap k (SeparableClosure k))).obj p.index.pinning.torus),
        p.index.pinning.toSplitPinning.representationWeightSpace
          (restrictCoordinates (ρ.restrict ((GroupScheme.baseChange
            (algebraBaseMap k (SeparableClosure k))).map (p.derived ≫ p.inclusion))) B C hCB hst)
          ν ≠ ⊥ →
        p.comparison.weightRestriction lam - ν ∈
          p.index.pinning.toSplitPinning.positiveRootMonoid := by
  obtain ⟨m, B, C, hCB, hcols, hproj, hst⟩ :=
    p.leviComparison.exists_isotypicCoordinates ρ lam
  exact ⟨m, B, C, hCB, hst, hcols, hproj,
    p.leviComparison.finrank_representationWeightSpace_isotypicCoordinates hρ B C hCB hcols
      hproj hst,
    fun ν hν => p.leviComparison.sub_mem_positiveRootMonoid_isotypicCoordinates hρ B C hCB
      hcols hproj hst hν⟩

end TitsIndexData.AnisotropicKernelIndex

end Langlands.GroupScheme
