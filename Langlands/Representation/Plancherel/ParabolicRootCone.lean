import Langlands.LinearAlgebra.SubmoduleFinrank
import Langlands.LinearAlgebra.RootFaceReflection
import Langlands.Representation.Plancherel.AmbientCharacterFormNaturality
import Langlands.Representation.Plancherel.ParabolicSquaredModulusReduction
import Langlands.GroupScheme.Rational.RelativeReflectionProperties
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.WeylPositiveCocharacter
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityReduction
import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.GroupScheme.Lie.FiniteDimensional
import Langlands.GroupScheme.Rational.SplitCentralDirectionsConstruction
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.GroupScheme.Lie.Functoriality

/-! # Conic decay bounds from the actual relative roots of a parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LinearAlgebra.RationalSpan Langlands.LinearAlgebra.RootFaceCone

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Plancherel

section Torus

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- Integral characters of a split torus embed into its real character space. -/
theorem one_tmul_character_injective (hT : IsSplitTorus T.toGrp) :
    Function.Injective (fun χ : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] χ) := by
  intro χ ψ h
  apply hT.character_toRat_injective
  apply toReal_injective (characterLattice T)
  simpa only [toReal_toRat] using h

variable {i}

/-- On the full rational character space a relative reflection in `β` moves every vector
along `β`, when the roots and the restricted characters span. -/
theorem IsRelativeReflection.exists_fullRatAction_eq_add {β : characterLattice T}
    {w : relativeWeylGroup i} (h : IsRelativeReflection i β w)
    (hspan : relativeRootSpan i ⊔ (rationalCharacterRestrictRat i).range = ⊤)
    (x : ℚ ⊗[ℤ] characterLattice T) :
    ∃ c : ℚ, relativeWeylFullRatAction i w x = x + c • toRat β := by
  obtain ⟨hβ, f, hf, hw⟩ := h
  have hx : x ∈ relativeRootSpan i ⊔ (rationalCharacterRestrictRat i).range := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, ⟨c, rfl⟩, hsum⟩ := Submodule.mem_sup.mp hx
  have hroot : relativeWeylFullRatAction i w y = y - f ⟨y, hy⟩ • toRat β := by
    have h1 := coe_relativeWeylAction_apply i w ⟨y, hy⟩
    rw [hw, Module.reflection_apply] at h1
    rw [← h1]
    rfl
  refine ⟨-f ⟨y, hy⟩, ?_⟩
  rw [← hsum, map_add, relativeWeylFullRatAction_restrictionRange, hroot, neg_smul]
  abel

/-- The real form of `exists_fullRatAction_eq_add`. -/
theorem IsRelativeReflection.exists_realAction_eq_add {β : characterLattice T}
    {w : relativeWeylGroup i} (h : IsRelativeReflection i β w)
    (hspan : relativeRootSpan i ⊔ (rationalCharacterRestrictRat i).range = ⊤)
    (x : Vstar T) :
    ∃ t : ℝ, relativeWeylRealCharacterAction i w x = x + t • ((1 : ℝ) ⊗ₜ[ℤ] β) := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    obtain ⟨c, hc⟩ := IsRelativeReflection.exists_fullRatAction_eq_add h hspan (toRat χ)
    have h1 := congrArg (toReal (characterLattice T)) hc
    rw [map_add, map_smul, toReal_toRat, toReal_toRat, toRat_apply,
      relativeWeylFullRatAction_tmul, toReal_tmul, Rat.cast_one] at h1
    have hq : c • ((1 : ℝ) ⊗ₜ[ℤ] β) = (c : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] β) := by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Rat.smul_one_eq_cast,
        smul_eq_mul, mul_one]
    rw [hq] at h1
    refine ⟨r * c, ?_⟩
    have hr : ∀ ξ : characterLattice T, r ⊗ₜ[ℤ] ξ = r • ((1 : ℝ) ⊗ₜ[ℤ] ξ) := fun ξ => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [relativeWeylRealCharacterAction_tmul, hr, hr χ]
    change r • ((1 : ℝ) ⊗ₜ[ℤ] relativeWeylLatticeAction i w χ) = _
    rw [h1, smul_add, smul_smul]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s + t, ?_⟩
    rw [map_add, hs, ht, add_smul]
    abel

variable [Fintype (relativeWeylGroup i)] (hT : IsSplitTorus T.toGrp)

include hT in
/-- The real reflection package of an actual relative reflection: an isometry of the
invariant form negating `β`, moving every vector along `β`, preserving the relative roots
with their multiplicities and fixing the restricted rational characters of `G`. -/
theorem IsRelativeReflection.realReflectionData {β : characterLattice T}
    {w : relativeWeylGroup i} (h : IsRelativeReflection i β w)
    (hspan : relativeRootSpan i ⊔ (rationalCharacterRestrictRat i).range = ⊤) :
    (∀ x y, relativeWeylInvariantForm i hT (relativeWeylRealCharacterAction i w x)
        (relativeWeylRealCharacterAction i w y) = relativeWeylInvariantForm i hT x y) ∧
      relativeWeylRealCharacterAction i w ((1 : ℝ) ⊗ₜ[ℤ] β) = -((1 : ℝ) ⊗ₜ[ℤ] β) ∧
      (∀ x, ∃ t : ℝ, relativeWeylRealCharacterAction i w x = x + t • ((1 : ℝ) ⊗ₜ[ℤ] β)) ∧
      (∀ χ, relativeWeylRealCharacterAction i w ((1 : ℝ) ⊗ₜ[ℤ] χ) =
        (1 : ℝ) ⊗ₜ[ℤ] relativeWeylLatticeAction i w χ) ∧
      (∀ χ ∈ relativeRoots i, relativeWeylLatticeAction i w χ ∈ relativeRoots i) ∧
      (∀ χ, Module.finrank k (weightSpace i (relativeWeylLatticeAction i w χ)) =
        Module.finrank k (weightSpace i χ)) ∧
      ∀ ξ : rationalCharacters G,
        relativeWeylRealCharacterAction i w ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict i ξ) =
          (1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict i ξ := by
  refine ⟨relativeWeylInvariantForm_invariant i hT w, ?_,
    IsRelativeReflection.exists_realAction_eq_add h hspan,
    fun χ => rfl, fun χ hχ => relativeWeylLatticeAction_mapsTo_relativeRoots i w hχ, ?_, ?_⟩
  · rw [relativeWeylRealCharacterAction_tmul,
      h.relativeWeylCharacterAction_apply_self i hT, TensorProduct.tmul_neg]
  · intro χ
    refine Quotient.inductionOn w ?_
    intro n
    exact finrank_weightSpace_weylAction n χ
  · intro ξ
    change (1 : ℝ) ⊗ₜ[ℤ] relativeWeylLatticeAction i w (torusCharacterRestrict i ξ) = _
    rw [relativeWeylLatticeAction_torusCharacterRestrict]

end Torus

section TorusLevi

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]
  (hT : IsSplitTorus T.toGrp)

include hT in
/-- **Levi orthogonality on the maximal split torus.** For a finite set `RT` of the relative
roots, with multiplicities the weight-space dimensions, the root weight of every `z` is
orthogonal to every root orthogonal to `z`. -/
theorem relativeWeylInvariantForm_rootWeight_levi (hroot : HasRelativeRootSystem i)
    (hspan : relativeRootSpan i ⊔ (rationalCharacterRestrictRat i).range = ⊤)
    (RT : Finset (characterLattice T)) (hRT : ∀ χ, χ ∈ RT ↔ χ ∈ relativeRoots i)
    (z : Vstar T) (χ : characterLattice T) (hχ : χ ∈ RT)
    (hz : relativeWeylInvariantForm i hT ((1 : ℝ) ⊗ₜ[ℤ] χ) z = 0) :
    relativeWeylInvariantForm i hT ((1 : ℝ) ⊗ₜ[ℤ] χ)
      (∑ χ' ∈ RT.filter (fun χ' => 0 < relativeWeylInvariantForm i hT ((1 : ℝ) ⊗ₜ[ℤ] χ') z),
        (Module.finrank k (weightSpace i χ') : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] χ')) = 0 := by
  classical
  have hinj := one_tmul_character_injective hT
  have key := rootWeight_levi_of_reflections (B := relativeWeylInvariantForm i hT)
    (Φ := RT.image (fun χ => (1 : ℝ) ⊗ₜ[ℤ] χ))
    (m := Function.extend (fun χ : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] χ)
      (fun χ => (Module.finrank k (weightSpace i χ) : ℝ)) 0)
    (fun x hx => relativeWeylInvariantForm_pos i hT hx) ?_ z _
    (Finset.mem_image_of_mem _ hχ) hz
  · rwa [rootWeight_image_eq RT hinj] at key
  · intro β hβ
    obtain ⟨χ₀, hχ₀, rfl⟩ := Finset.mem_image.1 hβ
    obtain ⟨w, hw⟩ := hroot.exists_isRelativeReflection ((hRT χ₀).1 hχ₀)
    obtain ⟨hB, hneg, hrank, htmul, hroots, hdim, -⟩ :=
      IsRelativeReflection.realReflectionData hT hw hspan
    refine ⟨relativeWeylRealCharacterAction i w, hB, hneg, hrank, ?_, ?_⟩
    · intro γ hγ
      obtain ⟨χ', hχ', rfl⟩ := Finset.mem_image.1 hγ
      rw [htmul]
      exact Finset.mem_image_of_mem _ ((hRT _).2 (hroots χ' ((hRT χ').1 hχ')))
    · intro γ hγ
      obtain ⟨χ', hχ', rfl⟩ := Finset.mem_image.1 hγ
      rw [htmul, hinj.extend_apply, hinj.extend_apply, hdim]

include hT in
/-- Relative roots are orthogonal to the restricted rational characters of `G`. -/
theorem relativeWeylInvariantForm_root_character (hroot : HasRelativeRootSystem i)
    (hspan : relativeRootSpan i ⊔ (rationalCharacterRestrictRat i).range = ⊤)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i) (ξ : rationalCharacters G) :
    relativeWeylInvariantForm i hT ((1 : ℝ) ⊗ₜ[ℤ] χ)
      ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict i ξ) = 0 := by
  obtain ⟨w, hw⟩ := hroot.exists_isRelativeReflection hχ
  obtain ⟨hB, hneg, -, -, -, -, hfix⟩ := IsRelativeReflection.realReflectionData hT hw hspan
  exact apply_eq_zero_of_isometry_fixed _ hB hneg (hfix ξ)

end TorusLevi

section Spanning

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The real span of the relative roots and the restricted rational characters of `G` is the
whole real character space of a maximal split torus. -/
theorem realSpan_relativeRoots_sup_characters (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    ∀ x : Vstar T, x ∈ Submodule.span ℝ ((fun χ => (1 : ℝ) ⊗ₜ[ℤ] χ) '' relativeRoots i) ⊔
      Submodule.span ℝ (Set.range fun ξ : rationalCharacters G =>
        (1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict i ξ) := by
  let := hG.isAffineHom
  have hrat := relativeRootsRestrictedCharactersSpan k G hG T i hi
  have hgen : ∀ χ : characterLattice T, (1 : ℝ) ⊗ₜ[ℤ] χ ∈
      Submodule.span ℝ ((fun χ => (1 : ℝ) ⊗ₜ[ℤ] χ) '' relativeRoots i) ⊔
        Submodule.span ℝ (Set.range fun ξ : rationalCharacters G =>
          (1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict i ξ) := by
    intro χ
    have h1 : toReal (characterLattice T) (toRat χ) ∈ Submodule.span ℝ
        ((fun χ => (1 : ℝ) ⊗ₜ[ℤ] χ) '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) := by
      rw [toReal_mem_span_iff]
      change toRat χ ∈ Submodule.span ℚ _
      rw [hrat]
      exact Submodule.mem_top
    rw [toReal_toRat, Set.image_union, Submodule.span_union, ← Set.range_comp] at h1
    exact h1
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul t χ =>
    have : t ⊗ₜ[ℤ] χ = t • ((1 : ℝ) ⊗ₜ[ℤ] χ) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ t (hgen χ)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end Spanning

section Multiplicity

variable {k : Type u} [Field k] {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

open Classical in
/-- **Multiplicities add along restriction.** The dimension of a nonzero weight space of a
restricted split torus is the sum of the dimensions of the weight spaces of the roots
restricting to that weight. -/
theorem finrank_weightSpace_comp_eq_sum (hT : IsSplitTorus T.toGrp)
    (hT' : IsSplitTorus T'.toGrp) (f : T' ⟶ T) (i : T.toGrp ⟶ G)
    (RT : Finset (characterLattice T)) (hRT : ∀ χ ∈ roots i, χ ∈ RT)
    {ψ : characterLattice T'} (hψ : ψ ≠ 0) :
    Module.finrank k (weightSpace (CommGroupScheme.groupHom f ≫ i) ψ) =
      ∑ χ ∈ RT.filter (fun χ => f ≫ χ = ψ), Module.finrank k (weightSpace i χ) := by
  classical
  have heq : weightSpace (CommGroupScheme.groupHom f ≫ i) ψ =
      ⨆ χ ∈ RT.filter (fun χ => f ≫ χ = ψ), weightSpace i χ := by
    rw [weightSpace_comp_eq_iSup hT hT' f i ψ]
    apply le_antisymm
    · refine iSup_le fun χ => ?_
      by_cases hbot : weightSpace i χ.val = ⊥
      · rw [hbot]
        exact bot_le
      · have hχ0 : χ.val ≠ 0 := by
          intro h0
          apply hψ
          rw [← χ.property, h0]
          simp
        exact le_biSup (fun χ => weightSpace i χ)
          (Finset.mem_filter.2 ⟨hRT _ ⟨hχ0, hbot⟩, χ.property⟩)
    · refine iSup₂_le fun χ hχ => ?_
      exact le_iSup (fun χ : {χ : characterLattice T // f ≫ χ = ψ} => weightSpace i χ.val)
        ⟨χ, (Finset.mem_filter.1 hχ).2⟩
  rw [heq]
  have := Lie.finiteDimensional_lieKernel G
  exact finrank_biSup_eq_sum
    (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSupIndep _

end Multiplicity

section SplitComponent

variable {k : Type u} [Field k] {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {M P G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)

/-- Restricting a real character along the split component acts on integral characters
by composition. -/
theorem parabolic_restrictReal_tmul (χ : characterLattice r.data.T) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f) ((1 : ℝ) ⊗ₜ[ℤ] χ) =
      (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ χ) :=
  rfl

/-- Restricting a restricted rational character of `G` along the split component gives
its restriction along `a ≫ l ≫ p`. -/
theorem parabolic_restrictReal_character (ξ : rationalCharacters G) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
        ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict r.data.i ξ) =
      (1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice A)
        (characterRestrict (a ≫ l ≫ p) ξ) := by
  rw [← r.isCompatible.factor_comp]
  rfl

variable [LocallyOfFiniteType G.X.hom]

/-- The relative roots of the split component are the nonzero restrictions of the relative
roots of the presentation torus. -/
theorem parabolic_mem_relativeRoots_iff (hA : IsSplitTorus A.toGrp)
    (hT : IsSplitTorus r.data.T.toGrp) (α : characterLattice A) :
    α ∈ relativeRoots (a ≫ l ≫ p) ↔
      α ≠ 0 ∧ ∃ χ ∈ relativeRoots r.data.i, r.data.f ≫ χ = α := by
  rw [← r.isCompatible.factor_comp]
  exact mem_roots_comp_iff hT hA r.data.f r.data.i α

/-- Under a relative root system for the presentation torus, the relative roots of the split
component are closed under negation. -/
theorem parabolic_neg_mem_relativeRoots [Mono r.data.i.hom.hom.left]
    (hroot : HasRelativeRootSystem r.data.i) (hA : IsSplitTorus A.toGrp)
    (hT : IsSplitTorus r.data.T.toGrp) {α : characterLattice A}
    (hα : α ∈ relativeRoots (a ≫ l ≫ p)) : -α ∈ relativeRoots (a ≫ l ≫ p) := by
  obtain ⟨hα0, χ, hχ, rfl⟩ := (parabolic_mem_relativeRoots_iff r hA hT α).1 hα
  refine (parabolic_mem_relativeRoots_iff r hA hT _).2 ⟨neg_ne_zero.2 hα0, -χ,
    HasRelativeRootSystem.neg_mem_relativeRoots r.data.i hroot hT hχ, ?_⟩
  exact Preadditive.comp_neg _ _

open Classical in
/-- The weight-space dimension of a relative root of the split component is the sum of the
weight-space dimensions of the relative roots of the presentation torus restricting to it. -/
theorem parabolic_finrank_weightSpace_eq_sum (hA : IsSplitTorus A.toGrp)
    (hT : IsSplitTorus r.data.T.toGrp) (RT : Finset (characterLattice r.data.T))
    (hRT : ∀ χ ∈ relativeRoots r.data.i, χ ∈ RT) {α : characterLattice A} (hα : α ≠ 0) :
    Module.finrank k (weightSpace (a ≫ l ≫ p) α) =
      ∑ χ ∈ RT.filter (fun χ => r.data.f ≫ χ = α),
        Module.finrank k (weightSpace r.data.i χ) := by
  rw [← r.isCompatible.factor_comp]
  exact finrank_weightSpace_comp_eq_sum hT hA r.data.f r.data.i RT hRT hα

/-- A relative root has a nonzero weight space. -/
theorem finrank_weightSpace_pos {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    0 < Module.finrank k (weightSpace i α) := by
  have := Lie.finiteDimensional_lieKernel G
  exact Submodule.one_le_finrank_iff.2 hα.2

omit [LocallyOfFiniteType G.X.hom] in
/-- **Kernel of restriction to the split component.** A real character of the presentation
torus restricting to zero on the split component is a real combination of relative roots
restricting to zero. -/
theorem parabolic_mem_span_of_restrictReal_eq_zero {x : Vstar r.data.T}
    (hx : rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f) x = 0) :
    x ∈ Submodule.span ℝ ((fun χ => (1 : ℝ) ⊗ₜ[ℤ] χ) ''
      {χ | χ ∈ relativeRoots r.data.i ∧ r.data.f ≫ χ = 0}) := by
  obtain ⟨j, hj⟩ := parabolic_exists_torusLeviFactor r
  have hf := parabolic_groupHom_comp_torusLeviFactor r j hj
  have hM := r.isCompatible.levi.isConnectedReductive
  let := hM.isAffineHom
  let := hM.smooth
  let := hM.connectedSpace
  have hA : IsSplitTorus A.toGrp := r.isCompatible.splitComponent.1.isSplitSubtorus.1
  have hT : IsSplitTorus r.data.T.toGrp := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have := r.isCompatible.levi.isClosedSubgroup.mono
  have := r.isCompatible.parabolic.isClosedSubgroup.mono
  have : Mono (l ≫ p).hom.hom.left := by
    change Mono (l.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  have : Mono (l ≫ p).hom.hom := Over.mono_of_mono_left _
  have : Mono r.data.i.hom.hom.left := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  have : Mono j.hom.hom.left := by
    have hfac : j.hom.hom.left ≫ (l ≫ p).hom.hom.left = r.data.i.hom.hom.left :=
      congrArg (fun z => z.hom.hom.left) hj
    exact mono_of_mono_fac hfac
  have hker := (IsSplitComponent.restriction_kernels_eq_relativeRootSpans
    rootAnnihilatorCentrality r.isCompatible.splitComponent hT r.data.f hf).2
  have hx' : x ∈ relativeRootSpanReal j := by
    rw [← hker]
    exact hx
  refine Submodule.span_mono ?_ hx'
  rintro _ ⟨χ, hχ, rfl⟩
  refine ⟨χ, ⟨?_, ?_⟩, rfl⟩
  · have h := roots_subset_comp (l ≫ p) j hχ
    rwa [hj] at h
  · have h0 : (1 : ℝ) ⊗ₜ[ℤ] χ ∈
        (rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)).ker := by
      rw [hker]
      exact Submodule.subset_span ⟨χ, hχ, rfl⟩
    rw [LinearMap.mem_ker] at h0
    change (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ χ) = 0 at h0
    apply one_tmul_character_injective hA
    exact h0.trans (TensorProduct.tmul_zero _ _).symm

end SplitComponent

section SplitLevi

variable {k : Type u} [Field k] {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {M P G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  [Fintype (relativeWeylGroup r.data.i)]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

include hA hT in
/-- **Levi orthogonality on the split component.** For a finite set `RA` of the relative roots
of the split component, with multiplicities the weight-space dimensions, the root weight of
every `y` for the induced form is orthogonal to every root orthogonal to `y`. -/
theorem parabolic_rootWeight_levi (hroot : HasRelativeRootSystem r.data.i)
    (hspan : relativeRootSpan r.data.i ⊔ (rationalCharacterRestrictRat r.data.i).range = ⊤)
    (RA : Finset (characterLattice A)) (hRA : ∀ α, α ∈ RA ↔ α ∈ relativeRoots (a ≫ l ≫ p))
    (y : Vstar A) {α : characterLattice A} (hα : α ∈ RA)
    (hy : weylInducedCharacterForm hA hT r.data.f r.data.i ((1 : ℝ) ⊗ₜ[ℤ] α) y = 0) :
    weylInducedCharacterForm hA hT r.data.f r.data.i ((1 : ℝ) ⊗ₜ[ℤ] α)
      (∑ α' ∈ RA.filter (fun α' =>
          0 < weylInducedCharacterForm hA hT r.data.f r.data.i ((1 : ℝ) ⊗ₜ[ℤ] α') y),
        (Module.finrank k (weightSpace (a ≫ l ≫ p) α') : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] α')) = 0 := by
  classical
  have hfin := hT.finite_relativeRoots r.data.i
  have hRT : ∀ χ, χ ∈ hfin.toFinset ↔ χ ∈ relativeRoots r.data.i := fun χ => hfin.mem_toFinset
  have hcomp := weylInducedCharacterForm_compatible hA hT r.data.f r.data.i
  refine indexedRootWeight_levi_descent (BT := relativeWeylInvariantForm r.data.i hT)
    (q := rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f))
    (L := weylCharacterRestrictionLift hA hT r.data.f r.data.i)
    (RT := hfin.toFinset) (ιT := fun χ => (1 : ℝ) ⊗ₜ[ℤ] χ)
    (mT := fun χ => (Module.finrank k (weightSpace r.data.i χ) : ℝ))
    (RA := RA) (ιA := fun α => (1 : ℝ) ⊗ₜ[ℤ] α)
    (mA := fun α => (Module.finrank k (weightSpace (a ≫ l ≫ p) α) : ℝ))
    (res := fun χ => r.data.f ≫ χ)
    hcomp.2 (relativeWeylInvariantForm_symm r.data.i hT)
    (LinearMap.BilinForm.isSymm_def.1 (weylInducedCharacterForm_symm hA hT r.data.f r.data.i))
    (fun χ => rfl) hcomp.1 ?_ ?_ ?_ ?_ ?_ y hα hy
  · intro χ hχ h0
    rw [hRA, parabolic_mem_relativeRoots_iff r hA hT]
    refine ⟨fun h => h0 ?_, χ, (hRT χ).1 hχ, rfl⟩
    change (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ χ) = 0
    rw [h, TensorProduct.tmul_zero]
  · intro α hα
    have hα' := (parabolic_mem_relativeRoots_iff r hA hT α).1 ((hRA α).1 hα)
    rw [parabolic_finrank_weightSpace_eq_sum r hA hT hfin.toFinset (fun χ hχ => (hRT χ).2 hχ)
      hα'.1, Nat.cast_sum]
  · intro α hα
    obtain ⟨-, χ, hχ, h⟩ := (parabolic_mem_relativeRoots_iff r hA hT α).1 ((hRA α).1 hα)
    exact ⟨χ, (hRT χ).2 hχ, h⟩
  · intro x hx
    refine Submodule.span_mono ?_ (parabolic_mem_span_of_restrictReal_eq_zero r hx)
    rintro _ ⟨χ, ⟨hχ, h0⟩, rfl⟩
    refine ⟨χ, ⟨(hRT χ).2 hχ, ?_⟩, rfl⟩
    change (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ χ) = 0
    rw [h0, TensorProduct.tmul_zero]
  · intro z χ hχ hz
    exact relativeWeylInvariantForm_rootWeight_levi r.data.i hT hroot hspan hfin.toFinset hRT
      z χ hχ hz

include hA hT in
/-- Relative roots of the split component are orthogonal, for the induced form, to the
restricted rational characters of `G`. -/
theorem parabolic_root_orthogonal_character (hroot : HasRelativeRootSystem r.data.i)
    (hspan : relativeRootSpan r.data.i ⊔ (rationalCharacterRestrictRat r.data.i).range = ⊤)
    {α : characterLattice A} (hα : α ∈ relativeRoots (a ≫ l ≫ p)) (ξ : rationalCharacters G) :
    weylInducedCharacterForm hA hT r.data.f r.data.i ((1 : ℝ) ⊗ₜ[ℤ] α)
      ((1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice A)
        (characterRestrict (a ≫ l ≫ p) ξ)) = 0 := by
  classical
  have hfin := hT.finite_relativeRoots r.data.i
  have hRT : ∀ χ, χ ∈ hfin.toFinset ↔ χ ∈ relativeRoots r.data.i := fun χ => hfin.mem_toFinset
  have hcomp := weylInducedCharacterForm_compatible hA hT r.data.f r.data.i
  rw [← parabolic_restrictReal_character r ξ]
  refine restrict_orthogonal_roots (BT := relativeWeylInvariantForm r.data.i hT)
    (q := rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f))
    (L := weylCharacterRestrictionLift hA hT r.data.f r.data.i)
    (RT := hfin.toFinset) (ιT := fun χ => (1 : ℝ) ⊗ₜ[ℤ] χ)
    (RA := (hA.finite_relativeRoots (a ≫ l ≫ p)).toFinset) (ιA := fun α => (1 : ℝ) ⊗ₜ[ℤ] α)
    (res := fun χ => r.data.f ≫ χ) hcomp.2 (fun χ => rfl) hcomp.1 ?_ ?_ ?_
    ((hA.finite_relativeRoots (a ≫ l ≫ p)).mem_toFinset.2 hα)
  · intro α hα
    obtain ⟨-, χ, hχ, h⟩ := (parabolic_mem_relativeRoots_iff r hA hT α).1
      ((hA.finite_relativeRoots (a ≫ l ≫ p)).mem_toFinset.1 hα)
    exact ⟨χ, (hRT χ).2 hχ, h⟩
  · intro x hx
    refine Submodule.span_mono ?_ (parabolic_mem_span_of_restrictReal_eq_zero r hx)
    rintro _ ⟨χ, ⟨hχ, h0⟩, rfl⟩
    refine ⟨χ, ⟨(hRT χ).2 hχ, ?_⟩, rfl⟩
    change (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ χ) = 0
    rw [h0, TensorProduct.tmul_zero]
  · intro χ hχ
    exact relativeWeylInvariantForm_root_character r.data.i hT hroot hspan ((hRT χ).1 hχ) ξ

include hA hT in
/-- The real span of the relative roots of the split component and the restricted rational
characters of `G` is the whole real character space of the split component. -/
theorem parabolic_realSpan_relativeRoots_sup_characters (hG : IsConnectedReductive G)
    (x : Vstar A) :
    x ∈ Submodule.span ℝ ((fun α => (1 : ℝ) ⊗ₜ[ℤ] α) '' relativeRoots (a ≫ l ≫ p)) ⊔
      Submodule.span ℝ (Set.range fun ξ : rationalCharacters G =>
        (1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice A)
          (characterRestrict (a ≫ l ≫ p) ξ)) := by
  have hcomp := weylInducedCharacterForm_compatible hA hT r.data.f r.data.i
  have hx := realSpan_relativeRoots_sup_characters hG r.data.i r.isCompatible.maximalSplit
    (weylCharacterRestrictionLift hA hT r.data.f r.data.i x)
  have hmem := Submodule.mem_map_of_mem
    (f := rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)) hx
  rw [hcomp.1, Submodule.map_sup, Submodule.map_span, Submodule.map_span] at hmem
  refine (sup_le_sup (α := Submodule ℝ (Vstar A)) ?_ ?_) hmem
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨χ, hχ, rfl⟩, rfl⟩
    change (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ χ) ∈ _
    by_cases h0 : r.data.f ≫ χ = 0
    · rw [h0, TensorProduct.tmul_zero]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span
        ⟨_, (parabolic_mem_relativeRoots_iff r hA hT _).2 ⟨h0, χ, hχ, rfl⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨ξ, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨ξ, (parabolic_restrictReal_character r ξ).symm⟩

end SplitLevi

section Realization

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **Integral sign realization.** For a bilinear form on the real character space of a split
torus, every real character `y` has an integral cocharacter `μ` such that each character of a
finite set is positive on `μ` exactly when it is positive against `y`. -/
theorem exists_cocharacter_sign_realization (hT : IsSplitTorus T.toGrp)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (R : Finset (characterLattice T)) (y : Vstar T) :
    ∃ μ : cocharacterLattice T, ∀ α ∈ R,
      (0 < latticePairing T α μ ↔ 0 < B ((1 : ℝ) ⊗ₜ[ℤ] α) y) := by
  have := isPerfPair_of_isSplitTorus hT
  have hgB : ∀ x, pair T x ((pair T).flip.toPerfPair.symm (B.flip y)) = B x y := fun x => by
    rw [LinearMap.apply_toPerfPair_flip]
    rfl
  obtain ⟨μ, hμ⟩ := exists_int_sign_realization R (fun α => latticePairing T α)
    (fun α => eval T α) (fun α t ν => eval_tmul T α t ν)
    ((pair T).flip.toPerfPair.symm (B.flip y))
  refine ⟨μ, fun α hα => ?_⟩
  rw [← hgB, ← eval_eq_pair]
  exact hμ α hα

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The sum of `|B(ν, α)|` over the relative roots `α` of `i`, for a bilinear form `B` on the
real character space. It is the size term of the conic decay bound. -/
abbrev relativeRootAbsSum (i : T.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (Vstar T))
    (ν : Vstar T) : ℝ :=
  ∑ᶠ α ∈ relativeRoots i, |B ν ((1 : ℝ) ⊗ₜ[ℤ] α)|

/-- Over a finset listing exactly the relative roots, `relativeRootAbsSum` is a finset sum. -/
theorem relativeRootAbsSum_eq_sum (i : T.toGrp ⟶ G) (B : LinearMap.BilinForm ℝ (Vstar T))
    (R : Finset (characterLattice T)) (hR : ∀ α, α ∈ R ↔ α ∈ relativeRoots i) (ν : Vstar T) :
    relativeRootAbsSum i B ν = ∑ α ∈ R, |B ν ((1 : ℝ) ⊗ₜ[ℤ] α)| := by
  have h : relativeRoots i = (R : Set (characterLattice T)) := Set.ext fun α => (hR α).symm
  rw [relativeRootAbsSum, h, finsum_mem_coe_finset]

/-- The real image of the positive-weight character of `μ` is the sum of the relative roots
positive on `μ`, each weighted by the dimension of its weight space. -/
theorem one_tmul_positiveWeightCharacter (i : T.toGrp ⟶ G) (R : Finset (characterLattice T))
    (hR : ∀ α, α ∈ R ↔ α ∈ relativeRoots i) (μ : cocharacterLattice T) :
    (1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice T) (positiveWeightCharacter i μ) =
      ∑ α ∈ R.filter (fun α => 0 < latticePairing T α μ),
        (Module.finrank k (weightSpace i α) : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] α) := by
  classical
  have hsupp : (Function.support fun α : characterLattice T =>
      (if 0 < latticePairing T α μ then Module.finrank k (weightSpace i α) else 0) •
        (rationalCharacters.equivCharacterLattice T).symm α) ⊆ R := by
    intro α hα
    rw [Function.mem_support] at hα
    rw [Finset.mem_coe, hR]
    refine ⟨?_, ?_⟩
    · rintro rfl
      apply hα
      simp
    · intro hbot
      apply hα
      rw [hbot, finrank_bot]
      simp
  unfold positiveWeightCharacter
  rw [finsum_eq_sum_of_support_subset _ hsupp, map_sum, TensorProduct.tmul_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs with h
  · rw [map_nsmul, AddEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
    exact map_nsmul (TensorProduct.mk ℤ ℝ (characterLattice T) 1) _ α
  · rw [zero_smul, map_zero, TensorProduct.tmul_zero]

end Realization

section Host

variable {k : Type u} [Field k] {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {M P G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)

include r in
/-- Under the relative root system statement, the relative roots of the split component of a
parabolic root presentation of a connected reductive group are closed under negation. -/
theorem parabolic_neg_mem_relativeRoots_of_statement (hRS : RelativeRootSystemStatement.{u})
    (hG : IsConnectedReductive G) {α : characterLattice A}
    (hα : α ∈ relativeRoots (a ≫ l ≫ p)) : -α ∈ relativeRoots (a ≫ l ≫ p) :=
  letI : Mono r.data.i.hom.hom.left := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  parabolic_neg_mem_relativeRoots r (hRS k G hG r.data.T r.data.i r.isCompatible.maximalSplit)
    r.isCompatible.splitComponent.1.isSplitSubtorus.1
    r.isCompatible.maximalSplit.isSplitSubtorus.1 hα

variable [Mono r.data.i.hom.hom.left] [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  [Fintype (relativeWeylGroup r.data.i)]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

include hA hT in
/-- **Conic decay on the split component.** Let `λ, λ'` be cocharacters of the split component
and call `μ` admissible when `⟨α, μ⟩ ≥ 0` for every relative root with `⟨α, λ⟩ < 0 < ⟨α, λ'⟩`.
For every `c`, `ψ` and `s` there are `R` and `K` such that every real linear functional `H`
bounded below by `-c μ` at the positive-weight characters of the admissible `μ` and vanishing on
the restricted rational characters of `G` satisfies
`H ν ≤ -s |H ψ| + K (1 + ∑_α |B(ν, α)|)` whenever `B(ν, α) > R` for every relative root with
`⟨α, λ⟩ > 0 > ⟨α, λ'⟩`. Here `B` is the Weyl-induced character form and the sum runs over all
relative roots of `a ≫ l ≫ p`. -/
theorem exists_parabolicRootCone_decay (hRS : RelativeRootSystemStatement.{u})
    (hG : IsConnectedReductive G) (lam lam' : cocharacterLattice A)
    (c : cocharacterLattice A → ℝ) (ψ : Vstar A) (s : ℝ) :
    ∃ R K : ℝ, ∀ H : Vstar A →ₗ[ℝ] ℝ,
      (∀ μ : cocharacterLattice A, (∀ α ∈ relativeRoots (a ≫ l ≫ p),
          latticePairing A α lam < 0 → 0 < latticePairing A α lam' →
            0 ≤ latticePairing A α μ) →
        -c μ ≤ H ((1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice A)
          (positiveWeightCharacter (a ≫ l ≫ p) μ))) →
      (∀ ξ : rationalCharacters G, H ((1 : ℝ) ⊗ₜ[ℤ]
          (rationalCharacters.equivCharacterLattice A) (characterRestrict (a ≫ l ≫ p) ξ)) = 0) →
      ∀ ν : Vstar A, (∀ α ∈ relativeRoots (a ≫ l ≫ p), 0 < latticePairing A α lam →
          latticePairing A α lam' < 0 →
            R < weylInducedCharacterForm hA hT r.data.f r.data.i ν ((1 : ℝ) ⊗ₜ[ℤ] α)) →
      H ν ≤ -s * |H ψ| + K * (1 + relativeRootAbsSum (a ≫ l ≫ p)
        (weylInducedCharacterForm hA hT r.data.f r.data.i) ν) := by
  classical
  unfold relativeRootAbsSum
  have hroot : HasRelativeRootSystem r.data.i :=
    hRS k G hG r.data.T r.data.i r.isCompatible.maximalSplit
  have hspan := hG.relativeRootSpan_sup_restrictionRange_eq_top r.data.i
    r.isCompatible.maximalSplit
  set B := weylInducedCharacterForm hA hT r.data.f r.data.i with hBdef
  have hBsymm : ∀ x y, B x y = B y x :=
    LinearMap.BilinForm.isSymm_def.1 (weylInducedCharacterForm_symm hA hT r.data.f r.data.i)
  have hfin := hA.finite_relativeRoots (a ≫ l ≫ p)
  set RA := hfin.toFinset with hRAdef
  have hRA : ∀ α, α ∈ RA ↔ α ∈ relativeRoots (a ≫ l ≫ p) := fun α => hfin.mem_toFinset
  set ι : characterLattice A → Vstar A := fun α => (1 : ℝ) ⊗ₜ[ℤ] α with hι
  have hinj : Function.Injective ι := one_tmul_character_injective hA
  set mA : characterLattice A → ℝ :=
    fun α => (Module.finrank k (weightSpace (a ≫ l ≫ p) α) : ℝ) with hmA
  set Φ := RA.image ι with hΦ
  set m := Function.extend ι mA 0 with hm
  set SA := RA.filter (fun α => 0 < latticePairing A α lam ∧ latticePairing A α lam' < 0)
    with hSA
  have hS : SA.image ι ⊆ Φ := Finset.image_subset_image (Finset.filter_subset _ _)
  have hpos : ∀ x : Vstar A, x ≠ 0 → 0 < B x x := fun x hx =>
    weylInducedCharacterForm_pos hA hT r.data.f r.data.i hx
  have hnegA : ∀ α ∈ RA, -α ∈ RA := fun α hα =>
    (hRA _).2 (parabolic_neg_mem_relativeRoots r hroot hA hT ((hRA α).1 hα))
  have hneg : ∀ x ∈ Φ, -x ∈ Φ := by
    intro x hx
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hx
    refine Finset.mem_image.2 ⟨-α, hnegA α hα, ?_⟩
    simp only [hι, TensorProduct.tmul_neg]
  have hmpos : ∀ x ∈ Φ, 0 < m x := by
    intro x hx
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hx
    rw [hm, hinj.extend_apply, hmA]
    exact Nat.cast_pos.2 (finrank_weightSpace_pos _ ((hRA α).1 hα))
  have hrw : ∀ y, rootWeight B Φ m y =
      ∑ α ∈ RA.filter (fun α => 0 < B (ι α) y), mA α • ι α :=
    fun y => rootWeight_image_eq RA hinj mA y
  have hlevi : ∀ y : Vstar A, ∀ x ∈ Φ, B x y = 0 → B x (rootWeight B Φ m y) = 0 := by
    intro y x hx hy
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hx
    rw [hrw]
    exact parabolic_rootWeight_levi r hA hT hroot hspan RA hRA y hα hy
  obtain ⟨ε, hε, L, hL, hdecay⟩ := exists_pos_rootCone_decay hpos hneg hmpos hlevi _ hS
  -- a uniform lower bound over the finitely many sign patterns of admissible cocharacters
  let adm : cocharacterLattice A → Prop := fun μ => ∀ α ∈ relativeRoots (a ≫ l ≫ p),
    latticePairing A α lam < 0 → 0 < latticePairing A α lam' → 0 ≤ latticePairing A α μ
  let pos : cocharacterLattice A → Finset (characterLattice A) :=
    fun μ => RA.filter (fun α => 0 < latticePairing A α μ)
  let μU : Finset (characterLattice A) → cocharacterLattice A := fun U =>
    if h : ∃ μ, adm μ ∧ pos μ = U then h.choose else 0
  have hμU : ∀ μ, adm μ → adm (μU (pos μ)) ∧ pos (μU (pos μ)) = pos μ := by
    intro μ hμ
    have h : ∃ μ', adm μ' ∧ pos μ' = pos μ := ⟨μ, hμ, rfl⟩
    simp only [μU]
    rw [dite_eq_left h]
    exact h.choose_spec
  set c₀ := ∑ U ∈ RA.powerset, |c (μU U)| with hc₀def
  have hc₀ : 0 ≤ c₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc₀le : ∀ μ, |c (μU (pos μ))| ≤ c₀ := fun μ =>
    Finset.single_le_sum (f := fun U => |c (μU U)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_powerset.2 (Finset.filter_subset _ _))
  have hposW : ∀ μ, (1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice A)
      (positiveWeightCharacter (a ≫ l ≫ p) μ) = ∑ α ∈ pos μ, mA α • ι α := fun μ =>
    one_tmul_positiveWeightCharacter (a ≫ l ≫ p) RA hRA μ
  -- the decomposition of `ψ` into a root part and a character part
  have hspanΦ : Submodule.span ℝ ((fun α => (1 : ℝ) ⊗ₜ[ℤ] α) '' relativeRoots (a ≫ l ≫ p)) =
      Submodule.span ℝ (Φ : Set (Vstar A)) := by
    rw [hΦ, Finset.coe_image, hRAdef, hfin.coe_toFinset]
  set Ξ := Submodule.span ℝ (Set.range fun ξ : rationalCharacters G =>
    (1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice A)
      (characterRestrict (a ≫ l ≫ p) ξ)) with hΞ
  have hdecomp : ∀ x : Vstar A, ∃ xΦ ∈ Submodule.span ℝ (Φ : Set (Vstar A)), ∃ xG ∈ Ξ,
      xΦ + xG = x := fun x => by
    have hx := parabolic_realSpan_relativeRoots_sup_characters r hA hT hG x
    rw [hspanΦ] at hx
    exact Submodule.mem_sup.1 hx
  have hBΞ : ∀ x ∈ Φ, ∀ z ∈ Ξ, B x z = 0 := by
    intro x hx z hz
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hx
    have hle : Ξ ≤ LinearMap.ker (B (ι α)) := by
      rw [hΞ, Submodule.span_le]
      rintro _ ⟨ξ, rfl⟩
      exact parabolic_root_orthogonal_character r hA hT hroot hspan ((hRA α).1 hα) ξ
    exact hle hz
  obtain ⟨ψΦ, hψΦ, ψG, hψG, hψsum⟩ := hdecomp ψ
  obtain ⟨t, -, ht⟩ := Submodule.mem_span_finset.1 hψΦ
  set T₀ := ∑ x ∈ Φ, |t x| with hT₀
  have hT₀0 : 0 ≤ T₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set s' := max s 0 * T₀ with hs'
  have hs'0 : 0 ≤ s' := mul_nonneg (le_max_right _ _) hT₀0
  set K := c₀ / ε * (1 + s' * L) with hK
  refine ⟨s' * L, K, fun H hH hHG ν hν => ?_⟩
  have hHΞ : ∀ z ∈ Ξ, H z = 0 := by
    intro z hz
    have hle : Ξ ≤ LinearMap.ker H := by
      rw [hΞ, Submodule.span_le]
      rintro _ ⟨ξ, rfl⟩
      exact hHG ξ
    exact hle hz
  have hcε : 0 ≤ c₀ / ε := div_nonneg hc₀ hε.le
  have hK0 : 0 ≤ K := mul_nonneg hcε (by nlinarith)
  -- the fixed-point bound for the cone lemma
  have hfix : ∀ y : Vstar A, (∀ x ∈ SA.image ι, B x y ≤ 0) → rootWeight B Φ m y = y →
      -c₀ ≤ H y := by
    intro y hy hfy
    obtain ⟨μ, hμ⟩ := exists_cocharacter_sign_realization hA B RA y
    have hadm : adm μ := by
      intro α hα h1 h2
      have hnα : -α ∈ SA := by
        refine Finset.mem_filter.2 ⟨hnegA α ((hRA α).2 hα), ?_, ?_⟩
        · rw [map_neg, LinearMap.neg_apply]
          omega
        · rw [map_neg, LinearMap.neg_apply]
          omega
      have hB := hy (ι (-α)) (Finset.mem_image_of_mem _ hnα)
      have hn := (hμ (-α) (hnegA α ((hRA α).2 hα))).not.2 (not_lt.2 hB)
      rw [map_neg, LinearMap.neg_apply] at hn
      omega
    have hpat : pos μ = RA.filter (fun α => 0 < B (ι α) y) :=
      Finset.filter_congr fun α hα => hμ α hα
    obtain ⟨hadm', hpos'⟩ := hμU μ hadm
    have h1 := hH _ hadm'
    have heq : (1 : ℝ) ⊗ₜ[ℤ] (rationalCharacters.equivCharacterLattice A)
        (positiveWeightCharacter (a ≫ l ≫ p) (μU (pos μ))) = y := by
      rw [hposW, hpos', hpat, ← hrw, hfy]
    rw [heq] at h1
    have h2 := hc₀le μ
    have h3 := le_abs_self (c (μU (pos μ)))
    linarith
  -- the decomposition of `ν`
  obtain ⟨νΦ, hνΦ, νG, hνG, hνsum⟩ := hdecomp ν
  have hBν : ∀ x ∈ Φ, B x ν = B x νΦ := fun x hx => by
    rw [← hνsum, map_add, hBΞ x hx νG hνG, add_zero]
  have hHν : H ν = H νΦ := by rw [← hνsum, map_add, hHΞ νG hνG, add_zero]
  have hHψ : H ψ = ∑ x ∈ Φ, t x * H x := by
    rw [← hψsum, map_add, hHΞ ψG hψG, add_zero, ← ht, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hsum : ∑ x ∈ Φ, |B x νΦ| = ∑ᶠ α ∈ relativeRoots (a ≫ l ≫ p), |B ν (ι α)| := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← hRAdef, hΦ,
      Finset.sum_image fun x _ y _ h => hinj h]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [← hBν _ (Finset.mem_image_of_mem _ hα), hBsymm]
  have hsum0 : 0 ≤ ∑ᶠ α ∈ relativeRoots (a ≫ l ≫ p), |B ν (ι α)| := by
    rw [← hsum]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  rcases Φ.eq_empty_or_nonempty with hΦe | hΦne
  · have hνΦ0 : νΦ = 0 := by
      rw [hΦe, Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hνΦ
      exact hνΦ
    rw [hHν, hνΦ0, map_zero, hHψ, hΦe, Finset.sum_empty, abs_zero, mul_zero,
      zero_add]
    exact mul_nonneg hK0 (by linarith)
  obtain ⟨β, hβ, hβmax⟩ := Φ.exists_max_image (fun x => |H x|) hΦne
  have hνS : ∀ x ∈ SA.image ι, s' * L ≤ B x νΦ := by
    intro x hx
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hαR, h1, h2⟩ := Finset.mem_filter.1 hα
    rw [← hBν _ (hS hx), hBsymm]
    exact (hν α ((hRA α).1 hαR) h1 h2).le
  have hmain := hdecay s' hs'0 c₀ hc₀ H hfix νΦ hνΦ hνS β hβ
  have hψβ : |H ψ| ≤ T₀ * |H β| := by
    rw [hHψ, hT₀, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hβmax x hx) (abs_nonneg _)
  have hsψ : s * |H ψ| ≤ s' * |H β| := by
    calc s * |H ψ| ≤ max s 0 * |H ψ| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
      _ ≤ max s 0 * (T₀ * |H β|) := mul_le_mul_of_nonneg_left hψβ (le_max_right _ _)
      _ = s' * |H β| := by rw [hs', mul_assoc]
  rw [hsum] at hmain
  rw [hHν]
  have hfinal : c₀ / ε * (∑ᶠ α ∈ relativeRoots (a ≫ l ≫ p), |B ν (ι α)| + s' * L) ≤
      K * (1 + ∑ᶠ α ∈ relativeRoots (a ≫ l ≫ p), |B ν (ι α)|) := by
    rw [hK]
    have hsL : 0 ≤ s' * L := mul_nonneg hs'0 hL
    nlinarith [mul_nonneg hcε (mul_nonneg hsL hsum0), mul_nonneg hcε hsL, mul_nonneg hcε hsum0]
  linarith

end Host

end Langlands.Plancherel
