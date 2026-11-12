import Langlands.GroupScheme.Rational.ParabolicCorootLiftUniqueness
import Langlands.GroupScheme.Rational.TitsStandardParabolic
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws
import Langlands.Representation.Plancherel.RationalTwistStabilizer

/-! # The actual full torus parameter of a Levi character -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace ParabolicRootPresentation

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

/-- The supplied Levi map represents its actual standard Levi. -/
theorem standardLeviRepresentative :
    (standardLevi r.data.i r.data.ν r.data.J).IsRepresentedBy (l ≫ p) := by
  have hjc := r.isCompatible.levi.isClosedSubgroup.comp
    r.isCompatible.parabolic.isClosedSubgroup
  let := hjc.mono
  exact ⟨Over.mono_of_mono_left _, r.isCompatible.levi_eq⟩

/-- The ambient maximal split torus, factored through the specified Levi. -/
def leviTorusHom : r.data.T.toGrp ⟶ M :=
  standardLeviTorusFactor r.data.i r.data.ν r.data.J r.standardLeviRepresentative

theorem leviTorusHom_comp : r.leviTorusHom ≫ (l ≫ p) = r.data.i :=
  standardLeviTorusFactor_comp r.data.i r.data.ν r.data.J r.standardLeviRepresentative

/-- The original split-component inclusion factors through the same torus map. -/
theorem factor_comp_leviTorusHom :
    CommGroupScheme.groupHom r.data.f ≫ r.leviTorusHom = a := by
  have := r.standardLeviRepresentative.1
  apply Grp.hom_ext
  apply (cancel_mono (l ≫ p).hom.hom).mp
  change (CommGroupScheme.groupHom r.data.f ≫ r.leviTorusHom ≫ (l ≫ p)).hom.hom =
    (a ≫ l ≫ p).hom.hom
  rw [r.leviTorusHom_comp]
  exact congrArg (fun g => g.hom.hom) r.isCompatible.factor_comp

end ParabolicRootPresentation

end Langlands.GroupScheme

namespace Langlands.Plancherel.SplitTorus

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine T.X.left]

local instance fullParameterTorusTopology : TopologicalSpace (rationalPoints T.toGrp) :=
  rationalPointTopology k T.X

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [IsAffine T.X.left] in
/-- A character restricted from a group is invariant under the inverse of
every torus automorphism realized by conjugation in that group. -/
theorem character_comp_inv_of_isNormalizingPoint (t : T.toGrp ⟶ H)
    (χ : rationalPoints H →* ℂˣ) {n : rationalPoints H} {σ : T ≅ T}
    (hn : IsNormalizingPoint t n σ) :
    (χ.comp (rationalPoints.map t)).comp
        (rationalPoints.map (CommGroupScheme.groupHom σ.inv)) =
      χ.comp (rationalPoints.map t) := by
  apply MonoidHom.ext
  intro x
  have he := congrArg χ (hn.inv.conj_comp (Over.mk (𝟙 _)) x)
  change χ ((x ≫ (CommGroupScheme.groupHom σ.inv).hom.hom) ≫
    t.hom.hom) = χ (x ≫ t.hom.hom)
  simpa only [constantPoint_self, map_mul, map_inv, mul_inv_cancel_comm,
    Iso.symm_hom] using he.symm

/-- A torus automorphism realized by group conjugation fixes the normalized
parameter of every smooth restricted character. -/
theorem characterRealAut_normalizedRealPart_comp (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ H) (χ : rationalPoints H →* ℂˣ)
    (hχ : IsOpen ((χ.comp (rationalPoints.map t)).ker : Set (rationalPoints T.toGrp)))
    {n : rationalPoints H} {σ : T ≅ T} (hn : IsNormalizingPoint t n σ) :
    RealTorusSpace.characterRealAut σ
        (normalizedRealPart hT (χ.comp (rationalPoints.map t))) =
      normalizedRealPart hT (χ.comp (rationalPoints.map t)) := by
  have h := normalizedRealPart_comp_points hT hT σ.inv
    (χ.comp (rationalPoints.map t)) hχ
  rw [character_comp_inv_of_isNormalizingPoint t χ hn] at h
  exact h.symm

/-- The full normalized parameter of a character restricted to a split torus
is fixed by the actual normalizer action. -/
theorem fullRealAction_normalizedRealPart_comp (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ H) [Mono t.hom.hom.left]
    (χ : rationalPoints H →* ℂˣ)
    (hχ : IsOpen ((χ.comp (rationalPoints.map t)).ker : Set (rationalPoints T.toGrp)))
    (n : normalizerPoints t) :
    relativeWeylFullRealAction t (QuotientGroup.mk n)
        (normalizedRealPart hT (χ.comp (rationalPoints.map t))) =
      normalizedRealPart hT (χ.comp (rationalPoints.map t)) := by
  exact characterRealAut_normalizedRealPart_comp hT t χ hχ
    (isNormalizingPoint_normalizingAut t n)

end Langlands.Plancherel.SplitTorus

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance : Mono r.data.i.hom.hom.left :=
  r.isCompatible.maximalSplit.isSplitSubtorus.mono

local instance : IsAffineHom r.data.T.X.hom :=
  r.isCompatible.maximalSplit.isSplitSubtorus.1.isAffineHom

local instance : IsAffine r.data.T.X.left :=
  isAffine_of_isAffineHom r.data.T.X.hom

local instance : TopologicalSpace (rationalPoints r.data.T.toGrp) :=
  rationalPointTopology k r.data.T.X

/-- The normalized real part of the original unramified character on the
ambient maximal split torus, using its actual factor into the supplied Levi. -/
def leviUnramifiedFullRealPart
    (ψ : leviUnramifiedCharacters l r.isCompatible.levi) :
    RealTorusSpace.Vstar r.data.T :=
  letI := leviPointTopology l r.isCompatible.levi
  Plancherel.SplitTorus.normalizedRealPart r.isCompatible.maximalSplit.isSplitSubtorus.1
    (ψ.val.toMonoidHom.comp (rationalPoints.map r.leviTorusHom))

/-- Restricting the full parameter recovers the published Levi split-component
parameter. -/
theorem restrict_leviUnramifiedFullRealPart
    (ψ : leviUnramifiedCharacters l r.isCompatible.levi) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
        (leviUnramifiedFullRealPart r ψ) =
      leviUnramifiedRealPart l r.isCompatible.levi a r.isCompatible.splitComponent ψ := by
  have := r.isCompatible.levi.isConnectedReductive.isAffineHom
  have hT := r.isCompatible.maximalSplit.isSplitSubtorus.1
  let := hT.isAffineHom
  let : IsAffine r.data.T.X.left := isAffine_of_isAffineHom r.data.T.X.hom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := r.isCompatible.levi.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l r.isCompatible.levi
  let : NonarchimedeanGroup (rationalPoints M) :=
    Plancherel.rationalPoints_nonarchimedeanGroup M
  let : TopologicalSpace (rationalPoints r.data.T.toGrp) :=
    rationalPointTopology k r.data.T.X
  have hψ : IsOpen ((ψ.val.toMonoidHom.comp (rationalPoints.map r.leviTorusHom)).ker :
      Set (rationalPoints r.data.T.toGrp)) :=
    (Plancherel.unramifiedCharacter_isOpen_ker _ ψ).preimage
      (continuous_rationalPointMap k r.leviTorusHom.hom.hom)
  rw [leviUnramifiedFullRealPart, ← Plancherel.SplitTorus.normalizedRealPart_comp_points
    r.isCompatible.splitComponent.isCentralSplitTorus.1.1 hT r.data.f _ hψ]
  congr 1
  apply MonoidHom.ext
  intro x
  change ψ.val (x ≫ (CommGroupScheme.groupHom r.data.f).hom.hom ≫
      r.leviTorusHom.hom.hom) = ψ.val (x ≫ a.hom.hom)
  rw [← Grp.comp_hom_hom, r.factor_comp_leviTorusHom]

/-- The actual torus restriction of an unramified Levi character is smooth. -/
theorem isOpen_ker_leviUnramifiedTorusCharacter
    (ψ : leviUnramifiedCharacters l r.isCompatible.levi) :
    letI := leviPointTopology l r.isCompatible.levi
    IsOpen ((ψ.val.toMonoidHom.comp (rationalPoints.map r.leviTorusHom)).ker :
      Set (rationalPoints r.data.T.toGrp)) := by
  have := r.isCompatible.levi.isConnectedReductive.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := r.isCompatible.levi.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l r.isCompatible.levi
  let : NonarchimedeanGroup (rationalPoints M) :=
    Plancherel.rationalPoints_nonarchimedeanGroup M
  exact (Plancherel.unramifiedCharacter_isOpen_ker _ ψ).preimage
    (continuous_rationalPointMap k r.leviTorusHom.hom.hom)

/-- The full parameter of the original character is fixed by the actual
standard Levi Weyl subgroup. -/
theorem relativeWeylFullRealAction_leviUnramifiedFullRealPart
    (ψ : leviUnramifiedCharacters l r.isCompatible.levi)
    (w : relativeWeylGroup r.data.i)
    (hw : w ∈ standardRelativeWeylGroup r.data.i r.data.ν r.data.J) :
    relativeWeylFullRealAction r.data.i w (leviUnramifiedFullRealPart r ψ) =
      leviUnramifiedFullRealPart r ψ := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  have hn := coe_mem_standardLeviPoints_of_mk_mem r.data.i r.data.ν r.data.J hw
  have hm : n.val ∈ (SubgroupFunctor.range (l ≫ p)).carrier (Over.mk (𝟙 _)) := by
    rw [r.isCompatible.levi_eq]
    exact hn
  obtain ⟨m, hm⟩ := hm
  change m ≫ (l ≫ p).hom.hom = n.val at hm
  have := r.standardLeviRepresentative.1
  have hnorm : IsNormalizingPoint r.leviTorusHom m (normalizingAut r.data.i n) := by
    apply IsNormalizingPoint.of_comp (l ≫ p)
    rw [r.leviTorusHom_comp, hm]
    exact isNormalizingPoint_normalizingAut r.data.i n
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l r.isCompatible.levi
  exact Plancherel.SplitTorus.characterRealAut_normalizedRealPart_comp
    r.isCompatible.maximalSplit.isSplitSubtorus.1 r.leviTorusHom ψ.val.toMonoidHom
    (isOpen_ker_leviUnramifiedTorusCharacter r ψ) hnorm

section Coroots

variable [LocallyOfFiniteType G.X.hom]

open RealTorusSpace
open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

/-- The original unramified character's full parameter annihilates every
selected coroot of the supplied actual reflection data. -/
theorem pair_leviUnramifiedFullRealPart_selectedCoroot
    (hG : IsConnectedReductive G) (D : RelativeRootReflectionData r.data.i)
    (ψ : leviUnramifiedCharacters l r.isCompatible.levi)
    (α : relativeRoots r.data.i) (hα : α.val ∈ r.data.J) :
    pair r.data.T (leviUnramifiedFullRealPart r ψ)
      ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0 := by
  classical
  obtain ⟨_, _, C, cs, hcs⟩ := relativeWeylCoxeter k G hG r.data.T r.data.i
    r.isCompatible.maximalSplit r.data.ν r.isCompatible.generic
  let αs : SimpleRoot r.data.i r.data.ν :=
    ⟨α.val, r.isCompatible.subset_simpleRoots hα⟩
  have hT := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hs : (QuotientGroup.mk (D.representative α) : relativeWeylGroup r.data.i) =
      cs.simple αs :=
    hcs.eq_simple_of_isRelativeReflection hT αs
      (D.isRelativeReflection_representative hT (hT.finite_relativeRoots r.data.i) α)
  have := r.finite_simpleRoots.to_subtype
  let I : Finset (SimpleRoot r.data.i r.data.ν) :=
    (Set.toFinite {β : SimpleRoot r.data.i r.data.ν | β.val ∈ r.data.J}).toFinset
  have hI (β : SimpleRoot r.data.i r.data.ν) : β ∈ I ↔ β.val ∈ r.data.J := by
    simp only [I, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hJ : rootSet r.data.i r.data.ν I = r.data.J := by
    ext β
    constructor
    · rintro ⟨bidx, hbidx, rfl⟩
      exact (hI bidx).mp hbidx
    · intro hβ
      exact ⟨⟨β, r.isCompatible.subset_simpleRoots hβ⟩, (hI _).mpr hβ, rfl⟩
  have hw : (QuotientGroup.mk (D.representative α) : relativeWeylGroup r.data.i) ∈
      standardRelativeWeylGroup r.data.i r.data.ν r.data.J := by
    rw [hs, ← hJ, ← hcs.2.2.2.2 I]
    exact simple_mem_standardSubgroup cs ((hI αs).mpr hα)
  have hfix := relativeWeylFullRealAction_leviUnramifiedFullRealPart r ψ _ hw
  rw [D.fullRealAction_representative] at hfix
  have heval := congrArg (fun x => pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) hfix
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    pair_tmul_tmul, D.pair_self] at heval
  norm_num at heval
  linarith

/-- A full lift annihilating the selected coroots and restricting to the
original character parameter is the actual torus parameter. -/
theorem leviUnramifiedFullRealPart_eq_of_restrict_eq
    (hG : IsConnectedReductive G) (D : RelativeRootReflectionData r.data.i)
    (ψ : leviUnramifiedCharacters l r.isCompatible.levi) (x : Vstar r.data.T)
    (hx : ∀ α : relativeRoots r.data.i, α.val ∈ r.data.J →
      pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0)
    (hres : rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f) x =
      leviUnramifiedRealPart l r.isCompatible.levi a r.isCompatible.splitComponent ψ) :
    leviUnramifiedFullRealPart r ψ = x := by
  apply r.eq_of_restrict_eq_of_selectedCoroot_pair_eq_zero hG D
    (leviUnramifiedFullRealPart r ψ) x
    (pair_leviUnramifiedFullRealPart_selectedCoroot r hG D ψ) hx
  rw [restrict_leviUnramifiedFullRealPart, hres]

/-- The chamber condition on the split-component parameter gives strict
positivity of the actual full parameter on every unselected simple coroot. -/
theorem pair_leviUnramifiedFullRealPart_pos_of_mem_restrictedCorootChamber
    (hG : IsConnectedReductive G) (D : RelativeRootReflectionData r.data.i)
    (ψ : leviUnramifiedCharacters l r.isCompatible.levi)
    (hψ : leviUnramifiedRealPart l r.isCompatible.levi a r.isCompatible.splitComponent ψ ∈
      restrictedCorootChamber r.data.i r.data.ν r.data.J r.data.f D)
    (α : relativeRoots r.data.i) (hα : α.val ∈ simpleRelativeRoots r.data.i r.data.ν)
    (hαJ : α.val ∉ r.data.J) :
    0 < pair r.data.T (leviUnramifiedFullRealPart r ψ)
      ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) := by
  obtain ⟨x, hres, hxJ, hxpos⟩ := hψ
  rw [leviUnramifiedFullRealPart_eq_of_restrict_eq r hG D ψ x hxJ hres]
  exact hxpos α hα hαJ

/-- The actual character parameter has a nonzero cone displacement under
every Weyl element outside the actual standard Levi Weyl subgroup. -/
theorem restrict_weyl_leviUnramifiedFullRealPart_eq_sub_nonzeroCone
    (hG : IsConnectedReductive G) (D : RelativeRootReflectionData r.data.i)
    (ψ : leviUnramifiedCharacters l r.isCompatible.levi)
    (hψ : leviUnramifiedRealPart l r.isCompatible.levi a r.isCompatible.splitComponent ψ ∈
      restrictedCorootChamber r.data.i r.data.ν r.data.J r.data.f D)
    (w : relativeWeylGroup r.data.i)
    (hw : w ∉ standardRelativeWeylGroup r.data.i r.data.ν r.data.J) :
    ∃ δ : Vstar A, δ ∈ r.nonnegCone ∧ δ ≠ 0 ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
        (relativeWeylFullRealAction r.data.i w (leviUnramifiedFullRealPart r ψ)) =
          leviUnramifiedRealPart l r.isCompatible.levi a r.isCompatible.splitComponent ψ -
            δ := by
  have hpos (α : SimpleRoot r.data.i r.data.ν) (hαJ : α.val ∉ r.data.J) :
      0 < pair r.data.T (leviUnramifiedFullRealPart r ψ)
        ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩) :=
    pair_leviUnramifiedFullRealPart_pos_of_mem_restrictedCorootChamber r hG D ψ hψ
      ⟨α.val, α.property.1.1⟩ α.property hαJ
  have hnonneg (α : SimpleRoot r.data.i r.data.ν) :
      0 ≤ pair r.data.T (leviUnramifiedFullRealPart r ψ)
        ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩) := by
    by_cases hαJ : α.val ∈ r.data.J
    · rw [pair_leviUnramifiedFullRealPart_selectedCoroot r hG D ψ _ hαJ]
    · exact (hpos α hαJ).le
  refine ⟨rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
    (relativeWeylDisplacement w (leviUnramifiedFullRealPart r ψ)),
    r.restrict_displacement_mem_nonnegCone hG D _ hnonneg w,
    fun hz => hw ((r.restrict_displacement_eq_zero_iff hG D _ hnonneg hpos w).mp hz), ?_⟩
  rw [relativeWeylDisplacement_apply, map_sub, restrict_leviUnramifiedFullRealPart]
  abel

end Coroots

end Langlands.Aubert.General.RepresentedParabolic
