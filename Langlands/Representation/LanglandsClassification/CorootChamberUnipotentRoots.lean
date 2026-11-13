import Langlands.Representation.LanglandsClassification.CorootChamberUnipotentRootsStatement
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Rational.ReflectionStandardCocharacter
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.DynamicPositiveSemigroup
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Roots positive on a coroot chamber are the roots in the unipotent radical (Renard V.3.17)

Proof of `CorootChamberUnipotentRootsStatement`. The roots of `T` in the standard unipotent
subgroup `N` of `J` are the relative roots positive on one standard cocharacter `ζ` of `J`.
On the coroot side, the relative Weyl group is finite, so the form
`B(x, y) = Σ_w ⟨w x, ν⟩ ⟨w y, ν⟩` on the real character space is invariant; the reflection of
`D` for a root `r` then gives `⟨x, ř⟩ B(r, r) = 2 B(x, r)` with `B(r, r) > 0`. Induction over
positive roots compares the signs of `B(x, ·)` and `⟨·, ζ⟩`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

namespace CorootChamberUnipotentRoots

section Unipotent

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The roots of `T` in the standard unipotent subgroup `N` of `J` are the relative roots on which
one (equivalently every) standard cocharacter `ζ` of `J` is positive. -/
theorem mem_subgroupRelativeRoots_standardUnipotent_iff
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {J : Set (characterLattice T)} {zeta : cocharacterLattice T}
    (hzeta : IsStandardCocharacter i ν J zeta) (r : characterLattice T) :
    r ∈ RelativeRoot.subgroupRelativeRoots i (standardUnipotent i ν J) ↔
      r ∈ relativeRoots i ∧ 0 < latticePairing T r zeta := by
  constructor
  · intro h
    have h' := RelativeRoot.subgroupRelativeRoots_mono i
      (standardUnipotent_le_dynamicUnipotent i ν hzeta) h
    rw [RelativeRoot.subgroupRelativeRoots_dynamicUnipotent i hT] at h'
    exact h'
  · rintro ⟨hr, hpos⟩
    obtain ⟨hr0, X, hX0, hXr, -⟩ :=
      (RelativeRoot.mem_relativeRoots_iff_actionWeightSupport_conjugation_top i r).mp hr
    refine ⟨⟨X, hX0, hXr, ?_⟩, hr0⟩
    rw [mem_standardUnipotent]
    intro eta heta
    have hposeta : 0 < latticePairing T r eta :=
      ((hzeta.haveSameRelativeRootSigns i ν hν hneg heta) r hr).2.2.mp hpos
    have hLie := (RelativeRoot.dynamicUnipotent_semigroupData G T hT i eta).2.2
    exact (hLie X).mpr ((le_iSup_of_le (⟨r, hposeta⟩ : RelativeRoot.positiveSemigroup eta)
      le_rfl : RelativeRoot.actionWeightSpace (AutomorphicAction.conjugation i) r ≤
        RelativeRoot.semigroupWeightSpan (AutomorphicAction.conjugation i)
          (RelativeRoot.positiveSemigroup eta)) hXr)

end Unipotent

section Form

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The linear functional `x ↦ ⟨w x, ν⟩` on the real character space. -/
def weylNuFunctional (ν : cocharacterLattice T) (w : relativeWeylGroup i) : Vstar T →ₗ[ℝ] ℝ :=
  (pair T).flip ((1 : ℝ) ⊗ₜ[ℤ] ν) ∘ₗ (relativeWeylFullRealAction i w).toLinearMap

theorem weylNuFunctional_apply (ν : cocharacterLattice T) (w : relativeWeylGroup i)
    (x : Vstar T) :
    weylNuFunctional i ν w x =
      pair T (relativeWeylFullRealAction i w x) ((1 : ℝ) ⊗ₜ[ℤ] ν) := rfl

variable [Fintype (relativeWeylGroup i)]

/-- The Weyl-averaged form `B(x,y) = Σ_w ⟨w x, ν⟩ ⟨w y, ν⟩`. -/
def averagedForm (ν : cocharacterLattice T) : LinearMap.BilinForm ℝ (Vstar T) :=
  ∑ w : relativeWeylGroup i,
    (LinearMap.mul ℝ ℝ).compl₁₂ (weylNuFunctional i ν w) (weylNuFunctional i ν w)

theorem averagedForm_apply (ν : cocharacterLattice T) (x y : Vstar T) :
    averagedForm i ν x y =
      ∑ w : relativeWeylGroup i, weylNuFunctional i ν w x * weylNuFunctional i ν w y := by
  simp only [averagedForm, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply']

/-- The averaged form is invariant under the full real relative Weyl action. -/
theorem averagedForm_invariant (ν : cocharacterLattice T) (u : relativeWeylGroup i)
    (x y : Vstar T) :
    averagedForm i ν (relativeWeylFullRealAction i u x) (relativeWeylFullRealAction i u y) =
      averagedForm i ν x y := by
  rw [averagedForm_apply, averagedForm_apply]
  refine Fintype.sum_equiv (Equiv.mulRight u) _ _ ?_
  intro w
  simp only [weylNuFunctional_apply, Equiv.coe_mulRight, map_mul, LinearEquiv.mul_apply]

end Form

section Reflection

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The reflection representative of `D` acts on the real character space by
`x ↦ x - ⟨x, ř⟩ r`. -/
theorem reflection_apply (D : RelativeRootReflectionData i) (r : relativeRoots i)
    (x : Vstar T) :
    relativeWeylFullRealAction i (QuotientGroup.mk (D.representative r)) x =
      x - pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot r) • ((1 : ℝ) ⊗ₜ[ℤ] r.val) := by
  induction x using TensorProduct.inductionOn with
  | tmul c χ =>
    rw [relativeWeylFullRealAction_tmul, relativeWeylLatticeAction_mk, D.action, pair_tmul_tmul,
      TensorProduct.tmul_sub, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 2
    simp [zsmul_eq_mul, mul_comm]
  | add x y hx hy =>
    rw [map_add, hx, hy, map_add, LinearMap.add_apply, add_smul]
    abel

variable [Fintype (relativeWeylGroup i)]

/-- The coroot pairing through the averaged form: `⟨x, ř⟩ B(r, r) = 2 B(x, r)`. -/
theorem coroot_pair_mul_form (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
    (r : relativeRoots i) (x : Vstar T) :
    pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot r) *
        averagedForm i ν ((1 : ℝ) ⊗ₜ[ℤ] r.val) ((1 : ℝ) ⊗ₜ[ℤ] r.val) =
      2 * averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] r.val) := by
  have hinv := averagedForm_invariant i ν (QuotientGroup.mk (D.representative r)) x
    ((1 : ℝ) ⊗ₜ[ℤ] r.val)
  rw [reflection_apply, reflection_apply] at hinv
  have h2 : pair T ((1 : ℝ) ⊗ₜ[ℤ] r.val) ((1 : ℝ) ⊗ₜ[ℤ] D.coroot r) = 2 := by
    rw [pair_tmul_tmul, D.pair_self]
    norm_num
  rw [h2] at hinv
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hinv
  linear_combination hinv

/-- For a generic `ν`, every relative root has positive averaged square length. -/
theorem averagedForm_root_pos (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (r : relativeRoots i) :
    0 < averagedForm i ν ((1 : ℝ) ⊗ₜ[ℤ] r.val) ((1 : ℝ) ⊗ₜ[ℤ] r.val) := by
  rw [averagedForm_apply]
  have h1 : weylNuFunctional i ν 1 ((1 : ℝ) ⊗ₜ[ℤ] r.val) = (latticePairing T r.val ν : ℝ) := by
    rw [weylNuFunctional_apply, map_one, LinearEquiv.coe_one, id, pair_tmul_tmul]
    ring
  have hne : (latticePairing T r.val ν : ℝ) ≠ 0 := by exact_mod_cast hν r.val r.property
  calc (0 : ℝ) < weylNuFunctional i ν 1 ((1 : ℝ) ⊗ₜ[ℤ] r.val) *
        weylNuFunctional i ν 1 ((1 : ℝ) ⊗ₜ[ℤ] r.val) := by
        rw [h1]; exact mul_self_pos.mpr hne
    _ ≤ _ := Finset.single_le_sum
        (f := fun w => weylNuFunctional i ν w ((1 : ℝ) ⊗ₜ[ℤ] r.val) *
          weylNuFunctional i ν w ((1 : ℝ) ⊗ₜ[ℤ] r.val))
        (fun w _ => mul_self_nonneg _) (Finset.mem_univ 1)

/-- The sign of `⟨x, ř⟩` is the sign of `B(x, r)`. -/
theorem coroot_pair_pos_iff (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (D : RelativeRootReflectionData i) (r : relativeRoots i) (x : Vstar T) :
    0 < pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot r) ↔ 0 < averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] r.val) := by
  have h := coroot_pair_mul_form i ν D r x
  have hB := averagedForm_root_pos i ν hν r
  constructor
  · intro hc
    have : 0 < pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot r) *
        averagedForm i ν ((1 : ℝ) ⊗ₜ[ℤ] r.val) ((1 : ℝ) ⊗ₜ[ℤ] r.val) := mul_pos hc hB
    linarith
  · intro hb
    have : 0 < pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot r) *
        averagedForm i ν ((1 : ℝ) ⊗ₜ[ℤ] r.val) ((1 : ℝ) ⊗ₜ[ℤ] r.val) := by linarith
    exact pos_of_mul_pos_left this hB.le

/-- `⟨x, ř⟩ = 0` exactly when `B(x, r) = 0`. -/
theorem coroot_pair_eq_zero_iff (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (D : RelativeRootReflectionData i) (r : relativeRoots i) (x : Vstar T) :
    pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot r) = 0 ↔ averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] r.val) = 0 := by
  have h := coroot_pair_mul_form i ν D r x
  have hB := averagedForm_root_pos i ν hν r
  constructor
  · intro hc
    rw [hc, zero_mul] at h
    linarith
  · intro hb
    rw [hb, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hB.ne'

end Reflection

section Main

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]
  (ν : cocharacterLattice T)

/-- For `x` in the open coroot chamber of `J`, the averaged form `B(x, ·)` is nonnegative on
positive roots and is positive exactly where a standard cocharacter `ζ` of `J` is positive. -/
theorem averagedForm_sign_of_positive (hν : IsGenericCocharacter i ν)
    (D : RelativeRootReflectionData i) {J : Set (characterLattice T)}
    {zeta : cocharacterLattice T} (hzeta : IsStandardCocharacter i ν J zeta) (x : Vstar T)
    (hxJ : ∀ α : relativeRoots i, α.1 ∈ J → pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0)
    (hxpos : ∀ α : relativeRoots i, α.1 ∈ simpleRelativeRoots i ν → α.1 ∉ J →
      0 < pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    {β : characterLattice T} (hβ : β ∈ positiveRelativeRoots i ν) :
    0 ≤ averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] β) ∧
      (0 < averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] β) ↔ 0 < latticePairing T β zeta) := by
  refine positiveRelativeRoots_induction i ν
    (P := fun β => 0 ≤ averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] β) ∧
      (0 < averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] β) ↔ 0 < latticePairing T β zeta)) ?_ ?_ hβ
  · intro α hα
    let a : relativeRoots i := ⟨α, hα.1.1⟩
    by_cases hαJ : α ∈ J
    · have hb : averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] α) = 0 :=
        (coroot_pair_eq_zero_iff i ν hν D a x).mp (hxJ a hαJ)
      rw [hb, hzeta.2.1 α hαJ]
      exact ⟨le_rfl, by simp⟩
    · have hb : 0 < averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] α) :=
        (coroot_pair_pos_iff i ν hν D a x).mp (hxpos a hα hαJ)
      exact ⟨hb.le, iff_of_true hb (hzeta.2.2 α hα hαJ)⟩
  · intro α hα δ hδ ⟨hα0, hαs⟩ ⟨hδ0, hδs⟩
    have hz1 := hzeta.pairing_nonneg_of_positive i ν hα
    have hz2 := hzeta.pairing_nonneg_of_positive i ν hδ
    have hadd : averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] (α + δ)) =
        averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] α) + averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] δ) := by
      rw [TensorProduct.tmul_add, map_add]
    have hzadd : latticePairing T (α + δ) zeta =
        latticePairing T α zeta + latticePairing T δ zeta := by
      rw [map_add, LinearMap.add_apply]
    rw [hadd, hzadd]
    refine ⟨add_nonneg hα0 hδ0, ?_⟩
    constructor
    · intro h
      rcases lt_or_eq_of_le hα0 with h1 | h1
      · have := hαs.mp h1
        omega
      · have h2 : 0 < averagedForm i ν x ((1 : ℝ) ⊗ₜ[ℤ] δ) := by linarith
        have := hδs.mp h2
        omega
    · intro h
      rcases lt_or_eq_of_le hz1 with h1 | h1
      · have := hαs.mpr h1
        linarith
      · have h2 : 0 < latticePairing T δ zeta := by omega
        have := hδs.mpr h2
        linarith

end Main

section Restrict

/-- Restriction of real characters along the identity is the identity. -/
theorem restrictReal_id_apply {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (x : ℝ ⊗[ℤ] rationalCharacters G) : rationalCharacterRestrictReal (𝟙 G) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    simp only [rationalCharacterRestrictReal_tmul, characterRestrict_id, AddMonoidHom.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end Restrict

end CorootChamberUnipotentRoots

/-- Renard V.3.17 (printed p.114 / PDF p.120): for `μ` in the open coroot chamber of the
standard parabolic `P = MN` of `J`, the relative roots `γ` with `⟨μ, γ̌⟩ > 0` are exactly the
roots of `A_∅` in `N`. -/
theorem corootChamberUnipotentRoots : CorootChamberUnipotentRootsStatement.{u} := by
  intro k _ G hG T i hi ν
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  intro hν D J hJ x hx r
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have : Finite (relativeWeylGroup i) := hG.finite_relativeWeylGroup i hi
  let : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  obtain ⟨zeta, hzeta⟩ :=
    D.exists_standardCocharacter i ν hT (hT.finite_relativeRoots i) hν J hJ
  have hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i :=
    fun α hα => D.neg_mem_relativeRoots i hα
  rw [CorootChamberUnipotentRoots.mem_subgroupRelativeRoots_standardUnipotent_iff i ν hT hν hneg hzeta]
  obtain ⟨y, hyx, hyJ, hypos⟩ := hx
  have hxy : y = x := by
    rw [← hyx]
    exact (CorootChamberUnipotentRoots.restrictReal_id_apply y).symm
  subst hxy
  rw [CorootChamberUnipotentRoots.coroot_pair_pos_iff i ν hν D r y]
  have hr := hν r.1 r.2
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · -- `r` is negative: both sides fail
    have hpos : -r.1 ∈ positiveRelativeRoots i ν := by
      refine ⟨hneg r.1 r.2, ?_⟩
      rw [map_neg, LinearMap.neg_apply]
      omega
    have h := CorootChamberUnipotentRoots.averagedForm_sign_of_positive i ν hν D hzeta y hyJ hypos hpos
    have hz := hzeta.pairing_nonneg_of_positive i ν hpos
    rw [TensorProduct.tmul_neg, map_neg] at h
    rw [map_neg, LinearMap.neg_apply] at hz
    constructor
    · intro hb
      linarith [h.1]
    · rintro ⟨-, hzr⟩
      omega
  · have h := CorootChamberUnipotentRoots.averagedForm_sign_of_positive i ν hν D hzeta y hyJ hypos ⟨r.2, hgt⟩
    exact h.2.trans ⟨fun h => ⟨r.2, h⟩, fun h => h.2⟩

end Langlands.GroupScheme
