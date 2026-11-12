import Langlands.GroupScheme.Rational.ParabolicCorootLiftUniqueness
import Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction

/-! # Full real lifts of actual Levi split-component parameters

Restriction identifies the selected-coroot annihilator in the full maximal
split-torus character space with the actual Levi split-component space.
Surjectivity follows by averaging over the finite selected Weyl subgroup.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

open RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

namespace RelativeRootReflectionData

variable (D : RelativeRootReflectionData i)

/-- Left multiplication reindexes the selected Weyl sum. -/
theorem fullRealAction_selectedWeylSum (J : Set (characterLattice T))
    [Fintype (D.selectedWeylGroup J)] (w : D.selectedWeylGroup J) (x : Vstar T) :
    relativeWeylFullRealAction i w.val (D.selectedWeylSum J x) =
      D.selectedWeylSum J x := by
  simp only [selectedWeylSum_apply, map_sum]
  simp_rw [← LinearEquiv.mul_apply, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft w) _ _ (fun _ => rfl)

/-- The selected Weyl sum annihilates every selected coroot. -/
theorem pair_selectedWeylSum_selectedCoroot (J : Set (characterLattice T))
    [Fintype (D.selectedWeylGroup J)] (x : Vstar T)
    (α : relativeRoots i) (hα : α.val ∈ J) :
    pair T (D.selectedWeylSum J x) ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0 := by
  let w : D.selectedWeylGroup J :=
    ⟨QuotientGroup.mk (D.representative α), Subgroup.subset_closure ⟨α, hα, rfl⟩⟩
  have hfix := D.fullRealAction_selectedWeylSum J w x
  change relativeWeylFullRealAction i (QuotientGroup.mk (D.representative α))
    (D.selectedWeylSum J x) = D.selectedWeylSum J x at hfix
  rw [D.fullRealAction_representative] at hfix
  have heval := congrArg (fun y => pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) hfix
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    pair_tmul_tmul, D.pair_self] at heval
  norm_num at heval
  simpa only [selectedWeylSum_apply, map_sum, LinearMap.sum_apply] using heval

end RelativeRootReflectionData

namespace ParabolicRootPresentation

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {P M : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance : Mono r.data.i.hom.hom.left := r.isCompatible.maximalSplit.isSplitSubtorus.mono

/-- The full vectors annihilating the selected actual coroots. -/
def selectedCorootAnnihilator (D : RelativeRootReflectionData r.data.i) :
    Submodule ℝ (Vstar r.data.T) where
  carrier := {x | ∀ α : relativeRoots r.data.i, α.val ∈ r.data.J →
    pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy α hα; simp [hx α hα, hy α hα]
  smul_mem' := by intro c x hx α hα; simp [hx α hα]

section FiniteType

variable [LocallyOfFiniteType G.X.hom]

/-- The selected Weyl subgroup acts trivially after restriction to the actual
Levi split component. -/
theorem restrict_fullRealAction_selectedWeylGroup
    (D : RelativeRootReflectionData r.data.i) (x : Vstar r.data.T)
    {w : relativeWeylGroup r.data.i} (hw : w ∈ D.selectedWeylGroup r.data.J) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
        (relativeWeylFullRealAction r.data.i w x) =
      rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f) x := by
  induction hw using Subgroup.closure_induction generalizing x with
  | mem w hw =>
    obtain ⟨α, hα, rfl⟩ := hw
    rw [D.fullRealAction_representative, map_sub, map_smul,
      rationalCharacterRestrictReal_tmul]
    change _ - _ • ((1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ α.val)) = _
    rw [r.selectedRoot_restrict_eq_zero hα, tmul_zero, smul_zero, sub_zero]
  | one => simp
  | mul w v _ _ hw hv => rw [map_mul, LinearEquiv.mul_apply, hw, hv]
  | inv w _ hw =>
    have he := hw (relativeWeylFullRealAction r.data.i w⁻¹ x)
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at he
    exact he.symm

/-- The unnormalized Weyl sum restricts to the subgroup order times the
original split-component parameter. -/
theorem restrict_selectedWeylSum (D : RelativeRootReflectionData r.data.i)
    [Fintype (D.selectedWeylGroup r.data.J)] (x : Vstar r.data.T) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
        (D.selectedWeylSum r.data.J x) =
      (Fintype.card (D.selectedWeylGroup r.data.J) : ℝ) •
        rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f) x := by
  simp only [D.selectedWeylSum_apply, map_sum,
    r.restrict_fullRealAction_selectedWeylGroup D x (Subtype.mem _)]
  simp [Nat.cast_smul_eq_nsmul]

/-- Every actual split-component real parameter has a unique full lift
annihilating the selected coroots. No chamber condition is required. -/
theorem existsUnique_selectedCorootLift (hG : IsConnectedReductive G)
    (D : RelativeRootReflectionData r.data.i) (y : Vstar A) :
    ∃! x : Vstar r.data.T,
      rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f) x = y ∧
        x ∈ r.selectedCorootAnnihilator D := by
  classical
  have := hG.finite_relativeWeylGroup r.data.i r.isCompatible.maximalSplit
  let H := D.selectedWeylGroup r.data.J
  let : Fintype H := Fintype.ofFinite H
  have hmono : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
    have hcomp : Mono
        ((CommGroupScheme.groupHom r.data.f).hom.hom.left ≫ r.data.i.hom.hom.left) := by
      change Mono (CommGroupScheme.groupHom r.data.f ≫ r.data.i).hom.hom.left
      rw [r.isCompatible.factor_comp]
      have := r.isCompatible.splitComponent.isCentralSplitTorus.1.mono
      have := r.isCompatible.levi.isClosedSubgroup.mono
      have := r.isCompatible.parabolic.isClosedSubgroup.mono
      change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
      infer_instance
    exact mono_of_mono (CommGroupScheme.groupHom r.data.f).hom.hom.left
      r.data.i.hom.hom.left
  obtain ⟨x, hx⟩ :=
    r.isCompatible.splitComponent.isCentralSplitTorus.1.1.rationalCharacterRestrictReal_surjective_of_mono
      r.isCompatible.maximalSplit.isSplitSubtorus.1
      (CommGroupScheme.groupHom r.data.f) y
  have hc : (Fintype.card H : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let z := (Fintype.card H : ℝ)⁻¹ • D.selectedWeylSum r.data.J x
  have hzres : rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f) z = y := by
    rw [map_smul, r.restrict_selectedWeylSum D x, hx, smul_smul, inv_mul_cancel₀ hc,
      one_smul]
  have hzpair : z ∈ r.selectedCorootAnnihilator D := by
    intro α hα
    simp only [z, map_smul, LinearMap.smul_apply,
      D.pair_selectedWeylSum_selectedCoroot r.data.J x α hα, smul_zero]
  refine ⟨z, ⟨hzres, hzpair⟩, ?_⟩
  rintro x' ⟨hx'res, hx'pair⟩
  exact r.eq_of_restrict_eq_of_selectedCoroot_pair_eq_zero hG D x' z
    hx'pair hzpair (hx'res.trans hzres.symm)

/-- The unique full lift as a real linear map. -/
def selectedCorootLift (hG : IsConnectedReductive G)
    (D : RelativeRootReflectionData r.data.i) : Vstar A →ₗ[ℝ] Vstar r.data.T where
  toFun y := (r.existsUnique_selectedCorootLift hG D y).choose
  map_add' x y := by
    refine (r.existsUnique_selectedCorootLift hG D (x + y)).unique
      (r.existsUnique_selectedCorootLift hG D (x + y)).choose_spec.1 ?_
    exact ⟨by rw [map_add,
      (r.existsUnique_selectedCorootLift hG D x).choose_spec.1.1,
      (r.existsUnique_selectedCorootLift hG D y).choose_spec.1.1],
      (r.selectedCorootAnnihilator D).add_mem
        (r.existsUnique_selectedCorootLift hG D x).choose_spec.1.2
        (r.existsUnique_selectedCorootLift hG D y).choose_spec.1.2⟩
  map_smul' c x := by
    refine (r.existsUnique_selectedCorootLift hG D (c • x)).unique
      (r.existsUnique_selectedCorootLift hG D (c • x)).choose_spec.1 ?_
    exact ⟨by
      rw [map_smul, (r.existsUnique_selectedCorootLift hG D x).choose_spec.1.1]
      rfl,
      (r.selectedCorootAnnihilator D).smul_mem c
        (r.existsUnique_selectedCorootLift hG D x).choose_spec.1.2⟩

/-- Restriction recovers the original actual split-component parameter. -/
@[simp] theorem restrict_selectedCorootLift (hG : IsConnectedReductive G)
    (D : RelativeRootReflectionData r.data.i) (y : Vstar A) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
      (r.selectedCorootLift hG D y) = y :=
  (r.existsUnique_selectedCorootLift hG D y).choose_spec.1.1

/-- Every selected coroot pairs to zero with the constructed full lift. -/
theorem pair_selectedCorootLift_selectedCoroot (hG : IsConnectedReductive G)
    (D : RelativeRootReflectionData r.data.i) (y : Vstar A)
    (α : relativeRoots r.data.i) (hα : α.val ∈ r.data.J) :
    pair r.data.T (r.selectedCorootLift hG D y) ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0 :=
  (r.existsUnique_selectedCorootLift hG D y).choose_spec.1.2 α hα

/-- A full vector already annihilating the selected coroots is its restriction's
constructed full lift. -/
theorem selectedCorootLift_restrict (hG : IsConnectedReductive G)
    (D : RelativeRootReflectionData r.data.i) (x : Vstar r.data.T)
    (hx : x ∈ r.selectedCorootAnnihilator D) :
    r.selectedCorootLift hG D
      (rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f) x) = x := by
  exact ((r.existsUnique_selectedCorootLift hG D _).choose_spec.2 x ⟨rfl, hx⟩).symm

/-- The constructed full lift is injective. -/
theorem selectedCorootLift_injective (hG : IsConnectedReductive G)
    (D : RelativeRootReflectionData r.data.i) :
    Function.Injective (r.selectedCorootLift hG D) := by
  intro x y hxy
  have h := congrArg (rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)) hxy
  simpa only [r.restrict_selectedCorootLift] using h

end FiniteType
end ParabolicRootPresentation
end Langlands.GroupScheme
