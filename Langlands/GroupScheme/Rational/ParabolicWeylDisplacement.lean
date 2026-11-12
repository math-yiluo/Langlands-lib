import Langlands.GroupScheme.Rational.IntrinsicRootCone
import Langlands.GroupScheme.Rational.ParabolicRootConeEvaluation
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.StandardRelativeWeylGenerationReduction

/-! # Dominant Weyl displacements in the actual parabolic root cone -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace RelativeRootSystem

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- The full real character displacement `x - w x`, retaining central directions. -/
def relativeWeylDisplacement (w : relativeWeylGroup i) : Vstar T →ₗ[ℝ] Vstar T :=
  LinearMap.id - (relativeWeylFullRealAction i w).toLinearMap

omit [IsAffineHom G.X.hom] in
@[simp]
theorem relativeWeylDisplacement_apply (w : relativeWeylGroup i) (x : Vstar T) :
    relativeWeylDisplacement w x = x - relativeWeylFullRealAction i w x := rfl

omit [IsAffineHom G.X.hom] in
theorem relativeWeylDisplacement_mul (w v : relativeWeylGroup i) (x : Vstar T) :
    relativeWeylDisplacement (w * v) x = relativeWeylDisplacement w x +
      relativeWeylFullRealAction i w (relativeWeylDisplacement v x) := by
  simp only [relativeWeylDisplacement_apply, map_mul, LinearEquiv.mul_apply, map_sub]
  abel

namespace RelativeRootReflectionData

variable (D : RelativeRootReflectionData i)

/-- The supplied integral reflection formula extends to the full real character space. -/
theorem fullRealAction_representative (α : relativeRoots i) (x : Vstar T) :
    relativeWeylFullRealAction i (QuotientGroup.mk (D.representative α)) x =
      x - pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) • ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  have h : (relativeWeylFullRealAction i (QuotientGroup.mk (D.representative α))).toLinearMap =
      LinearMap.id - ((pair T).flip ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)).smulRight
        ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s χ
    change s ⊗ₜ[ℤ] weylAction i (D.representative α) χ =
      s ⊗ₜ[ℤ] χ - pair T (s ⊗ₜ[ℤ] χ) ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) •
        ((1 : ℝ) ⊗ₜ[ℤ] α.val)
    simp only [D.action, tmul_sub, pair_tmul_tmul, mul_one,
      TensorProduct.smul_tmul', tmul_smul, zsmul_eq_mul]
    simp [smul_eq_mul, mul_comm]
  exact LinearMap.congr_fun h x

/-- Each supplied normalizer reflection gives the actual quotient reflection. -/
theorem isRelativeReflection_representative (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) (α : relativeRoots i) :
    IsRelativeReflection i α.val (QuotientGroup.mk (D.representative α)) := by
  have hself : corootFunctional i (D.coroot α) (rootVector i α) = 2 := by
    rw [corootFunctional_rootVector, D.pair_self]
    norm_num
  refine ⟨α.property, corootFunctional i (D.coroot α), hself, ?_⟩
  rw [← D.reflection_eq_relativeWeylAction hT hfinite α]
  apply LinearEquiv.ext
  intro x
  change x - corootFunctional i (D.coroot α) x • rootVector i α = _
  exact (Module.reflection_apply x hself).symm

end RelativeRootReflectionData

namespace ParabolicRootPresentation

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {P M : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  [LocallyOfFiniteType G.X.hom] (r : ParabolicRootPresentation p l a)

local instance : Mono r.data.i.hom.hom.left := r.isCompatible.maximalSplit.isSplitSubtorus.mono

open Langlands.Aubert.General.RationalPointFamily

/-- Dominance for the simple coroots implies that every full Weyl displacement,
restricted to the actual split component, belongs to the parabolic root cone.
This version takes a supplied finite Coxeter realization. -/
theorem restrict_displacement_mem_nonnegCone_of_coxeter
    (D : RelativeRootReflectionData r.data.i)
    [Finite (relativeWeylGroup r.data.i)]
    {C : CoxeterMatrix (SimpleRoot r.data.i r.data.ν)}
    (cs : CoxeterSystem C (relativeWeylGroup r.data.i))
    (hcs : IsRelativeWeylCoxeterRealization r.data.i r.data.ν cs)
    (x : Vstar r.data.T)
    (hx : ∀ α : SimpleRoot r.data.i r.data.ν,
      0 ≤ pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩))
    (w : relativeWeylGroup r.data.i) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
      (relativeWeylDisplacement w x) ∈ r.nonnegCone := by
  have hT := r.isCompatible.maximalSplit.isSplitSubtorus.1
  have hfin := hT.finite_relativeRoots r.data.i
  have hs (α : SimpleRoot r.data.i r.data.ν) :
      (QuotientGroup.mk (D.representative ⟨α.val, α.property.1.1⟩) :
        relativeWeylGroup r.data.i) = cs.simple α :=
    hcs.eq_simple_of_isRelativeReflection hT α
      (D.isRelativeReflection_representative hT hfin ⟨α.val, α.property.1.1⟩)
  suffices h : ∀ n (v : relativeWeylGroup r.data.i), cs.length v = n →
      rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
        (relativeWeylDisplacement v x) ∈ r.nonnegCone from h _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hv
    by_cases hv1 : v = 1
    · subst v
      simpa [relativeWeylDisplacement] using r.zero_mem_nonnegCone
    obtain ⟨α, hα⟩ := cs.exists_rightDescent_of_ne_one hv1
    change cs.length (v * cs.simple α) < cs.length v at hα
    let v' := v * cs.simple α
    have hv' : cs.length v' < n := by
      simpa only [v', ← hv] using hα
    have hv's : v' * cs.simple α = v := cs.simple_mul_simple_cancel_right α
    have hstep : cs.length v' < cs.length (v' * cs.simple α) := by
      rw [hv's, hv]
      exact hv'
    have hpos := (hcs.2.2.1 v' α).mp hstep
    have hroot : rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
        (relativeWeylFullRealAction r.data.i v' ((1 : ℝ) ⊗ₜ[ℤ] α.val)) ∈
          r.nonnegCone := by
      change (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ schemeWeylCharacterAction r.data.i v' α.val) ∈ _
      exact r.one_tmul_restrict_mem_nonnegCone hpos
    have hsimple : relativeWeylDisplacement (cs.simple α) x =
        pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩) •
          ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
      rw [← hs α, relativeWeylDisplacement_apply, D.fullRealAction_representative]
      abel
    rw [← hv's, relativeWeylDisplacement_mul, hsimple, map_smul, map_add, map_smul]
    exact r.add_mem_nonnegCone (ih _ hv' v' rfl)
      (r.smul_mem_nonnegCone (hx α) hroot)

/-- For a connected reductive group, the proved relative Coxeter theorem supplies
all length and root-sign inputs to the dominant displacement cone bound. -/
theorem restrict_displacement_mem_nonnegCone (hG : IsConnectedReductive G)
    (D : RelativeRootReflectionData r.data.i) (x : Vstar r.data.T)
    (hx : ∀ α : SimpleRoot r.data.i r.data.ν,
      0 ≤ pair r.data.T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩))
    (w : relativeWeylGroup r.data.i) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom r.data.f)
      (relativeWeylDisplacement w x) ∈ r.nonnegCone := by
  obtain ⟨hW, _, C, cs, hcs⟩ := relativeWeylCoxeter k G hG r.data.T r.data.i
    r.isCompatible.maximalSplit r.data.ν r.isCompatible.generic
  have := hW
  exact r.restrict_displacement_mem_nonnegCone_of_coxeter D cs hcs x hx w

/-- On the nonnegative root cone, the defining evaluation vanishes exactly at zero. -/
theorem splitComponentEvaluation_eq_zero_iff_of_mem_nonnegCone
    {x : Vstar A} (hx : x ∈ r.nonnegCone) :
    r.splitComponentEvaluation x = 0 ↔ x = 0 := by
  obtain ⟨c, hc, rfl⟩ := (RootCombination.mem_nonneg r.finite_restrictedRoots).mp hx
  constructor
  · intro heval
    rw [map_sum] at heval
    have hnonneg (β) (hβ : β ∈ r.finite_restrictedRoots.toFinset) :
        0 ≤ r.splitComponentEvaluation (c β • β) := by
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg (hc β (r.finite_restrictedRoots.mem_toFinset.mp hβ))
        (r.splitComponentEvaluation_pos_of_mem_restrictedRoots
          (r.finite_restrictedRoots.mem_toFinset.mp hβ)).le
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp heval
    apply Finset.sum_eq_zero
    intro β hβ
    have hterm := hzero β hβ
    rw [map_smul, smul_eq_mul] at hterm
    have hc0 := (mul_eq_zero.mp hterm).resolve_right
      (r.splitComponentEvaluation_pos_of_mem_restrictedRoots
        (r.finite_restrictedRoots.mem_toFinset.mp hβ)).ne'
    rw [hc0, zero_smul]
  · intro heq
    rw [heq, map_zero]

/-- Every nonzero vector in the nonnegative root cone has strictly positive evaluation. -/
theorem splitComponentEvaluation_pos_of_mem_nonnegCone
    {x : Vstar A} (hx : x ∈ r.nonnegCone) (hx0 : x ≠ 0) :
    0 < r.splitComponentEvaluation x := by
  have hnonneg := r.splitComponentEvaluation_nonneg_of_mem_nonnegCone hx
  by_contra h
  exact hx0 ((r.splitComponentEvaluation_eq_zero_iff_of_mem_nonnegCone hx).mp
    (le_antisymm (not_lt.mp h) hnonneg))

/-- Adding a vector in the cone to a nonzero vector in the cone cannot give zero. -/
theorem add_ne_zero_of_mem_nonnegCone {x y : Vstar A}
    (hx : x ∈ r.nonnegCone) (hy : y ∈ r.nonnegCone) (hy0 : y ≠ 0) : x + y ≠ 0 := by
  intro heq
  have h := congrArg r.splitComponentEvaluation heq
  rw [map_add, map_zero] at h
  have := r.splitComponentEvaluation_nonneg_of_mem_nonnegCone hx
  have := r.splitComponentEvaluation_pos_of_mem_nonnegCone hy hy0
  linarith

end ParabolicRootPresentation

end Langlands.GroupScheme
