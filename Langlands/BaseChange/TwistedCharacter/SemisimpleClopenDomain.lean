import Langlands.BaseChange.TwistedCharacter.SemisimpleConjugationSubmersion
import Langlands.HarmonicAnalysis.UnitConjugation.PairingHaar

/-! # A clopen invariant neighborhood in the fixed algebra -/

noncomputable section

namespace Langlands.BaseChange

open ContinuousLinearMap Function Set Module Metric
open HarmonicAnalysis.UnitConjugation

variable {F R : Type*} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [NormedRing R] [NormedAlgebra F R] [CompleteSpace R] [FiniteDimensional F R]
  (α : R ≃ₐ[F] R)

local notation "S" => adjointFixedAlgebra α

/-- At a semisimple automorphism, the submersion domain contains a fixed-unit
invariant clopen neighborhood of zero. -/
def SemisimpleClopenDomainStatement : Prop :=
  Module.End.IsSemisimple α.toLinearMap →
    ∃ C : Set S, IsClopen C ∧ 0 ∈ C ∧ C ⊆ adjointConjugationDomain α ∧
      ∀ u : Sˣ, ∀ y ∈ C, conjugationHomeomorph u y ∈ C

omit [CompleteSpace F] [IsUltrametricDist F] in
private theorem det_ne_zero_iff_surjective {A : Type*} [AddCommGroup A] [Module F A]
    [FiniteDimensional F A] (T : A →ₗ[F] A) : T.det ≠ 0 ↔ Surjective T := by
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
  exact ⟨fun h => h.2, fun h => ⟨LinearMap.injective_iff_surjective.mpr h, h⟩⟩

/-- The invariant neighborhood is defined by requiring two determinants to lie
in clopen balls avoiding zero. -/
theorem semisimpleClopenDomain : SemisimpleClopenDomainStatement α := by
  intro hα
  obtain ⟨q, _, hq, hqr, _⟩ := exists_semisimpleSliceChart α hα
  let P : R →ₗ[F] S := (adjointFixedAlgebra α).toSubmodule.projectionOnto q hq
  let a : R →L[F] R := α.toLinearMap.toContinuousLinearMap
  let r (y : S) : R := 1 + y.val
  let T (y : S) : R →L[F] R :=
    mulLeftRight F R 1 (r y) + ((adjointFixedAlgebra α).val.toLinearMap.comp P).toContinuousLinearMap -
      (mulLeftRight F R (r y) 1).comp a
  have hT (y : S) (z : R) : T y z = z * r y + (P z).val - r y * α z := by
    change 1 * z * r y + (P z).val - (r y * α z * 1) = _
    rw [one_mul, mul_one]
  have hT0 (z : R) : T 0 z = z + (P z).val - α z := by rw [hT]; simp [r]
  have hPleft (x : S) : P x.val = x := Submodule.projectionOnto_apply_left hq x
  have hPright {x : R} (hx : x ∈ q) : P x = 0 := Submodule.projectionOnto_apply_of_mem_right hq hx
  have hT0s : Surjective (T 0) := by
    intro z
    obtain ⟨⟨b, c⟩, hbc⟩ := ((adjointFixedAlgebra α).toSubmodule.prodEquivOfIsCompl q hq).surjective z
    change b.val + c.val = z at hbc
    have hc : c.val ∈ LinearMap.range (LinearMap.id - α.toLinearMap) := by
      rw [← hqr]
      exact c.property
    obtain ⟨x, hx⟩ := hc
    change x - α x = c.val at hx
    let t := P x
    have ht : α t.val = t.val := t.property
    refine ⟨x - t.val + b.val, ?_⟩
    rw [hT0, map_add P, map_sub P, hPleft t, hPleft b, sub_self, zero_add,
      map_add, map_sub, ht, show α b.val = b.val from b.property]
    change x - t.val + b.val + b.val - (α x - t.val + b.val) = z
    rw [← hbc, ← hx]
    abel
  have hTc : Continuous T := by
    have hr : Continuous r := continuous_const.add continuous_subtype_val
    have h₁ : Continuous fun y : S => mulLeftRight F R 1 (r y) :=
      (mulLeftRight F R 1).continuous.comp hr
    have h₂ : Continuous fun y : S => mulLeftRight F R (r y) 1 :=
      ((mulLeftRight F R).continuous.comp hr).clm_apply continuous_const
    exact (h₁.add continuous_const).sub (h₂.clm_comp continuous_const)
  let Δ (y : S) := (T y).det
  have hΔc : Continuous Δ := ContinuousLinearMap.continuous_det.comp hTc
  have hΔ0 : Δ 0 ≠ 0 := (det_ne_zero_iff_surjective _).2 hT0s
  let M (y : S) : S →L[F] S := mulLeftRight F S (1 + y) 1
  let Ξ (y : S) := (M y).det
  have hΞc : Continuous Ξ := ContinuousLinearMap.continuous_det.comp
    (((mulLeftRight F S).continuous.comp (continuous_const.add continuous_id)).clm_apply continuous_const)
  have hM (y : S) : (M y).toLinearMap = Algebra.lmul F S (1 + y) := by
    ext x
    simp [M, mulLeftRight_apply]
  have hΞ0 : Ξ 0 = 1 := by
    change LinearMap.det (M 0).toLinearMap = 1
    rw [hM, add_zero, map_one]
    exact LinearMap.det_id
  have hconj (u : Sˣ) (y : S) :
      Δ (conjugationHomeomorph u y) = Δ y ∧ Ξ (conjugationHomeomorph u y) = Ξ y := by
    let v := Units.map (adjointFixedAlgebra α).val.toMonoidHom u
    let e := conjugationLinearEquiv F v
    let f := conjugationLinearEquiv F u
    have hαv : α v.val = v.val := u.val.property
    have hαvi : α ((v⁻¹ : Rˣ) : R) = (v⁻¹ : Rˣ).val := ((u⁻¹ : Sˣ) : S).property
    have hcomm (x : R) : α (e x) = e (α x) := by
      simp only [e, conjugationLinearEquiv_apply, map_mul, hαv, hαvi]
    have hmul (x x' : R) : e (x * x') = e x * e x' := by
      simp [e, mul_assoc]
    have heq (x : R) (hx : x ∈ q) : e x ∈ q := by
      rw [hqr] at hx ⊢
      obtain ⟨z, hz⟩ := hx
      change z - α z = x at hz
      refine ⟨e z, ?_⟩
      change e z - α (e z) = e x
      rw [hcomm, ← map_sub, hz]
    have hPe (x : R) : P (e x) = f (P x) := by
      obtain ⟨⟨b, c⟩, hbc⟩ := ((adjointFixedAlgebra α).toSubmodule.prodEquivOfIsCompl q hq).surjective x
      change b.val + c.val = x at hbc
      have hb : e b.val = (f b).val := rfl
      rw [← hbc, map_add e, map_add P, map_add P, hPleft b, hPright c.property,
        hPright (heq c.val c.property), hb, hPleft (f b), add_zero, add_zero]
    have hr (y' : S) : r (f y') = e (r y') := by
      change 1 + v.val * y'.val * ((v⁻¹ : Rˣ) : R) = v.val * (1 + y'.val) * ((v⁻¹ : Rˣ) : R)
      rw [mul_add, mul_one, add_mul, Units.mul_inv]
    have hTf : (T (f y)).toLinearMap = (e : R →ₗ[F] R) ∘ₗ (T y).toLinearMap ∘ₗ
        (e.symm : R →ₗ[F] R) := by
      ext z
      obtain ⟨x, rfl⟩ := e.surjective z
      change T (f y) (e x) = e (T y (e.symm (e x)))
      rw [e.symm_apply_apply, hT, hT, hr, hcomm, hPe, map_sub,
        map_add e (x * r y) (P x).val, hmul x (r y), hmul (r y) (α x)]
      rfl
    have hfMul (x x' : S) : f (x * x') = f x * f x' := by simp [f, mul_assoc]
    have hfOne : f (1 : S) = 1 := by simp [f]
    have hMf : (M (f y)).toLinearMap = (f : S →ₗ[F] S) ∘ₗ (M y).toLinearMap ∘ₗ
        (f.symm : S →ₗ[F] S) := by
      apply LinearMap.ext
      intro z
      obtain ⟨x, rfl⟩ := f.surjective z
      change M (f y) (f x) = f (M y (f.symm (f x)))
      rw [f.symm_apply_apply]
      change (1 + f y) * f x * 1 = f ((1 + y) * x * 1)
      rw [mul_one, mul_one, hfMul, map_add f 1 y, hfOne]
    change (T (f y)).toLinearMap.det = (T y).toLinearMap.det ∧
      (M (f y)).toLinearMap.det = (M y).toLinearMap.det
    rw [hTf, hMf, LinearMap.det_conj, LinearMap.det_conj]
    exact ⟨rfl, rfl⟩
  let C := Δ ⁻¹' closedBall (Δ 0) (‖Δ 0‖ / 2) ∩ Ξ ⁻¹' closedBall 1 (1 / 2)
  have hhalf : 0 < ‖Δ 0‖ / 2 := half_pos (norm_pos_iff.mpr hΔ0)
  refine ⟨C, ((IsUltrametricDist.isClopen_closedBall (Δ 0) hhalf.ne').preimage hΔc).inter
      ((IsUltrametricDist.isClopen_closedBall (1 : F) (by norm_num)).preimage hΞc),
    ⟨mem_closedBall_self hhalf.le, by
      change Ξ 0 ∈ closedBall (1 : F) (1 / 2)
      rw [hΞ0]
      exact mem_closedBall_self (by norm_num)⟩,
    ?_, ?_⟩
  · rintro y ⟨hyΔ, hyΞ⟩
    have hyΔ' : Δ y ≠ 0 := by
      intro hz
      have h := mem_closedBall.mp (show Δ y ∈ closedBall (Δ 0) (‖Δ 0‖ / 2) from hyΔ)
      rw [hz, dist_zero_left] at h
      exact (not_le_of_gt (half_lt_self (norm_pos_iff.mpr hΔ0))) h
    have hyΞ' : Ξ y ≠ 0 := by
      intro hz
      have h := mem_closedBall.mp (show Ξ y ∈ closedBall (1 : F) (1 / 2) from hyΞ)
      rw [hz, dist_zero_left, norm_one] at h
      norm_num at h
    refine ⟨?_, ?_⟩
    · apply (Algebra.lmul_isUnit_iff (R := F)).mp
      rw [LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← hM]
      exact hyΞ'
    · have hs : Surjective (T y) := (det_ne_zero_iff_surjective _).1 hyΔ'
      intro z
      obtain ⟨x, rfl⟩ := hs z
      exact ⟨(x, P x), by rw [hT, adjointConjugationDifferential_apply]⟩
  · rintro u y ⟨hyΔ, hyΞ⟩
    constructor
    · change Δ (conjugationHomeomorph u y) ∈ closedBall (Δ 0) (‖Δ 0‖ / 2)
      rw [(hconj u y).1]
      exact hyΔ
    · change Ξ (conjugationHomeomorph u y) ∈ closedBall (1 : F) (1 / 2)
      rw [(hconj u y).2]
      exact hyΞ

end Langlands.BaseChange
