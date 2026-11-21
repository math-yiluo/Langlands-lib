import Langlands.Global.AdelicBlockCoefficientDifferential
import Langlands.Global.AdelicBlockSmoothScalarSections

/-!
# Archimedean differentiation of adelic scalar sections

Differentiation in an actual archimedean Lie direction preserves the realized
coefficient space of each normalized compact slice.
-/

noncomputable section

open scoped BigOperators Classical ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1250000
set_option synthInstance.maxHeartbeats 85000

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear NumberField
open AdelicBlockParabolic AdelicBlockDeterminantCharacter PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "A" => ArchimedeanMatrix F n
local notation "KI" => standardInfiniteCompact F n
local notation "KF" => FiniteAdelicGL.standardIntegral F n
local notation "W" => coefficientValues F B S
local notation "e" => archimedeanGLCoordinates F n
local notation "μ∞" => (B.leviProjection (InfiniteAdeles F))

/-- Apply the mixed matrix directional derivative in the infinite slice at
the finite component of the argument. -/
def scalarDirectionalDerivative (X : ArchimedeanGL.RealLieAlgebra F n)
    (f : AdelicGL F n → ℂ) (g : AdelicGL F n) : ℂ :=
  let a := (e (AdelicGL.infinite F n g)).val
  fderiv ℝ (infiniteSliceExtension F f (AdelicGL.finite F n g)) a
    (a * ArchimedeanGL.realLieAlgebraToMatrix F n X)

@[simp]
theorem scalarDirectionalDerivative_pair (X : ArchimedeanGL.RealLieAlgebra F n)
    (f : AdelicGL F n → ℂ) (a : InfiniteAdelicGL F n) (d : FiniteAdelicGL F n) :
    scalarDirectionalDerivative F X f (AdelicGL.pair F n a d) =
      fderiv ℝ (infiniteSliceExtension F f d) (e a).val
        ((e a).val * ArchimedeanGL.realLieAlgebraToMatrix F n X) := by
  rw [scalarDirectionalDerivative, AdelicGL.infinite_pair, AdelicGL.finite_pair]

private theorem normalized_leftParabolic_eval (f : RealizedSections F B S) (a : Infinite F B)
    (q : KI) (l : KF) (m : FullLevi F B) :
    (leviHalfCharacter F B m : ℂ)⁻¹ *
      f.val (B.leviEmbedding (Adeles F) m * (ofInfinite F B a).val * (compactPair F q l).val) =
      archimedeanHalfExtension F B (e a.val).val *
        normalizedSlice F B f.val (compactPair F q l) (m * leviPair F B (μ∞ a) 1) := by
  let j := B.leviInParabolic (Adeles F) m
  change (leviHalfCharacter F B m : ℂ)⁻¹ *
    f.val ((j * ofInfinite F B a).val * (compactPair F q l).val) = _
  have hproj : B.leviProjection (Adeles F) (ofInfinite F B a) =
      leviPair F B (μ∞ a) 1 := by
    change B.leviProjection (Adeles F) (AdelicBlockParabolic.pair F B a 1) = _
    rw [leviProjection_pair, map_one]
  rw [scalarSection_apply_mul F B W f, map_mul (parabolicHalfCharacter F B), Units.val_mul,
    parabolicHalfCharacter_section, ← archimedeanHalfExtension_parabolic,
    map_mul (B.leviProjection (Adeles F)), B.leviProjection_section, hproj]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

private theorem coefficientExtension_leviMatrix (m : FullLevi F B) (c : W) :
    coefficientExtension F B S (leviFinite F B m) c (infiniteLeviMatrix F B m) =
      c.val m := by
  have h11 : leviPair F B (1 : InfiniteLevi F B) (1 : FiniteLevi F B) = 1 := by
    simpa only [map_one] using leviPair_projections F B (1 : FullLevi F B)
  simpa only [OneMemClass.coe_one, map_one, Units.val_one, h11, mul_one] using
    coefficientExtension_levi_mul_parabolic F B S m c 1

private theorem normalizedSlice_derivative_mem_pair (f : CompactFiniteRealizedSections F B S)
    (hf : HasSmoothCompactSlices F B S f.val.val)
    (X : ArchimedeanGL.RealLieAlgebra F n) (k : KI) (l : KF) :
    normalizedSlice F B (scalarDirectionalDerivative F X f.val.val.val) (compactPair F k l) ∈ W := by
  obtain ⟨r, c, φ, hφ, hExpansion⟩ := exists_smoothCompactSlice_expansion F B S f hf k l
  obtain ⟨b, q, hb, hq, hb₁, hq₁, hFact⟩ := ArchimedeanGL.exists_smoothLocalIwasawa_at_one F n
  let u := e k.val
  let x := ArchimedeanGL.realLieAlgebraToMatrix F n X
  let y : A := u.val * x * u.inv
  let p (t : ℝ) : A := 1 + t • y
  let β (t : ℝ) : A := b (p t)
  let γ (t : ℝ) : A := q (p t) * u.val
  have hp₀ : p 0 = 1 := by simp [p]
  have hp : HasDerivAt p y 0 := by
    simpa only [one_smul] using ((hasDerivAt_id' (x := (0 : ℝ))).smul_const y).const_add (1 : A)
  have hβ₀ : β 0 = 1 := by
    change b (p 0) = 1
    rw [hp₀, hb₁]
  have hγ₀ : γ 0 = compactMatrix F k := by
    change q (p 0) * u.val = u.val
    rw [hp₀, hq₁, one_mul]
  have hβ : DifferentiableAt ℝ β 0 := by
    have h := hb.differentiableAt (by simp)
    rw [← hp₀] at h
    exact h.comp 0 hp.differentiableAt
  have hγ : DifferentiableAt ℝ γ 0 := by
    have h := hq.differentiableAt (by simp)
    rw [← hp₀] at h
    exact (h.comp 0 hp.differentiableAt).mul_const u.val
  have hHalf : DifferentiableAt ℝ (archimedeanHalfExtension F B) (1 : A) := by
    simpa only [OneMemClass.coe_one, map_one, Units.val_one] using
      (contDiffAt_archimedeanHalfExtension F B (1 : Infinite F B)).differentiableAt (by simp)
  let ψ (j : Fin r) (t : ℝ) := archimedeanHalfExtension F B (β t) * φ j (γ t)
  have hψ (j : Fin r) : DifferentiableAt ℝ (ψ j) 0 := by
    rw [← hβ₀] at hHalf
    have h := (hφ j).differentiableAt (by simp)
    rw [← hγ₀] at h
    exact (hHalf.comp 0 hβ).mul (h.comp 0 hγ)
  let w : W := ∑ j, (deriv (ψ j) 0 • c j +
    ψ j 0 • coefficientDifferential F B S (deriv β 0) (c j))
  suffices heq : normalizedSlice F B (scalarDirectionalDerivative F X f.val.val.val)
      (compactPair F k l) = w.val by
    rw [heq]
    exact w.property
  funext m
  let ji := B.leviEmbedding (InfiniteAdeles F) (leviInfinite F B m)
  let jf := B.leviEmbedding (FiniteAdeles F) (leviFinite F B m)
  let a := ji * k.val
  let d := jf * l.val
  let g : ArchimedeanGL F n := e a
  let path (t : ℝ) : A := infiniteLeviMatrix F B m * (p t * u.val)
  let C (j : Fin r) (t : ℝ) := coefficientExtension F B S (leviFinite F B m) (c j)
    (infiniteLeviMatrix F B m * β t)
  have hC₀ (j : Fin r) : C j 0 = (c j).val m := by
    change coefficientExtension F B S (leviFinite F B m) (c j)
      (infiniteLeviMatrix F B m * β 0) = _
    rw [hβ₀, mul_one, coefficientExtension_leviMatrix]
  have hSum : HasDerivAt (fun t => ∑ j, ψ j t * C j t) (w.val m) 0 := by
    have h (j : Fin r) : HasDerivAt (fun t => ψ j t * C j t)
        (deriv (ψ j) 0 * (c j).val m + ψ j 0 *
          (coefficientDifferential F B S (deriv β 0) (c j)).val m) 0 := by
      rw [← hC₀]
      exact (hψ j).hasDerivAt.mul
        (coefficientExtension_hasDerivAt F B S m (c j) hβ₀ hβ.hasDerivAt)
    simpa only [w, Submodule.coe_sum, Submodule.coe_add, Submodule.coe_smul,
      Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => h j))
  have hjPair : AdelicGL.pair F n ji jf = B.leviEmbedding (Adeles F) m := by
    have h := AdelicBlockParabolic.pair_projections F B (B.leviInParabolic (Adeles F) m)
    rw [infinite_leviInParabolic, finite_leviInParabolic] at h
    exact congrArg Subtype.val h
  have had : AdelicGL.pair F n a d = B.leviEmbedding (Adeles F) m * (compactPair F k l).val := by
    change AdelicGL.pair F n (ji * k.val) (jf * l.val) = _
    rw [← AdelicGL.pair_mul, hjPair, compactPair_val]
  have hg : g.val = infiniteLeviMatrix F B m * u.val := by
    change (e (ji * k.val)).val = _
    rw [map_mul, Units.val_mul]
  have hpath₀ : g.val = path 0 := by
    change g.val = infiniteLeviMatrix F B m * (p 0 * u.val)
    rw [hp₀, one_mul, hg]
  have hy : y * u.val = u.val * x := by
    change (u.val * x * (u⁻¹ : ArchimedeanGL F n).val) * u.val = _
    rw [mul_assoc (u.val * x), u.inv_mul, mul_one]
  have hpath : HasDerivAt path (g.val * x) 0 := by
    simpa only [hy, hg, mul_assoc] using (hp.mul_const u.val).const_mul (infiniteLeviMatrix F B m)
  have hDiff := (contDiffAt_infiniteSliceExtension F B S f hf d g).differentiableAt (by simp)
  have hCurve := (hDiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath hpath₀).const_mul
    (leviHalfCharacter F B m : ℂ)⁻¹
  have hNearP := hp.continuousAt
  rw [ContinuousAt, hp₀] at hNearP
  have hNearΓ := hγ.continuousAt
  rw [ContinuousAt, hγ₀] at hNearΓ
  have hAgree : (fun t => (leviHalfCharacter F B m : ℂ)⁻¹ *
      infiniteSliceExtension F f.val.val.val d (path t)) =ᶠ[𝓝 0]
      (fun t => ∑ j, ψ j t * C j t) := by
    filter_upwards [hNearP.eventually hFact, hNearΓ.eventually hExpansion] with t ht he
    let a' : Infinite F B := ⟨(e).symm ht.2.1.unit, by
      apply B.mem_parabolic_of_isUpperTriangular
      intro i j hij
      change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (ht.2.1.unit.val i j) = 0
      rw [ht.2.1.unit_spec, ht.1 hij, map_zero]⟩
    let q' : KI := ⟨(e).symm (Unitary.toUnits ⟨q (p t), ht.2.2.1⟩),
      (ArchimedeanGL.mem_standardInfiniteCompact_iff_mem_unitary F n _).mpr (by
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact ht.2.2.1)⟩
    have ha' : (e a'.val).val = β t :=
      (congrArg Units.val ((e).apply_symm_apply ht.2.1.unit)).trans ht.2.1.unit_spec
    have hq' : (e q'.val).val = q (p t) :=
      congrArg Units.val ((e).apply_symm_apply (Unitary.toUnits ⟨q (p t), ht.2.2.1⟩))
    have hqk : compactMatrix F (q' * k) = γ t := by
      change (e (q'.val * k.val)).val = _
      rw [map_mul, Units.val_mul, hq']
    have hv : (e (ji * a'.val * (q' * k).val)).val = path t := by
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ha']
      change infiniteLeviMatrix F B m * β t * compactMatrix F (q' * k) = _
      rw [hqk, mul_assoc]
      change infiniteLeviMatrix F B m * (b (p t) * (q (p t) * u.val)) =
        infiniteLeviMatrix F B m * (p t * u.val)
      rw [← mul_assoc (b (p t)), ht.2.2.2]
    have hvalue : infiniteSliceExtension F f.val.val.val d (path t) =
        f.val.val.val (B.leviEmbedding (Adeles F) m * (ofInfinite F B a').val *
          (compactPair F (q' * k) l).val) := by
      rw [← hv, infiniteSliceExtension_apply, ContinuousMulEquiv.symm_apply_apply, ← hjPair]
      change f.val.val.val (AdelicGL.pair F n (ji * a'.val * (q' * k).val) (jf * l.val)) =
        f.val.val.val (AdelicGL.pair F n ji jf * AdelicGL.pair F n a'.val 1 *
          AdelicGL.pair F n (q' * k).val l.val)
      rw [AdelicGL.pair_mul, AdelicGL.pair_mul, mul_one]
    rw [hvalue, normalized_leftParabolic_eval F B S f.val.val, he (q' * k) hqk, ha']
    have hC (j : Fin r) : (c j).val (m * leviPair F B (μ∞ a') 1) = C j t := by
      change _ = coefficientExtension F B S (leviFinite F B m) (c j)
        (infiniteLeviMatrix F B m * β t)
      rw [← ha', coefficientExtension_levi_mul_parabolic]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hC, ψ, Finset.mul_sum, mul_assoc]
  simp only [normalizedSlice, ← had, scalarDirectionalDerivative_pair]
  exact hCurve.unique (hSum.congr_of_eventuallyEq hAgree)

/-- The derivative has realized normalized Levi slices at every full compact point. -/
theorem normalizedSlice_derivative_mem (f : CompactFiniteRealizedSections F B S)
    (hf : HasSmoothCompactSlices F B S f.val.val) (X : ArchimedeanGL.RealLieAlgebra F n)
    (k : standardCompact F n) :
    normalizedSlice F B (scalarDirectionalDerivative F X f.val.val.val) k ∈ W := by
  have h := (mem_standardCompact_iff F n k.val).mp k.property
  let a : KI := ⟨AdelicGL.infinite F n k.val, h.1⟩
  let d : KF := ⟨AdelicGL.finite F n k.val, h.2⟩
  have he : compactPair F a d = k := Subtype.ext (AdelicGL.pair_projections F n k.val)
  rw [← he]
  exact normalizedSlice_derivative_mem_pair F B S f hf X a d

end Langlands.Global.AdelicBlockScalarSections
