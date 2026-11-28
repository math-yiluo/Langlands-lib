import Langlands.ClassFieldTheory.Global.CofiniteQuadraticNorm
import Langlands.Global.AdelicFunctoriality.Inclusion
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Cofinite quadratic norm representation in finite commutative algebras -/

noncomputable section

open NumberField IsDedekindDomain Filter
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.ClassFieldTheory.Global

open Langlands.Global.AdelicFunctoriality

universe u

section NumberFields

variable {F L : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

omit [NumberField F] in
private theorem eventually_forall_above {p : HeightOneSpectrum (𝓞 L) → Prop}
    (hp : ∀ᶠ w in cofinite, p w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ w : FinitePlacesAbove L v, p w.1 := by
  classical
  refine eventually_cofinite.mpr (((eventually_cofinite.mp hp).image (fun w => w.under (𝓞 F))).subset ?_)
  intro v hv
  obtain ⟨w, hw⟩ := not_forall.mp hv
  exact ⟨w.1, hw, finitePlacesAbove_under v w⟩

private theorem eventually_tensor_quadratic_norm_form (d : F) (hd : d ≠ 0) (a : Lˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∃ x y : v.adicCompletion F ⊗[F] L,
        x ^ 2 - algebraMap F _ d * y ^ 2 = (1 : v.adicCompletion F) ⊗ₜ[F] (a : L) := by
  classical
  have h := eventually_quadratic_norm_form (algebraMap F L d)
    ((map_ne_zero_iff _ (algebraMap F L).injective).mpr hd) a
  filter_upwards [eventually_forall_above (F := F) h] with v hv
  choose x y hxy using hv
  let f := AlgEquiv.ofBijective (finiteTensorMap (L := L) v) ((completedTensorComparison F L).1 v)
  refine ⟨f.symm x, f.symm y, f.injective ?_⟩
  simp only [map_sub, map_pow, map_mul, f.apply_symm_apply]
  funext w
  have hscalar : f (algebraMap F (v.adicCompletion F ⊗[F] L) d) w =
      algebraMap L (w.1.adicCompletion L) (algebraMap F L d) := by
    rw [Algebra.TensorProduct.algebraMap_apply']
    change finiteTensorMap (L := L) v ((1 : v.adicCompletion F) ⊗ₜ[F] algebraMap F L d) w = _
    simp only [finiteTensorMap_tmul, map_one, one_mul]
  have hunit : f ((1 : v.adicCompletion F) ⊗ₜ[F] (a : L)) w =
      algebraMap L (w.1.adicCompletion L) (a : L) := by
    change finiteTensorMap (L := L) v ((1 : v.adicCompletion F) ⊗ₜ[F] (a : L)) w = _
    simp only [finiteTensorMap_tmul, map_one, one_mul]
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, hscalar, hunit]
  exact hxy w

end NumberFields

private theorem exists_square_one_add_of_nilpotent {A : Type u} [CommRing A]
    (half : A) (hhalf : half + half = 1) (z : A) (hz : IsNilpotent z) :
    ∃ r : A, r ^ 2 = 1 + z := by
  obtain ⟨n, hn⟩ := hz
  induction n using Nat.strong_induction_on generalizing z with
  | h n ih =>
    by_cases hn₀ : n = 0
    · rw [hn₀, pow_zero] at hn
      have hz0 : z = 0 := by rw [← one_mul z, hn, zero_mul]
      exact ⟨1, by rw [one_pow, hz0, add_zero]⟩
    by_cases hn₁ : n = 1
    · refine ⟨1, ?_⟩
      simp only [hn₁, pow_one] at hn
      simp [hn]
    have hnil : IsNilpotent (half * z) := ⟨n, by rw [mul_pow, hn, mul_zero]⟩
    have hu : IsUnit (1 + half * z) := hnil.isUnit_one_add
    let u := hu.unit
    let q : A := -(half * z) ^ 2 * (↑u⁻¹ : A) ^ 2
    have hq : q = (-(half ^ 2) * (↑u⁻¹ : A) ^ 2) * z ^ 2 := by
      dsimp only [q]
      ring
    have hq' : q ^ (n - 1) = 0 := by
      rw [hq, mul_pow, ← pow_mul]
      have hbound : n ≤ 2 * (n - 1) := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hbound
      rw [hk, pow_add, hn, zero_mul, mul_zero]
    obtain ⟨r, hr⟩ := ih (n - 1) (by omega) q hq'
    refine ⟨(u : A) * r, ?_⟩
    rw [mul_pow, hr]
    calc
      (u : A) ^ 2 * (1 + q) = (u : A) ^ 2 - (half * z) ^ 2 * ((u : A) * ↑u⁻¹) ^ 2 := by
        dsimp only [q]
        ring
      _ = (1 + half * z) ^ 2 - (half * z) ^ 2 := by
        rw [Units.mul_inv, one_pow, mul_one, IsUnit.unit_spec]
      _ = 1 + (half + half) * z := by ring
      _ = 1 + z := by rw [hhalf, one_mul]

/-- A unit of a finite commutative algebra over a number field is represented by
any nondegenerate scalar quadratic norm form at all but finitely many finite places. -/
def CofiniteQuadraticNormAlgebraStatement : Prop :=
  ∀ (F A : Type u) [Field F] [NumberField F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (d : F), d ≠ 0 → ∀ a : Aˣ,
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∃ x y : v.adicCompletion F ⊗[F] A,
        x ^ 2 - algebraMap F _ d * y ^ 2 = (1 : v.adicCompletion F) ⊗ₜ[F] (a : A)

theorem cofiniteQuadraticNormAlgebra : CofiniteQuadraticNormAlgebraStatement.{u} := by
  classical
  intro F A _ _ _ _ _ d hd a
  let : IsArtinianRing A := IsArtinianRing.of_finite F A
  let D := A ⧸ nilradical A
  let q := Ideal.Quotient.mkₐ F (nilradical A)
  let I := MaximalSpectrum A
  let : Fintype I := Fintype.ofFinite I
  let K (i : I) := A ⧸ i.asIdeal
  let : ∀ i : I, Field (K i) := fun i => Ideal.Quotient.field i.asIdeal
  let : ∀ i : I, NumberField (K i) := fun i => NumberField.of_module_finite F (K i)
  let e : D ≃ₐ[F] ∀ i : I, K i := (IsArtinianRing.quotNilradicalEquivPi A).restrictScalars F
  let : Algebra.FormallySmooth F (∀ i : I, K i) := (Algebra.FormallySmooth.pi_iff K).2 (fun i => by
    let : Algebra.FormallyEtale F (K i) := Algebra.FormallyEtale.of_isSeparable F (K i)
    infer_instance)
  let : Algebra.FormallySmooth F D := Algebra.FormallySmooth.of_equiv e.symm
  obtain ⟨s, hs⟩ := Algebra.FormallySmooth.exists_lift (nilradical A)
    (IsArtinianRing.isNilpotent_nilradical (R := A)) (AlgHom.id F D)
  let b : Aˣ := Units.map s.toMonoidHom (Units.map q.toMonoidHom a)
  have hb : Units.map q.toMonoidHom b = Units.map q.toMonoidHom a := by
    apply Units.ext
    exact AlgHom.congr_fun hs (q a)
  have hnil : IsNilpotent ((a : A) * (↑b⁻¹ : A) - 1) := by
    change (a : A) * (↑b⁻¹ : A) - 1 ∈ nilradical A
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change q ((a : A) * (↑b⁻¹ : A) - 1) = 0
    rw [map_sub, map_mul, map_one]
    have h : q (a : A) = q (b : A) := (congrArg Units.val hb).symm
    rw [h, ← map_mul, Units.mul_inv, map_one, sub_self]
  let half := algebraMap F A ((2 : F)⁻¹)
  have hhalf : half + half = 1 := by
    rw [← map_add, ← map_one (algebraMap F A)]
    congr 1
    field_simp
    ring
  obtain ⟨r, hr⟩ := exists_square_one_add_of_nilpotent half hhalf _ hnil
  have hrb : r ^ 2 * (b : A) = (a : A) := by
    have h : 1 + ((a : A) * (↑b⁻¹ : A) - 1) = (a : A) * (↑b⁻¹ : A) := by ring
    rw [hr, h, mul_assoc, Units.inv_mul, mul_one]
  let κ (i : I) : D →ₐ[F] K i := (Pi.evalAlgHom F K i).comp e.toAlgHom
  let aᵢ (i : I) : (K i)ˣ := Units.map (κ i).toMonoidHom (Units.map q.toMonoidHom a)
  have ha := eventually_all.mpr fun i : I => eventually_tensor_quadratic_norm_form d hd (aᵢ i)
  filter_upwards [ha] with v hv
  let R := v.adicCompletion F
  let f : R ⊗[F] D ≃ₐ[R] ∀ i : I, R ⊗[F] K i :=
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans (Algebra.TensorProduct.piRight F R R K)
  choose x y hxy using hv
  let j : R ⊗[F] D →ₐ[R] R ⊗[F] A := Algebra.TensorProduct.map (AlgHom.id R R) s
  let t : R ⊗[F] A := (1 : R) ⊗ₜ[F] r
  have h : f.symm x ^ 2 - algebraMap F (R ⊗[F] D) d * f.symm y ^ 2 = (1 : R) ⊗ₜ[F] q a := by
    apply f.injective
    simp only [map_sub, map_pow, map_mul, f.apply_symm_apply]
    funext i
    have hscalar : f (algebraMap F (R ⊗[F] D) d) i = algebraMap F (R ⊗[F] K i) d := by
      change (Algebra.TensorProduct.piRight F R R K)
        ((algebraMap F R d) ⊗ₜ[F] e (1 : D)) i = _
      rw [map_one, Algebra.TensorProduct.piRight_tmul]
      rfl
    have hunit : f ((1 : R) ⊗ₜ[F] q (a : A)) i = (1 : R) ⊗ₜ[F] (aᵢ i : K i) := by
      change (Algebra.TensorProduct.piRight F R R K) ((1 : R) ⊗ₜ[F] e (q a)) i = _
      rw [Algebra.TensorProduct.piRight_tmul]
      rfl
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, hscalar, hunit]
    exact hxy i
  have hj := congrArg j h
  have hjd : j (algebraMap F (R ⊗[F] D) d) = algebraMap F (R ⊗[F] A) d :=
    (j.restrictScalars F).commutes d
  rw [map_sub, map_pow, map_mul, map_pow, hjd] at hj
  change j (f.symm x) ^ 2 - algebraMap F (R ⊗[F] A) d * j (f.symm y) ^ 2 = (1 : R) ⊗ₜ[F] (b : A) at hj
  refine ⟨t * j (f.symm x), t * j (f.symm y), ?_⟩
  calc
    _ = t ^ 2 * (j (f.symm x) ^ 2 - algebraMap F (R ⊗[F] A) d * j (f.symm y) ^ 2) := by ring
    _ = (1 : R) ⊗ₜ[F] (r ^ 2 * (b : A)) := by
      rw [hj]
      change ((1 : R) ⊗ₜ[F] r) ^ 2 * ((1 : R) ⊗ₜ[F] (b : A)) = _
      simp only [pow_two, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    _ = _ := by rw [hrb]

end Langlands.ClassFieldTheory.Global
