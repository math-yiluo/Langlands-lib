import Langlands.Galois.QuadraticFrobeniusPatching.Local
import Langlands.Galois.QuadraticFrobeniusPatching.Polynomial
import Langlands.ClassField.Global.IdeleGaloisDescentProof
import Langlands.Global.AdelicFunctoriality.GaloisPlaceCount

/-! # Transport of Euler polynomial matching among number fields -/

noncomputable section

universe u

namespace Langlands.GaloisRepresentation.QuadraticFrobeniusPatching

open Polynomial Filter IsDedekindDomain Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped NumberField Valued FiniteExtension

section Extension

variable {K E C : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E] [Field C] [TopologicalSpace C]
  (v : FinitePlace K) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]

private theorem residueCardinality_eq_pow :
    residueCardinality w = residueCardinality v ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  let := w.isPrime
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm

private theorem completionMap_norm_le_one_iff (x : FiniteCompletion K v) :
    ‖completionMap v w x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  simpa only [Valued.toNormedField.norm_le_one_iff,
    HeightOneSpectrum.mem_adicCompletionIntegers] using completionMap_mem_integers_iff v w x

private theorem completionMap_isAlgebraic :
    letI : Algebra (FiniteCompletion K v) (FiniteCompletion E w) :=
      (completionMap v w).toAlgebra
    Algebra.IsAlgebraic (FiniteCompletion K v) (FiniteCompletion E w) := by
  let := local_finite v w
  infer_instance

/-- Restriction along a number-field extension raises the eigenvalues of
geometric Frobenius to the residue degree at the chosen place. -/
theorem hasEulerPolynomialAt_pullback_pow [IsAlgClosed C] {A : Objects K C} {Q : C[X]}
    (hQ : Q.natDegree = A.val.rank) (hA : HasEulerPolynomialAt A v Q.reverse) :
    HasEulerPolynomialAt (pullback (algebraMap K E) A) w
      (frobeniusRootPower (w.asIdeal.inertiaDeg (𝓞 K)) Q).reverse := by
  obtain ⟨hur, b, hb, hpoly⟩ := hA
  have hchar : characteristicPolynomial (atFinitePlace v A) b = Q :=
    eq_of_reverse_eq_of_natDegree_eq
      ((characteristicPolynomial_natDegree (atFinitePlace v A) b).trans hQ.symm) hpoly
  have hur' := isUnramifiedAt_pullback (completionMap v w) (algebraMap K E)
    (completionMap_coe v w) (completionMap_norm_le_one_iff v w)
    (completionMap_isAlgebraic v w) hur
  let a := geometricFrobeniusLift w
  have ha : IsGeometricFrobeniusLift w a := geometricFrobeniusLift_spec w
  refine ⟨hur', a, ha, ?_⟩
  rw [eulerPolynomial_pullback_pow (completionMap v w) (algebraMap K E)
    (completionMap_coe v w) (completionMap_norm_le_one_iff v w)
    (completionMap_isAlgebraic v w) hur _ (residueCardinality_eq_pow v w) ha hb]
  rw [eulerPolynomial, characteristicPolynomial, map_pow, charpoly_pow]
  exact congrArg (fun P : C[X] => (frobeniusRootPower (w.asIdeal.inertiaDeg (𝓞 K)) P).reverse)
    hchar

/-- Complete splitting makes the local restriction sufficient to detect both
unramifiedness and the specified Euler polynomial. -/
theorem hasEulerPolynomialAt_of_splitsCompletely {A : Objects K C} {Q : C[X]}
    (hs : SplitsCompletelyAt (N := E) v)
    (hA : HasEulerPolynomialAt (pullback (algebraMap K E) A) w Q) :
    HasEulerPolynomialAt A v Q := by
  have hdeg := hs w inferInstance
  have hres := Nat.eq_one_of_mul_eq_one_left ((localDegree_eq v w).symm.trans hdeg)
  have hcard : residueCardinality w = residueCardinality v := by
    rw [residueCardinality_eq_pow v w, hres, pow_one]
  exact hasEulerPolynomialAt_of_local_surjective (completionMap v w) (algebraMap K E)
    (completionMap_coe v w) (completionMap_norm_le_one_iff v w)
    (completionMap_isAlgebraic v w)
    (Module.Free.bijective_algebraMap_of_finrank_eq_one hdeg).2 hcard hA

end Extension

section BaseChange

variable {F K E C : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
  [Field E] [NumberField E] [Field C] [TopologicalSpace C]
  [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]

/-- A cofinite set of matching places for one auxiliary representation yields
a cofinite set after extension, with exponent given by the whole tower. -/
theorem eventually_hasEulerPolynomialAt_pullback [IsAlgClosed C] {A : Objects K C}
    {P : FinitePlace F → C[X]} (hdeg : ∀ v, (P v).natDegree = A.val.rank)
    (hA : ∀ᶠ v in cofinite, ∀ w : FinitePlacesAbove K v,
      HasEulerPolynomialAt A w.val
        (frobeniusRootPower (w.val.asIdeal.inertiaDeg (𝓞 F)) (P v)).reverse) :
    ∀ᶠ z : FinitePlace E in cofinite, HasEulerPolynomialAt (pullback (algebraMap K E) A) z
      (frobeniusRootPower (z.asIdeal.inertiaDeg (𝓞 F)) (P (z.under (𝓞 F)))).reverse := by
  filter_upwards [(tendsto_under_cofinite (K := F) (L := E)).eventually hA] with z hz
  let w := z.under (𝓞 K)
  let v := z.under (𝓞 F)
  have hw : w.under (𝓞 F) = v :=
    HeightOneSpectrum.ext (Ideal.under_under (B := 𝓞 K) z.asIdeal)
  have hwv : w.asIdeal.LiesOver v.asIdeal := hw ▸ liesOver_under w
  have hh := hz ⟨w, hwv⟩
  have hd := (frobeniusRootPower_natDegree (w.asIdeal.inertiaDeg (𝓞 F)) (P v)).trans (hdeg v)
  have h := hasEulerPolynomialAt_pullback_pow w z hd hh
  rw [frobeniusRootPower_mul, ← Ideal.inertiaDeg_tower (R := 𝓞 F) w.asIdeal z.asIdeal] at h
  exact h

end BaseChange

section Automorphism

variable {F K : Type u} {C : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [Field C] [TopologicalSpace C] {A : Objects K C}

private theorem hasEulerPolynomialAt_pullback_aut (σ : K ≃ₐ[F] K)
    (v : FinitePlace F) (w : FinitePlacesAbove K v) {Q : C[X]}
    (hA : HasEulerPolynomialAt A (finitePlaceEquiv σ.toRingEquiv w.val) Q) :
    HasEulerPolynomialAt (pullback σ.toRingEquiv.toRingHom A) w.val Q := by
  let w' := finitePlaceEquiv σ.toRingEquiv w.val
  let g := finiteCompletionEquiv σ.toRingEquiv w.val
  let : w'.asIdeal.LiesOver v.asIdeal :=
    Langlands.ClassField.Global.IdeleGaloisDescentProof.liesOver_finitePlaceEquiv σ v w.val
  have hcard : residueCardinality w.val = residueCardinality w' := by
    rw [residueCardinality_eq_pow v w.val, residueCardinality_eq_pow v w']
    simp only [w', inertiaDeg_finitePlaceEquiv_algEquiv]
  have hg (x : FiniteCompletion K w') : ‖g x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
    simpa only [Valued.toNormedField.norm_le_one_iff,
      HeightOneSpectrum.mem_adicCompletionIntegers] using
      finiteCompletionEquiv_integral σ.toRingEquiv w.val x
  have halg := isAlgebraic_of_surjective g.toRingHom g.surjective
  obtain ⟨hur, b, hb, hQ⟩ := hA
  let a := geometricFrobeniusLift w.val
  have ha : IsGeometricFrobeniusLift w.val a := geometricFrobeniusLift_spec w.val
  refine ⟨isUnramifiedAt_pullback g.toRingHom σ.toRingEquiv.toRingHom
    (finiteCompletionEquiv_coe σ.toRingEquiv w.val) hg halg hur, a, ha, ?_⟩
  have h := eulerPolynomial_pullback_pow g.toRingHom σ.toRingEquiv.toRingHom
    (finiteCompletionEquiv_coe σ.toRingEquiv w.val) hg halg hur 1
    (by simpa only [pow_one] using hcard) ha hb
  simpa only [pow_one, hQ] using h

/-- A relative automorphism preserves the residue degree in the matching formula
and transports the Euler polynomial from the corresponding finite place. -/
theorem eventually_hasEulerPolynomialAt_pullback_aut (σ : K ≃ₐ[F] K)
    {P : FinitePlace F → C[X]}
    (hA : ∀ᶠ v in cofinite, ∀ w : FinitePlacesAbove K v,
      HasEulerPolynomialAt A w.val
        (frobeniusRootPower (w.val.asIdeal.inertiaDeg (𝓞 F)) (P v)).reverse) :
    ∀ᶠ w : FinitePlace K in cofinite, HasEulerPolynomialAt
      (pullback σ.toRingEquiv.toRingHom A) w
      (frobeniusRootPower (w.asIdeal.inertiaDeg (𝓞 F)) (P (w.under (𝓞 F)))).reverse := by
  filter_upwards [(tendsto_under_cofinite (K := F) (L := K)).eventually hA] with w hw
  let v := w.under (𝓞 F)
  let w' : FinitePlacesAbove K v := ⟨finitePlaceEquiv σ.toRingEquiv w,
    Langlands.ClassField.Global.IdeleGaloisDescentProof.liesOver_finitePlaceEquiv σ v w⟩
  apply hasEulerPolynomialAt_pullback_aut σ v ⟨w, liesOver_under w⟩
  simpa only [w', inertiaDeg_finitePlaceEquiv_algEquiv] using hw w'

end Automorphism

end Langlands.GaloisRepresentation.QuadraticFrobeniusPatching
