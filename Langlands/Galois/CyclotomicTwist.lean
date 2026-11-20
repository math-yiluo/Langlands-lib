import Langlands.Galois.CyclotomicFrobenius
import Langlands.Global.Arithmetic.HenniartCompletionConjugation
import Langlands.Weil.Representation.Twist
import Mathlib.Topology.Algebra.Group.ZPow

/-! # Integral cyclotomic twists of actual Galois representations -/

noncomputable section

namespace Langlands.GaloisRepresentation

open Langlands.Global Polynomial
open scoped Valued

universe uK uL uV uW

variable {K : Type uK} [Field K] {L : Type uL} [Field L] [TopologicalSpace L]

section Twist

variable (χ : Field.absoluteGaloisGroup K →* Lˣ)
variable (hχ : Continuous fun g => (χ g : L))
variable (A : Objects.{uK, uL, uV} K L)

/-- Twist a continuous action on its actual carrier by a continuous unit character. -/
def twist [IsTopologicalRing L] : Objects.{uK, uL, uV} K L := by
  refine ⟨FiniteRepresentation.twist χ A.val, ?_⟩
  let : TopologicalSpace (Module.End L A.val) := moduleTopology L (Module.End L A.val)
  let : IsModuleTopology L (Module.End L A.val) := ⟨rfl⟩
  change Continuous (fun g => (χ g : L) • A.val.representation g)
  exact hχ.smul A.property

theorem twist_action [IsTopologicalRing L] (g : Field.absoluteGaloisGroup K) :
    (twist χ hχ A).val.representation g = (χ g : L) • A.val.representation g := rfl

/-- Cancel a common twist on an actual invertible intertwiner. -/
def untwistEquiv [IsTopologicalRing L] {B : Objects.{uK, uL, uW} K L}
    (e : FiniteRepresentation.Equiv (twist χ hχ A).val (twist χ hχ B).val) :
    FiniteRepresentation.Equiv A.val B.val where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' := (Langlands.untwistIntertwining χ e.toIntertwiningMap).isIntertwining'

/-- The Euler polynomial of the twist is obtained by scaling its variable. -/
theorem eulerPolynomial_twist [IsTopologicalRing L] (g : Field.absoluteGaloisGroup K) :
    eulerPolynomial (twist χ hχ A) g =
      (eulerPolynomial A g).comp (C (χ g : L) * X) := by
  classical
  let b := Module.finBasis L A.val
  let s := (χ g : L)
  let f := compRingHom (C s * X)
  have hmatrix :
      LinearMap.toMatrix b b ((twist χ hχ A).val.representation g) =
        s • LinearMap.toMatrix b b (A.val.representation g) := by
    change LinearMap.toMatrix b b (s • A.val.representation g) = _
    exact map_smul (LinearMap.toMatrix b b) s (A.val.representation g)
  refine (eulerPolynomial_eq_det (twist χ hχ A) b g).trans ?_
  refine (congrArg (fun M : Matrix (Fin (Module.finrank L A.val)) (Fin (Module.finrank L A.val)) L =>
    Matrix.det (1 - (X : L[X]) • M.map C)) hmatrix).trans ?_
  rw [eulerPolynomial_eq_det A b g]
  change _ = f (Matrix.det _)
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, map_one, map_sub, smul_eq_mul, map_mul, f, coe_compRingHom_apply,
    C_comp, X_comp]
  ring

variable [NumberField K]

/-- Cancel the common character after restriction to the actual completion. -/
def untwistAtFinitePlaceEquiv [IsTopologicalRing L] {B : Objects.{uK, uL, uW} K L}
    (v : FinitePlace K) (e : FiniteRepresentation.Equiv
      (atFinitePlace v (twist χ hχ A)).val (atFinitePlace v (twist χ hχ B)).val) :
    FiniteRepresentation.Equiv (atFinitePlace v A).val (atFinitePlace v B).val := by
  let res := Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding (K := K) v)
  exact untwistEquiv (χ.comp res.toMonoidHom) (hχ.comp res.continuous) (atFinitePlace v A) e

/-- At a place where both actions are trivial on inertia, the twist is unramified. -/
theorem isUnramifiedAt_twist [IsTopologicalRing L] {v : FinitePlace K} (hA : IsUnramifiedAt A v)
    (hI : ∀ i : localInertia v,
      χ (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) i.val) = 1) :
    IsUnramifiedAt (twist χ hχ A) v := by
  intro i
  change (χ (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) i.val) : L) •
    (atFinitePlace v A).val.representation i.val = 1
  rw [hI, Units.val_one, one_smul, hA]

end Twist

section CyclotomicPower

variable (p : ℕ) [Fact p.Prime] (φ : ℚ_[p] →+* L)
variable (K)

/-- The inverse cyclotomic character to an integral power, with coefficients
    transported from the p-adic numbers. -/
def geometricCyclotomicPower (k : ℤ) : Field.absoluteGaloisGroup K →* Lˣ :=
  (Units.map (φ.comp (PadicInt.Coe.ringHom (p := p))).toMonoidHom).comp
    ((zpowGroupHom k).comp (invMonoidHom.comp (absoluteCyclotomicCharacter p K)))

theorem continuous_geometricCyclotomicPower (hφ : Continuous φ) (k : ℤ) :
    Continuous fun g => (geometricCyclotomicPower K p φ k g : L) := by
  change Continuous fun g =>
    φ (((((absoluteCyclotomicCharacter p K g)⁻¹ : ℤ_[p]ˣ) ^ k).val : ℤ_[p]) : ℚ_[p])
  have hcoe : Continuous (fun x : ℤ_[p] => (x : ℚ_[p])) := continuous_subtype_val
  exact hφ.comp (hcoe.comp
    (Units.continuous_val.comp ((continuous_absoluteCyclotomicCharacter p K).inv.zpow k)))

variable {K} [NumberField K]

omit [TopologicalSpace L] in
theorem geometricCyclotomicPower_inertia {v : FinitePlace K} (hchar : residueCharacteristic v ≠ p)
    (i : localInertia v) (k : ℤ) :
    geometricCyclotomicPower K p φ k
      (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) i.val) = 1 := by
  let : CharZero (FiniteCompletion K v) :=
    Algebra.charZero_of_charZero K (FiniteCompletion K v)
  simp [geometricCyclotomicPower, absoluteCyclotomicCharacter_map,
    absoluteCyclotomicCharacter_inertia p v hchar i]

omit [TopologicalSpace L] in
theorem geometricCyclotomicPower_frobenius {v : FinitePlace K}
    (hchar : residueCharacteristic v ≠ p) {g : LocalGroup v}
    (hg : IsGeometricFrobeniusLift v g) (k : ℤ) :
    (geometricCyclotomicPower K p φ k
      (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) g) : L) =
      (residueCardinality v : L) ^ k := by
  let : CharZero (FiniteCompletion K v) :=
    Algebra.charZero_of_charZero K (FiniteCompletion K v)
  let f := φ.comp (PadicInt.Coe.ringHom (p := p))
  let c := absoluteCyclotomicCharacter p K
  let res := Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding (K := K) v)
  change (Units.map f.toMonoidHom ((c (res g))⁻¹ ^ k) : L) = _
  rw [← map_inv c, ← map_inv res, absoluteCyclotomicCharacter_map, map_zpow,
    Units.val_zpow_eq_zpow_val]
  congr 1
  change f _ = _
  rw [absoluteCyclotomicCharacter_geometricFrobenius_inv p v hchar hg, map_natCast]

/-- Twisting by the inverse cyclotomic character to power `k` scales
    the unramified geometric Euler variable by `q ^ k`. -/
theorem HasEulerPolynomialAt.geometricCyclotomicTwist [IsTopologicalRing L]
    {A : Objects.{uK, uL, uV} K L} {v : FinitePlace K} {P : L[X]}
    (hA : HasEulerPolynomialAt A v P) (hφ : Continuous φ) (k : ℤ)
    (hchar : residueCharacteristic v ≠ p) :
    HasEulerPolynomialAt (twist (geometricCyclotomicPower K p φ k)
      (continuous_geometricCyclotomicPower K p φ hφ k) A) v
      (P.comp (C ((residueCardinality v : L) ^ k) * X)) := by
  obtain ⟨hI, g, hg, hP⟩ := hA
  refine ⟨isUnramifiedAt_twist _ _ _ hI (fun i => geometricCyclotomicPower_inertia p φ hchar i k),
    g, hg, ?_⟩
  rw [atFinitePlace, eulerPolynomial_pullback, eulerPolynomial_twist,
    geometricCyclotomicPower_frobenius p φ hchar hg k]
  change (eulerPolynomial (atFinitePlace v A) g).comp _ = _
  rw [hP]

end CyclotomicPower

section CoefficientCompletion

variable {F : Type uL} [Field F] [NumberField F]

/-- The residue prime used for the p-adic completion map is the characteristic
    of the residue field used for compatible families. -/
theorem residueCharacteristic_eq_residuePrime (lam : FinitePlace F) :
    residueCharacteristic lam = CompletionPadic.residuePrime lam := by
  let : Fact (residueCharacteristic lam).Prime :=
    ⟨CharP.prime_ringChar (NumberField.RingOfIntegers F ⧸ lam.asIdeal)⟩
  symm
  apply residuePrime_eq_of_natCast_mem
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero (NumberField.RingOfIntegers F ⧸ lam.asIdeal) (residueCharacteristic lam)

/-- The integral inverse cyclotomic twist over the actual coefficient completion. -/
def cyclotomicTwist (lam : FinitePlace F) (k : ℤ)
    (A : LambdaAdic.{uK, uL, uV} K F lam) : LambdaAdic.{uK, uL, uV} K F lam :=
  twist (geometricCyclotomicPower K _ (CompletionPadic.padicMap lam) k)
    (continuous_geometricCyclotomicPower K _ _ (CompletionPadic.continuous_padicMap lam) k) A

variable [NumberField K]

theorem HasEulerPolynomialAt.cyclotomicTwist {lam : FinitePlace F}
    {A : LambdaAdic.{uK, uL, uV} K F lam} {v : FinitePlace K}
    {P : (FiniteCompletion F lam)[X]} (hA : HasEulerPolynomialAt A v P)
    (k : ℤ) (hchar : residueCharacteristic v ≠ residueCharacteristic lam) :
    HasEulerPolynomialAt (cyclotomicTwist lam k A) v
      (P.comp (C ((residueCardinality v : FiniteCompletion F lam) ^ k) * X)) :=
  HasEulerPolynomialAt.geometricCyclotomicTwist _ _ hA (CompletionPadic.continuous_padicMap lam) k
    (by rwa [← residueCharacteristic_eq_residuePrime lam])

end CoefficientCompletion
end Langlands.GaloisRepresentation
