import Langlands.AbelianScheme.Tate.PrimeScalars
import Langlands.AbelianScheme.Tate.GeometricAdelicRankStatement
import Langlands.AbelianScheme.Tate.GeometricPrimeAdicRankProof
import Langlands.AbelianScheme.Tate.PrimeComparisonProof
import Langlands.Global.ProfiniteIntegerPadicProductComparisonProof
import Langlands.Global.ProfiniteIntegerCompletionComparisonProof
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Geometric full and away Tate modules are free of rank `2 * g` -/

set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.TateAdelicRank

local instance primeFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

open Langlands.Global

def fullScalarCoordinates :
    ProfiniteIntegerRing →+* ((p : Nat.Primes) → PadicInt p.val) :=
  RingHom.pi fun p => ProfiniteIntegerRing.toPadic p.val

theorem fullScalarCoordinates_bijective : Function.Bijective fullScalarCoordinates := by
  obtain ⟨e, he, _, hz⟩ := profiniteIntegerPadicProductComparison
  have hc : Continuous fullScalarCoordinates :=
    continuous_pi fun p => ProfiniteIntegerRing.continuous_toPadic p.val
  have h : (e : ProfiniteIntegerRing → _) = fullScalarCoordinates := by
    apply residue_integer_dense.equalizer he hc
    funext z p
    exact (hz z p).trans (ProfiniteIntegerRing.toPadic_intCast p.val z).symm
  rw [← h]
  exact e.bijective

def fullScalarEquiv :
    ProfiniteIntegerRing ≃+* ((p : Nat.Primes) → PadicInt p.val) :=
  RingEquiv.ofBijective fullScalarCoordinates fullScalarCoordinates_bijective

abbrev AwayPrime (m : ℕ) := {p : Nat.Primes // Nat.Coprime p.val m}

def awayScalarCoordinates (m : ℕ) :
    PrimeToProfiniteIntegerRing m →+* ((p : AwayPrime m) → PadicInt p.val.val) :=
  RingHom.pi fun p => PrimeToProfiniteIntegerRing.toPadic p.val.val m p.property

theorem awayScalarCoordinates_injective (m : ℕ) :
    Function.Injective (awayScalarCoordinates m) := by
  intro x y hxy
  ext n
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (PrimeToProfiniteIntegerRing.reduction n x)
  obtain ⟨w, hw⟩ := ZMod.intCast_surjective (PrimeToProfiniteIntegerRing.reduction n y)
  change PrimeToProfiniteIntegerRing.reduction n x = PrimeToProfiniteIntegerRing.reduction n y
  rw [← hz, ← hw, ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natCast_dvd]
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hpk
  let : Fact p.Prime := ⟨hp⟩
  by_cases hk : k = 0
  · simp [hk]
  have hpm : Nat.Coprime p m := n.property.of_dvd_left
    (dvd_trans (dvd_pow_self p hk) hpk)
  let q : AwayPrime m := ⟨⟨p, hp⟩, hpm⟩
  have he := congrArg (PadicInt.toZModPow k) (congrFun hxy q)
  have hred (a : PrimeToProfiniteIntegerRing m) (t : ℤ)
      (ht : (t : ZMod (n.val : ℕ)) = PrimeToProfiniteIntegerRing.reduction n a) :
      PadicInt.toZModPow k (PrimeToProfiniteIntegerRing.toPadic p m hpm a) =
        (t : ZMod (p ^ k)) := by
    rw [PrimeToProfiniteIntegerRing.toZModPow_toPadic,
      ← ResidueLimit.compatible a (PrimeToProfiniteIntegerRing.primePowerModulus p m hpm k) n hpk,
      ← ht]
    exact ResidueLimit.transition_intCast hpk t
  change PadicInt.toZModPow k (PrimeToProfiniteIntegerRing.toPadic p m hpm x) =
    PadicInt.toZModPow k (PrimeToProfiniteIntegerRing.toPadic p m hpm y) at he
  rw [hred x z hz, hred y w hw, ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natCast_dvd] at he
  exact he

theorem awayScalarCoordinates_surjective (m : ℕ) :
    Function.Surjective (awayScalarCoordinates m) := by
  classical
  intro y
  let z : (p : Nat.Primes) → PadicInt p.val :=
    fun p => if h : Nat.Coprime p.val m then y ⟨p, h⟩ else 0
  obtain ⟨x, hx⟩ := fullScalarCoordinates_bijective.surjective z
  refine ⟨PrimeToProfiniteIntegerRing.restrict m x, ?_⟩
  funext p
  change PrimeToProfiniteIntegerRing.toPadic p.val.val m p.property
    (PrimeToProfiniteIntegerRing.restrict m x) = y p
  rw [PrimeToProfiniteIntegerRing.toPadic_restrict]
  apply (congrFun hx p.val).trans
  dsimp only [z]
  rw [dite_eq_left p.property]

def awayScalarEquiv (m : ℕ) :
    PrimeToProfiniteIntegerRing m ≃+* ((p : AwayPrime m) → PadicInt p.val.val) :=
  RingEquiv.ofBijective (awayScalarCoordinates m)
    ⟨awayScalarCoordinates_injective m, awayScalarCoordinates_surjective m⟩

section Coordinates

open Langlands.GroupScheme.Tate
open Langlands.GroupScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
variable (p : ℕ) [Fact p.Prime]

theorem fullToPrime_smul (a : ProfiniteIntegerRing) (x : Full G T) :
    fullToPrime G T p (a • x) =
      ProfiniteIntegerRing.toPadic p a • fullToPrime G T p x :=
  Langlands.GroupScheme.Tate.PrimeComparison.fullToPrime_smul G T p a x

theorem awayToPrime_smul (m : ℕ) (h : Nat.Coprime p m)
    (a : PrimeToProfiniteIntegerRing m) (x : Away G T m) :
    awayToPrime G T p m h (a • x) =
      PrimeToProfiniteIntegerRing.toPadic p m h a • awayToPrime G T p m h x :=
  Langlands.GroupScheme.Tate.PrimeComparison.awayToPrime_smul G T p m h a x

end Coordinates

section Assembly

variable {R : Type*} [CommRing R] {J : Type*}
  {Rp : J → Type*} [∀ p, CommRing (Rp p)]
  {Mp : J → Type*} [∀ p, AddCommGroup (Mp p)] [∀ p, Module (Rp p) (Mp p)]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- Assemble finite free prime coordinates over their actual product scalar ring. -/
def assemble (r : ℕ) (c : R ≃+* ((p : J) → Rp p))
    (t : M ≃+ ((p : J) → Mp p))
    (ht : ∀ a x p, t (a • x) p = c a p • t x p)
    (b : ∀ p, (Fin r → Rp p) ≃ₗ[Rp p] Mp p) :
    (Fin r → R) ≃ₗ[R] M := by
  let d : (Fin r → R) ≃+ ((p : J) → Fin r → Rp p) :=
    { toFun := fun x p i => c (x i) p
      invFun := fun x i => c.symm (fun p => x p i)
      left_inv := by intro x; funext i; exact c.symm_apply_apply (x i)
      right_inv := by
        intro x
        funext p i
        exact congrFun (c.apply_symm_apply (fun p => x p i)) p
      map_add' := by
        intro x y
        funext p i
        exact congrFun (c.map_add (x i) (y i)) p }
  let e := d.trans ((AddEquiv.piCongrRight (fun p => (b p).toAddEquiv)).trans t.symm)
  have he (x : Fin r → R) (p : J) : t (e x) p = b p (fun i => c (x i) p) := by
    exact congrFun (t.apply_symm_apply _) p
  exact
    { e with
      map_smul' := by
        intro a x
        apply t.injective
        funext p
        change t (e (a • x)) p = t (a • e x) p
        rw [he, ht, he, ← map_smul]
        congr 1
        funext i
        exact congrFun (c.map_mul a (x i)) p }

end Assembly

section IntegralFree

open Langlands.GroupScheme.Tate
open Langlands.GroupScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- Assemble the actual prime-power bases without assuming linearity of the comparison. -/
def fullFree (r : ℕ)
    (b : ∀ p : Nat.Primes,
      (Fin r → PadicInt p.val) ≃ₗ[PadicInt p.val] PrimeAdic.Integral G T p.val) :
    (Fin r → ProfiniteIntegerRing) ≃ₗ[ProfiniteIntegerRing] Full G T := by
  let t := (fullPrimeProductComparison G T).choose
  have ht := (fullPrimeProductComparison G T).choose_spec.1
  have he (x : Full G T) : t x = toPrimeProduct G T x := DFunLike.congr_fun ht x
  refine assemble r fullScalarEquiv t ?_ b
  intro a x p
  rw [he, he]
  exact fullToPrime_smul G T p.val a x

def awayFree (m r : ℕ)
    (b : ∀ p : AwayPrime m,
      (Fin r → PadicInt p.val.val) ≃ₗ[PadicInt p.val.val]
        PrimeAdic.Integral G T p.val.val) :
    (Fin r → PrimeToProfiniteIntegerRing m) ≃ₗ[PrimeToProfiniteIntegerRing m]
      Away G T m := by
  let t := (awayPrimeProductComparison G T m).choose
  have ht := (awayPrimeProductComparison G T m).choose_spec.1
  have he (x : Away G T m) : t x = toAwayPrimeProduct G T m x :=
    DFunLike.congr_fun ht x
  refine assemble r (awayScalarEquiv m) t ?_ b
  intro a x p
  rw [he, he]
  exact awayToPrime_smul G T p.val.val m p.property a x

end IntegralFree

section GeometricIntegral

universe u
variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S) (g : ℕ)
  (hdim : A.HasRelativeDimension g)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)

def geometricFullIntegral
    (hunit : ∀ n : ℕ, 0 < n → IsUnit (n : Γ(S, ⊤))) :
    (Fin (2 * g) → ProfiniteIntegerRing) ≃ₗ[ProfiniteIntegerRing]
      Langlands.AbelianScheme.Tate.FullAt A s :=
  fullFree A.toGrp (Over.mk s) (2 * g) fun p =>
    (Langlands.AbelianScheme.Tate.PrimeAdic.geometricPrimeAdicRank S A g hdim
      p.val (hunit p.val p.property.pos) Ω s).1.some

def geometricAwayIntegral (m : ℕ)
    (hunit : ∀ n : ℕ, 0 < n → Nat.Coprime n m → IsUnit (n : Γ(S, ⊤))) :
    (Fin (2 * g) → PrimeToProfiniteIntegerRing m) ≃ₗ[PrimeToProfiniteIntegerRing m]
      Langlands.AbelianScheme.Tate.AwayAt A s m :=
  awayFree A.toGrp (Over.mk s) m (2 * g) fun p =>
    (Langlands.AbelianScheme.Tate.PrimeAdic.geometricPrimeAdicRank S A g hdim
      p.val.val (hunit p.val.val p.val.property.pos p.property) Ω s).1.some

end GeometricIntegral

section RationalFree

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The finite-coordinate tensor equivalence respects the extended residue action. -/
theorem piRight_action (r : ℕ) (a : ℚ ⊗[ℤ] R) (x : ℚ ⊗[ℤ] (Fin r → R)) :
    TensorProduct.piRight ℤ ℚ ℚ (fun _ : Fin r => R)
        (Langlands.TateScalarExtension.action R (Fin r → R) a x) =
      a • TensorProduct.piRight ℤ ℚ ℚ (fun _ : Fin r => R) x := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    induction x using TensorProduct.inductionOn with
    | tmul t x =>
      funext i
      change (q * t) ⊗ₜ[ℤ] (a * x i) = (q ⊗ₜ[ℤ] a) * (t ⊗ₜ[ℤ] x i)
      exact (Algebra.TensorProduct.tmul_mul_tmul q t a (x i)).symm
    | add x y hx hy => simp_all [smul_add]
  | add a b ha hb => simp_all [add_smul]

/-- Rationalize a finite free module using the specified transported action. -/
def rationalFree (r : ℕ) (b : (Fin r → R) ≃ₗ[R] M)
    {C : Type*} [CommRing C] [Algebra ℚ C]
    (c : (ℚ ⊗[ℤ] R) ≃ₐ[ℚ] C) [Module C (ℚ ⊗[ℤ] M)]
    (hc : ∀ a x, a • x = Langlands.TateScalarExtension.action R M (c.symm a) x) :
    (Fin r → C) ≃ₗ[C] (ℚ ⊗[ℤ] M) := by
  let eb := b.symm.toAddEquiv.toIntLinearEquiv.baseChange ℤ ℚ M (Fin r → R)
  let d := TensorProduct.piRight ℤ ℚ ℚ (fun _ : Fin r => R)
  let f := eb.trans (d.trans (LinearEquiv.piCongrRight fun _ => c.toLinearEquiv))
  refine (show (ℚ ⊗[ℤ] M) ≃ₗ[C] (Fin r → C) from
    { f.toAddEquiv with map_smul' := ?_ }).symm
  intro a x
  rw [hc]
  have hbc : eb (Langlands.TateScalarExtension.action R M (c.symm a) x) =
      Langlands.TateScalarExtension.action R (Fin r → R) (c.symm a) (eb x) :=
    Langlands.TateScalarExtension.map_action b.symm.toLinearMap (c.symm a) x
  change (fun i => c (d (eb (Langlands.TateScalarExtension.action R M
    (c.symm a) x)) i)) = a • (fun i => c (d (eb x) i))
  rw [hbc, piRight_action]
  funext i
  change c (c.symm a * d (eb x) i) = a * c (d (eb x) i)
  rw [map_mul, AlgEquiv.apply_symm_apply]

end RationalFree

end Langlands.TateAdelicRank

namespace Langlands.AbelianScheme.Tate

open Langlands.TateAdelicRank

universe u

/-- The actual full and prime-to-modulus Tate modules at geometric points are
free of rank `2 * g` over their specified integral and adelic scalar rings. -/
theorem geometricAdelicRank :
    Langlands.AbelianScheme.Tate.GeometricAdelicRankStatement.{u} := by
  intro S A g hdim
  constructor
  · intro hunit Ω _ _ s
    let b := geometricFullIntegral A g hdim s hunit
    refine ⟨⟨b⟩, ?_⟩
    intro h
    let := Langlands.AbelianScheme.Tate.finiteAdeleModule A (Over.mk s) (fun _ => True) h
    exact ⟨rationalFree (2 * g) b
      (Langlands.Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv h) (fun _ _ => rfl)⟩
  · intro m hunit Ω _ _ s
    let b := geometricAwayIntegral A g hdim s m hunit
    refine ⟨⟨b⟩, ?_⟩
    intro h hAway
    let := Langlands.AbelianScheme.Tate.primeToFiniteAdeleModule A (Over.mk s) hAway
    exact ⟨rationalFree (2 * g) b
      (Langlands.Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv hAway)
      (fun _ _ => rfl)⟩

end Langlands.AbelianScheme.Tate
