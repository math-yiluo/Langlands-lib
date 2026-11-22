import Langlands.Global.AdelicEisensteinCompactContinuationComparison
import Langlands.Global.AdelicLeadingCuspidalPairing
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Global.AdelicStandardConstantTermTwist

/-! # Scalar continuation of the norm-one tests of the continued inducing expression -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold BigOperators

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Analysis.Meromorphic
  Langlands.Automorphic.GroupSchemeFunctions

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (P J : StandardIndex F G fam.i fam.ν)
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))

local notation "Y" => (AdelicGroupPoints F G → ℂ)
local notation "Test" => (AdelicGroupPoints F (fam.M J) → ℂ)
local notation "Aut" => fam.IsAutomorphicOn hsmooth Kinf rho P
local notation "Projection" => fam.IsCuspidalProjection hsmooth Kinf rho J

/-- Finite linearity of the tested nested constant term, with absolute
integrability of the finitely many pairings. -/
theorem leviPairing_constantTerm_sum_smul {k : ℕ} (hJP : J ≤ P)
    (psi : Fin k → Y) (hpsi : ∀ i, Aut (psi i)) (c : Fin k → ℂ)
    (test : Test) (hint : ∀ i, fam.constantTerm J (psi i) ∈ fam.leviPairingDomain J test)
    (g : AdelicGroupPoints F G) :
    fam.leviPairing J (fam.constantTerm J (∑ i, c i • psi i)) g test =
      ∑ i, c i * fam.leviPairing J (fam.constantTerm J (psi i)) g test := by
  let f (i : Fin k) : automorphicFunctionsOn
      (parabolicQuotientSubgroup F (fam.p P) (fam.iU P) (fam.l P)) Kinf rho hsmooth
      (adelicDifferentialCommutator_of_smooth F G hsmooth) := ⟨psi i, hpsi i⟩
  let v (i : Fin k) : fam.leviPairingDomain J test := ⟨fam.constantTerm J (psi i), hint i⟩
  let C := fam.constantTermLinear P J hsmooth Kinf rho hJP
  let L := fam.leviPairingLinear J test
  have hsum : fam.constantTerm J (∑ i, c i • psi i) = (∑ i, c i • v i).val := by
    calc
      _ = C (∑ i, c i • f i) := by
        change fam.constantTerm J _ = fam.constantTerm J (∑ i, c i • f i).val
        simp only [Submodule.coe_sum, Submodule.coe_smul, f]
      _ = (∑ i, c i • v i).val := by
        simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
        rfl
  rw [hsum]
  change L (∑ i, c i • v i) g = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/-- In the nested tested constant term, a common parameter twist
distributes over a finite linear combination of inducing functions. -/
theorem leviPairing_parabolicConstantTerm_twist_sum_smul {k : ℕ}
    [IsClosedImmersion (fam.p P).hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p P) K) (lam : ComplexCharacterParameter F (fam.P P))
    (psi : Fin k → Y) (hpsi : ∀ i, Aut (psi i)) (c : Fin k → ℂ)
    (test : Test) (hint : J ≤ P → ∀ i, fam.constantTerm J (psi i) ∈ fam.leviPairingDomain J test)
    (g : AdelicGroupPoints F G) :
    fam.leviPairing J (fam.parabolicConstantTerm P J (hK.parameterTwist (∑ i, c i • psi i) lam)) g test =
      ∑ i, c i * fam.leviPairing J (fam.parabolicConstantTerm P J (hK.parameterTwist (psi i) lam)) g test := by
  classical
  by_cases hJP : J ≤ P
  · simp only [parabolicConstantTerm, ite_eq_left hJP,
      fam.leviPairing_constantTerm_parameterTwist P J hK hJP,
      fam.leviPairing_constantTerm_sum_smul P J rho hsmooth Kinf hJP psi hpsi c test (hint hJP),
      Finset.sum_mul, mul_assoc]
  · have hz : fam.leviPairing J 0 g test = 0 :=
      congrFun (map_zero (fam.leviPairingLinear J test)) g
    simp only [parabolicConstantTerm, ite_eq_right hJP, hz, mul_zero, Finset.sum_const_zero]

end StandardParabolicFamily

/-- On an open dense chart domain, testing the nested constant term of the
twist of a finite meromorphic combination of inducing forms gives a
scalar meromorphic function. The test is zero outside the range of
standard parabolics contained in the inducing parabolic. -/
def EisensteinInducingPairingContinuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (P J : StandardIndex F G fam.i fam.ν)
    [IsClosedImmersion (fam.p P).hom.hom.left]
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p P) K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    {n k : ℕ} (b : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F (fam.P P))
    (D : Set (Fin n → ℂ)) (psi : Fin k → AdelicGroupPoints F G → ℂ)
    (coeff : Fin k → (Fin n → ℂ) → ℂ),
    IsOpen D → Dense D →
    (∀ i, fam.IsAutomorphicOn hsmooth Kinf rho P (psi i)) →
    (J ≤ P → ∀ i, ∃ c, fam.IsCuspidalProjection hsmooth Kinf rho J
      (fam.constantTerm J (psi i)) c) →
    (∀ i, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (coeff i) D) →
    ∀ test : AdelicGroupPoints F (fam.M J) → ℂ, fam.IsLeviCuspForm Kinf rho J test →
      ∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun t =>
        fam.leviPairing J (fam.parabolicConstantTerm P J
          (hK.parameterTwist (∑ i, coeff i t • psi i) (b t))) g test) D

theorem eisensteinInducingPairingContinuation : EisensteinInducingPairingContinuationStatement.{u} := by
  classical
  intro F _ _ G _ _ _ fam P J _ K hK N d rho hsmooth Kinf n k b D psi coeff ho hd
    hpsi hProject hcoeff test htest g
  by_cases hJP : J ≤ P
  · have hint (i : Fin k) : fam.constantTerm J (psi i) ∈ fam.leviPairingDomain J test := by
      obtain ⟨v, hv⟩ := hProject hJP i
      exact fun x => (hv.2.2 test htest x).1
    let a (i : Fin k) (t : Fin n → ℂ) :=
      coeff i t * fam.leviPairing J (fam.constantTerm J (psi i)) g test
    have hTerm (i : Fin k) : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (a i) D := by
      have hconst := isMeromorphicOn_const (E := Fin n → ℂ)
        (fam.leviPairing J (fam.constantTerm J (psi i)) g test)
      have hm := (hcoeff i).mul hconst
      rw [Set.inter_univ] at hm
      exact hm
    have hsum := IsMeromorphicOn.sum Finset.univ ho hd (fun i _ => hTerm i)
    have hheight := isMeromorphicOn_exp_parameterPairing b (hK.height g) ho hd
    have hmul := hsum.mul hheight
    rw [Set.inter_self] at hmul
    convert hmul using 1
    funext t
    simp only [StandardParabolicFamily.parabolicConstantTerm, ite_eq_left hJP,
      fam.leviPairing_constantTerm_parameterTwist P J hK hJP,
      fam.leviPairing_constantTerm_sum_smul P J rho hsmooth Kinf hJP psi hpsi _ test hint,
      Pi.mul_apply, Finset.sum_apply, a, IsIwasawaCompact.heightPower]
  · have hz : fam.leviPairing J 0 g test = 0 :=
      congrFun (map_zero (fam.leviPairingLinear J test)) g
    simp only [StandardParabolicFamily.parabolicConstantTerm, ite_eq_right hJP, hz]
    exact (isMeromorphicOn_const 0).restrict_domain ho hd (Set.subset_univ D)

end Langlands.Global
