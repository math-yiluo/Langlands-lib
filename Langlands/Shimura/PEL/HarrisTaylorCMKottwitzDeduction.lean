import Langlands.Shimura.PEL.HarrisTaylorCMKottwitzTraceComparison
import Langlands.Cohomology.Weights.SeparationProof

/-! # Deduction of Kottwitz's theorem from the Harris CM trace comparison -/

noncomputable section

universe wS wR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Global AdelicFunctoriality
open Langlands.Shimura.CompactOpenLevel Langlands.Shimura.RestrictedLevelColimit
open Langlands.Shimura.SmallLevelGaloisTower
open Langlands.Shimura.IsotypicGaloisAction
open Langlands.Shimura.ContinuousIsotypicGaloisRepresentation
open Langlands.GaloisRepresentation (chosenClosureEmbedding)
open Langlands.Cohomology.Weights

private theorem complexWeightFactor_prod_monic {I : Type*} (q : ℕ) (w : ℤ)
    (s : Finset I) (f : I → Polynomial ℂ) (hm : ∀ i, (f i).Monic) :
    complexWeightFactor q w (∏ i ∈ s, f i) =
      ∏ i ∈ s, complexWeightFactor q w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [complexWeightFactor_one]
  | insert i s hi ih =>
    have hprod := Polynomial.monic_prod_of_monic s f (fun j _ => hm j)
    simp only [Finset.prod_insert hi, complexWeightFactor_mul q w (hm i).ne_zero hprod.ne_zero, ih]

/-- Pure factors of distinct weights are determined by their product. -/
private theorem pureFactors_unique {K : Type} [Field K] [NumberField K]
    (ι : K →+* ℂ) {d q : ℕ} {w : ℤ} (hq : 1 < q) {P : Polynomial K}
    {Q R : Fin (2 * d + 1) → Polynomial K}
    (hQprod : (∏ i, Q i) = P) (hRprod : (∏ i, R i) = P)
    (hQ : ∀ i, IsPurePolynomial q ((i.val : ℤ) + w) (Q i))
    (hR : ∀ i, IsPurePolynomial q ((i.val : ℤ) + w) (R i)) : Q = R := by
  classical
  funext i
  have recover (f : Fin (2 * d + 1) → Polynomial K) (hprod : (∏ j, f j) = P)
      (hpure : ∀ j, IsPurePolynomial q ((j.val : ℤ) + w) (f j)) :
      complexWeightFactor q ((i.val : ℤ) + w) (P.map ι) = (f i).map ι := by
    rw [← hprod, Polynomial.map_prod,
      complexWeightFactor_prod_monic _ _ _ _ fun j => (hpure j).1.map ι,
      Finset.prod_eq_single i]
    · exact complexWeightFactor_eq_self ((hpure i).1.map ι) ((hpure i).hasComplexRootsOfWeight ι)
    · intro j _ hji
      refine complexWeightFactor_different_weight hq ?_ ((hpure j).hasComplexRootsOfWeight ι)
      intro heq
      exact hji (Fin.ext (by omega))
    · simp
  exact Polynomial.map_injective ι ι.injective ((recover Q hQprod hQ).symm.trans (recover R hRprod hR))

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

variable [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)
  (U : SmallCMLevel D)

set_option hygiene false in
local notation "Φ" => harrisCMSection E (algebraMap L F) τ₀

set_option hygiene false in
local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

set_option hygiene false in
local notation "τλ" =>
  (Module.End.baseChangeHom K (FiniteCompletion K lam.1) V).toMonoidHom.comp πf

set_option hygiene false in
local notation "heckeMultiplicity(" i ")" => cmHarrisLambdaTowerHeckeMultiplicity D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry
  hRigid lam i (FiniteCompletion K lam.1) (τλ) U

set_option hygiene false in
local notation "vθ" => (harrisPlace p₀ θ (Φ C.distinguished)).1

/-- The virtual Frobenius comparison implies the published Kottwitz proposition on the
actual Harris CM tower. -/
def CMHarrisKottwitzDeductionStatement : Prop :=
  CMHarrisKottwitzTraceComparisonStatement.{wS, wR} D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q ρ existence geometry hRigid U →
  CMHarrisKottwitzLambdaAdicStatement.{wS, wR} D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q ρ existence geometry hRigid U

set_option maxHeartbeats 2500000 in
/-- Deduce occurrence, pure factorization and the Euler polynomial from the virtual identity. -/
theorem cmHarrisKottwitzLambdaAdic_of_traceComparison :
    CMHarrisKottwitzDeductionStatement.{wS, wR} D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q ρ existence geometry hRigid U := by
  classical
  intro htrace hdiv hn hρ w hw V _ _ πf hadm hirr
  obtain ⟨a, S, haux, hcharts⟩ := @htrace hdiv hn hρ w hw V _ _ πf hadm hirr
  refine ⟨a, ?_, S, ?_⟩
  · intro ℓ hS hR lam hfix
    obtain ⟨⟨p, v, _, j, H, P, hPm, hPdeg, hFrob, hvirtual⟩, habove⟩ := @haux ℓ hS hR lam
    let ι := j.comp (algebraMap K (FiniteCompletion K lam.1))
    have hoccurs := (weightSeparationStatement K ι (n - 1) (Ideal.absNorm v.1.asIdeal)
      w a P (fun i => (H i).map j) (NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
      hPm hPdeg hvirtual.1 hvirtual.2).1
    have hdim (i : Fin (2 * (n - 1) + 1)) :
        0 < ((H i).map j).natDegree ↔ Nontrivial (heckeMultiplicity(i.val)).V := by
      obtain ⟨hfin, hpoly⟩ := (hFrob i).2 (hfix i.val)
      let _ := hfin
      rw [Polynomial.natDegree_map, ← hpoly, LinearMap.charpoly_natDegree]
      exact Module.finrank_pos_iff
    rw [hoccurs]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i.val, (hdim i).mp hi⟩
    · rintro ⟨i, hi⟩
      by_cases hirange : i ≤ 2 * (n - 1)
      · let k : Fin (2 * (n - 1) + 1) := ⟨i, Nat.lt_succ_of_le hirange⟩
        exact ⟨k, (hdim k).mpr hi⟩
      · exact (not_nontrivial_iff_subsingleton.mpr (habove i (by omega) (hfix i)) hi).elim
  · intro p₀ hp₀ hgood hunr c hlevel πp hcomponent ha
    obtain ⟨hspherical, hchart⟩ := @hcharts p₀ hp₀ hgood hunr c hlevel πp hcomponent ha
    refine ⟨hspherical, ?_⟩
    intro θ s P hP
    obtain ⟨hPm, hPdim⟩ := hP.monic_and_natDegree
    have hPdeg : 0 < P.natDegree := by
      rw [hPdim, KottwitzDual.kottwitzDim]
      refine Finset.prod_pos fun τ _ => Nat.choose_pos ?_
      have hsum := KottwitzDual.cmHodge_add hΦ C.hodgeFunction
        (KottwitzDual.harrisCharts_hodgeFunction_add_conjugate hΦ C) τ
      change KottwitzDual.cmHodge hΦ C.hodgeFunction (τ, false) ≤ n
      omega
    have hv : 1 < Ideal.absNorm (vθ).asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm vθ
    obtain ⟨⟨ℓ₀, lam₀, _, j₀, H₀, _, hvirtual₀⟩, hall⟩ := hchart θ s P hP
    let ι₀ := j₀.comp (algebraMap K (FiniteCompletion K lam₀.1))
    obtain ⟨Pf, ⟨hprod, hPf⟩, _⟩ := (weightSeparationStatement K ι₀ (n - 1)
      (Ideal.absNorm (vθ).asIdeal) w a P (fun i => (H₀ i).map j₀) hv hPm hPdeg
      hvirtual₀.1 hvirtual₀.2).2 ha
    have hpure i := (hPf i).1
    have hunique (Q : Fin (2 * (n - 1) + 1) → Polynomial K) (hQprod : (∏ i, Q i) = P)
        (hQpure : ∀ i, IsPurePolynomial (Ideal.absNorm (vθ).asIdeal) ((i.val : ℤ) + w) (Q i)) :
        Q = Pf :=
      pureFactors_unique ι₀ hv hQprod hprod hQpure hpure
    refine ⟨?_, Pf, ⟨hprod, hpure⟩, hunique, ?_⟩
    · intro ι z hz
      rw [← hprod, Polynomial.map_prod, Polynomial.roots_prod] at hz
      · obtain ⟨i, _, hi⟩ := Multiset.mem_bind.mp hz
        have hsign : ¬ ((-1 : ℤ) ^ i.val * a < 0) := by
          intro hneg
          rw [(hPf i).2.2 hneg, Polynomial.map_one, Polynomial.roots_one] at hi
          exact Multiset.notMem_zero z hi
        refine ⟨i.val, Nat.le_of_lt_succ i.isLt, ?_, (hpure i).2 ι z hi⟩
        rw [neg_one_pow_eq_ite] at hsign
        by_cases he : Even i.val <;> simp [he] at hsign ⊢ <;> omega
      · exact (Polynomial.monic_prod_of_monic _ _ fun i _ => (hpure i).1.map ι).ne_zero
    · intro ℓ hS hR lam hl i hi hfix hcont hfinite
      obtain ⟨j, H, hFrob, hvirtual⟩ := @hall ℓ hS hR lam hl
      let f := algebraMap K (FiniteCompletion K lam.1)
      let ι := j.comp f
      obtain ⟨Q, ⟨hQprod, hQ⟩, _⟩ := (weightSeparationStatement K ι (n - 1)
        (Ideal.absNorm (vθ).asIdeal) w a P (fun i => (H i).map j) hv hPm hPdeg
        hvirtual.1 hvirtual.2).2 ha
      have hQeq : Q = Pf := hunique Q hQprod (fun k => (hQ k).1)
      subst Q
      let k : Fin (2 * (n - 1) + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
      have hlocal : H k = ((Pf k) ^ a.natAbs).map f := by
        apply Polynomial.map_injective j j.injective
        simpa only [Polynomial.map_map, Polynomial.map_pow] using (hQ k).2.1
      have ⟨hu, hcomp⟩ := hFrob k
      obtain ⟨_, hchar⟩ := hcomp hfix
      have hEuler := hasEulerPolynomialAt_cmHarrisLambdaHeckeMultiplicityObjects D C preservation
        composition unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry hRigid
        lam i (FiniteCompletion K lam.1) continuous_id hfix U hcont (τλ)
        (chosenClosureEmbedding (NumberField.FinitePlace.embedding (K := F) vθ)) hu
      rw [hchar, hlocal] at hEuler
      exact hEuler

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
