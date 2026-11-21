import Langlands.Shimura.PEL.HarrisTaylorCMKottwitzTraceComparison
import Langlands.Cohomology.Weights.PowerTraces
import Langlands.Global.AdelicFunctoriality.LocalDegree

/-! # Reducing the Harris Frobenius comparison to power traces -/

noncomputable section

universe wS wR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
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
open Langlands.Shimura.DecompositionGroupAction (geometricFrobenius)
open Langlands.Shimura.KottwitzUnramified (UnramifiedChart LocalPoints SqrtPrime)
open Langlands.Shimura.KottwitzDual (IsKottwitzPolynomial)
open Langlands.Cohomology.Weights
open Langlands.AlgebraicGeometry

/-- Transport the algebraic step of §5 to a comparison on actual Frobenius
operators, once the finite-dimensional models and the signed traces are supplied. -/
private theorem charpoly_virtualIdentity_of_powerTrace
    {F K R : Type} [Field F] [NumberField F] [Field K] [Field R]
    (d : ℕ) (v : Global.FinitePlace F) (w a : ℤ) (j : R →+* ℂ) (f : K →+* R)
    (P : Polynomial K) (hPm : P.Monic) (hP0 : P.eval 0 ≠ 0)
    (M : Fin (2 * d + 1) → ModuleCat.{0} R)
    (hfin : ∀ i, Module.Finite R (M i))
    (T : ∀ i, (M i) ≃ₗ[R] (M i))
    (hpure : ∀ i, letI := hfin i
      ∀ z ∈ ((T i).toLinearMap.charpoly.map j).roots,
        IsWeilNumber (Ideal.absNorm v.asIdeal) ((i.val : ℤ) + w) z)
    (htrace : ∃ N : ℕ, ∀ k ≥ N,
      ∑ i, (-1 : ℂ) ^ i.val * complexPowerTrace j (T i).toLinearMap k =
        (a : ℂ) * rootPowerSum (P.map (j.comp f)) k) :
    CMHarrisKottwitzVirtualIdentity d v w a (j.comp f) P
      (fun i => letI := hfin i; (T i).toLinearMap.charpoly.map j) := by
  let H : Fin (2 * d + 1) → ℂ[X] :=
    fun i => letI := hfin i; (T i).toLinearMap.charpoly.map j
  have hm (i) : (H i).Monic := by
    let := hfin i
    exact (LinearMap.charpoly_monic _).map _
  have hu (i) : IsUnit (T i).toLinearMap :=
    ⟨LinearEquiv.automorphismGroup.toLinearMapMonoidHom.toHomUnits (T i), rfl⟩
  have hz (i) : (H i).eval 0 ≠ 0 := by
    let := hfin i
    change ((T i).toLinearMap.charpoly.map j).eval 0 ≠ 0
    have he : ((T i).toLinearMap.charpoly.map j).eval 0 = j ((T i).toLinearMap.charpoly.eval 0) := by
      simpa only [map_zero] using Polynomial.eval_map_apply (f := j)
        (p := (T i).toLinearMap.charpoly) 0
    rw [he]
    exact (_root_.map_ne_zero j).2 (charpoly_eval_zero_ne_zero_of_isUnit _ (hu i))
  have hpz : (P.map (j.comp f)).eval 0 ≠ 0 := by
    have he : (P.map (j.comp f)).eval 0 = (j.comp f) (P.eval 0) := by
      simpa only [map_zero] using Polynomial.eval_map_apply (f := j.comp f) (p := P) 0
    rw [he]
    exact (_root_.map_ne_zero _).2 hP0
  obtain ⟨N, hN⟩ := htrace
  refine ⟨fun i => ⟨hm i, hpure i⟩, ?_⟩
  apply alternatingPolynomial_eq_zpow_of_eventual_powerSums hm hz (hPm.map _) hpz
    (N := N)
  intro k hk
  rw [← hN k hk]
  refine Finset.sum_congr rfl fun i _ => congrArg (fun z => (-1 : ℂ) ^ i.val * z) ?_
  let := hfin i
  exact (complexPowerTrace_eq_rootPowerSum j (T i).toLinearMap (hu i) k).symm

/-- A matrix unit over a field has characteristic polynomial with nonzero constant term. -/
private theorem matrix_charpoly_eval_zero_ne_zero {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Field R] (M : Matrix ι ι R) (hM : IsUnit M) : M.charpoly.eval 0 ≠ 0 := by
  rw [Matrix.eval_charpoly, map_zero, zero_sub, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (hM.map Matrix.detMonoidHom).ne_zero

/-- The matrix of a linear automorphism in a basis is a unit. -/
private theorem isUnit_toMatrix_linearEquiv {ι R M : Type*} [Fintype ι] [DecidableEq ι]
    [CommSemiring R] [AddCommMonoid M] [Module R M] (b : Module.Basis ι R M) (e : M ≃ₗ[R] M) :
    IsUnit (LinearMap.toMatrix b b e.toLinearMap) := by
  have he : IsUnit (e.toLinearMap : Module.End R M) :=
    ⟨LinearEquiv.automorphismGroup.toLinearMapMonoidHom.toHomUnits e, rfl⟩
  exact he.map (LinearMap.toMatrixAlgEquiv b)

open scoped Classical in
/-- Kottwitz's polynomial is the characteristic polynomial of an automorphism, so its constant
term is nonzero. -/
private theorem kottwitzCharpoly_eval_zero_ne_zero {S : Type*} [Fintype S] {n : ℕ}
    {L : Type*} [Field L] (hS : S × Bool → ℕ) (hsum : ∀ τ, hS (τ, true) + hS (τ, false) = n)
    (G : KottwitzDual.CMPerm S) (f : ℕ)
    (hGf : ∀ x, hS (((G ^ f : KottwitzDual.CMPerm S) : Equiv.Perm (S × Bool)) x) = hS x)
    (s : Lˣ) (x : KottwitzDual.DualGroup S n L) :
    (KottwitzDual.kottwitzCharpoly hS hsum G f hGf s x).eval 0 ≠ 0 := by
  unfold KottwitzDual.kottwitzCharpoly
  refine matrix_charpoly_eval_zero_ne_zero _ ?_
  unfold KottwitzDual.kottwitzFrobenius
  exact isUnit_toMatrix_linearEquiv _ _

private theorem choose_coefficient_place_away_from {K : Type} [Field K] [NumberField K]
    (p : Global.FinitePlace ℚ) : ∃ (ℓ : Global.FinitePlace ℚ) (_ : FinitePlacesAbove K ℓ), ℓ ≠ p := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h23 : rationalPrimePlace 2 ≠ rationalPrimePlace 3 := by
    intro hEq
    have hEq' := Rat.HeightOneSpectrum.primesEquiv.symm.injective hEq
    exact (by decide : (2 : ℕ) ≠ 3) (congrArg Subtype.val hEq')
  by_cases he : rationalPrimePlace 2 = p
  · exact ⟨rationalPrimePlace 3, placeAbove K _, fun h => h23 (he.trans h.symm)⟩
  · exact ⟨rationalPrimePlace 2, placeAbove K _, he⟩

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
/-- Harris's CM-type section `Φ`. -/
local notation "Φ" => harrisCMSection E (algebraMap L F) τ₀

set_option hygiene false in
local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

set_option hygiene false in
local notation "levelSheaf(" ℓ ", " U' ")" =>
  EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q).obj U')
      (HarrisCoefficientIntegers K ℓ)

set_option hygiene false in
local notation "derivedInstances(" ℓ ")" =>
  ∀ U' : SmallCMLevel D, HasDerivedCategory.{wS} (levelSheaf(ℓ, U'))

set_option hygiene false in
/-- `π_f ⊗_K K_λ`. -/
local notation "τλ" =>
  (Module.End.baseChangeHom K (FiniteCompletion K lam.1) V).toMonoidHom.comp πf

set_option hygiene false in
/-- The place `v` of `F` determined by `θ`, via `Φ τ₁ : F → ℂ`. -/
local notation "vθ" => (harrisPlace p₀ θ (Φ C.distinguished)).1

set_option hygiene false in
local notation "fixedComparison(" i ")" => CMHarrisLambdaTowerFixedVectorComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry
  hRigid lam i

set_option hygiene false in
local notation "harrisMultiplicity(" i ")" => cmHarrisLambdaTowerHeckeMultiplicity D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry
  hRigid lam i (FiniteCompletion K lam.1) (τλ) U

set_option hygiene false in
local notation "levelUnramified(" v ", " i ")" => CMHarrisLambdaCohomologyUnramifiedAt D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ ℓ existence geometry
  (hRigid U) lam i v

section AtPlace

variable (ℓ : Global.FinitePlace ℚ) [derivedInstances(ℓ)]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
  (lam : FinitePlacesAbove K ℓ) {V : Type} [AddCommGroup V] [Module K V]
  (πf : Representation K D.rationalInvolution.FiniteAdelicPoints V)

local notation "Rλ" => FiniteCompletion K lam.1
local notation "degrees" => Fin (2 * (n - 1) + 1)

set_option hygiene false in
local notation "FrobOnMultiplicity(" v ", " i ")" =>
  (geometricFrobenius (ModuleCat.{0} Rλ) v (harrisMultiplicity(i))
    (chosenClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v))).hom

/-- Local input in trace form. Finite-dimensional operators can be supplied before assuming
fixed-vector comparisons. Under the comparison in each degree, the corresponding operator is
identified with the chosen geometric Frobenius on the actual Harris Hecke Hom. -/
def CMHarrisKottwitzAtPlacePowerTrace (v : Global.FinitePlace F) (w a : ℤ)
    (P : Polynomial K) : Prop :=
  ∃ (j : Rλ →+* ℂ) (M : degrees → ModuleCat.{0} Rλ)
    (hfin : ∀ i, Module.Finite Rλ (M i)) (T : ∀ i, (M i) ≃ₗ[Rλ] (M i)),
    (∀ i, letI := hfin i
      ∀ z ∈ ((T i).toLinearMap.charpoly.map j).roots,
        IsWeilNumber (Ideal.absNorm v.asIdeal) ((i.val : ℤ) + w) z) ∧
    (∃ N : ℕ, ∀ k ≥ N,
      ∑ i, (-1 : ℂ) ^ i.val * complexPowerTrace j (T i).toLinearMap k =
        (a : ℂ) * rootPowerSum (P.map (j.comp (algebraMap K Rλ))) k) ∧
    ∀ i : degrees, levelUnramified(v, i.val) ∧
      (fixedComparison(i.val) →
        ∃ e : (M i) ≃ₗ[Rλ] (harrisMultiplicity(i.val)).V,
          (e : (M i) →ₗ[Rλ] (harrisMultiplicity(i.val)).V) ∘ₗ (T i).toLinearMap =
            FrobOnMultiplicity(v, i.val) ∘ₗ (e : (M i) →ₗ[Rλ] (harrisMultiplicity(i.val)).V))

set_option hygiene false in
local notation "powerTracesAt(" v ", " P ")" =>
  CMHarrisKottwitzAtPlacePowerTrace D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q ρ existence geometry hRigid U ℓ lam πf v w a P

set_option hygiene false in
local notation "frobeniusComparison(" v ", " H ")" =>
  CMHarrisKottwitzFrobeniusComparison D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q ρ existence geometry hRigid U ℓ lam πf v H

set_option hygiene false in
local notation "virtualIdentity(" v ", " j ", " P ", " H ")" =>
  CMHarrisKottwitzVirtualIdentity (n - 1) v w a
    (j.comp (algebraMap K (FiniteCompletion K lam.1))) P (fun i => (H i).map j)

set_option maxHeartbeats 1800000 in
/-- From eventual projected power traces and degreewise comparison on actual spaces, obtain
the two at-place clauses used by the published target. -/
theorem cmHarrisKottwitz_atPlace_of_powerTrace (v : Global.FinitePlace F) (w a : ℤ)
    (P : Polynomial K) (hPm : P.Monic) (hP0 : P.eval 0 ≠ 0) (htrace : powerTracesAt(v, P)) :
    ∃ (j : Rλ →+* ℂ) (H : degrees → Polynomial Rλ),
      frobeniusComparison(v, H) ∧ virtualIdentity(v, j, P, H) := by
  obtain ⟨j, M, hfin, T, hpure, hpow, hcomp⟩ := htrace
  let H : degrees → Polynomial Rλ := fun i => letI := hfin i; (T i).toLinearMap.charpoly
  refine ⟨j, H, ?_, ?_⟩
  · intro i
    refine ⟨(hcomp i).1, fun hfix => ?_⟩
    obtain ⟨e, he⟩ := (hcomp i).2 hfix
    let := hfin i
    let hfin' := Module.Finite.of_surjective e.toLinearMap e.surjective
    let := hfin'
    exact ⟨hfin', (FrobeniusPolynomial.charpoly_eq_of_comp_eq e he).symm⟩
  · exact charpoly_virtualIdentity_of_powerTrace _ v w a j (algebraMap K Rλ) P hPm hP0
      M hfin T hpure hpow

end AtPlace

set_option hygiene false in
local notation "powerTracesAt(" v ", " P ")" =>
  CMHarrisKottwitzAtPlacePowerTrace D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q ρ existence geometry hRigid U ℓ lam πf v w a P

set_option linter.unusedVariables false in
set_option maxHeartbeats 3000000 in
/-- Uniform inputs for the assembly of the exact trace comparison. The standard derived-category
witness in the published conclusion is not an additional premise here. Instead supply the power
traces over the two arbitrary universes and over the standard localization choices. The latter
can be obtained by proving a universe-polymorphic geometric and spectral comparison. -/
def CMHarrisKottwitzPowerTraceInputs : Prop :=
  ∀ (_hdiv : ∀ a : A, a ≠ 0 → IsUnit a)
    (_hn : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished)
    (_hρ : Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (ρ.act (AlgebraicClosure K))))
    (w : ℤ)
    (_hw : ∀ (g : (D.rationalInvolution.baseChange K).similitudes) (t : Kˣ),
      ((g.1.1 : K ⊗[ℚ] A) = algebraMap K (K ⊗[ℚ] A) t) →
        ∀ x : W, ρ.rationalAction g x = ((t : K) ^ (-w)) • x)
    {V : Type} [AddCommGroup V] [Module K V]
    (πf : Representation K D.rationalInvolution.FiniteAdelicPoints V)
    (_hadm : Langlands.IsAdmissible πf)
    (_hirr : Representation.IsIrreducible
      ((Module.End.baseChangeHom K (AlgebraicClosure K) V).toMonoidHom.comp πf)),
  ∃ (a : ℤ) (S : Finset ℕ),
    (∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances(ℓ)]
      [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
      (lam : FinitePlacesAbove K ℓ),
      (∃ (p : Global.FinitePlace ℚ) (v : FinitePlacesAbove F p), ℓ ≠ p ∧
        ∃ P : Polynomial K, P.Monic ∧ 0 < P.natDegree ∧ P.eval 0 ≠ 0 ∧ powerTracesAt(v.1, P)) ∧
      ∀ i : ℕ, 2 * (n - 1) < i → fixedComparison(i) → Subsingleton (harrisMultiplicity(i)).V) ∧
    ∀ (p₀ : ℕ) [Fact p₀.Prime], p₀ ∉ S →
      KottwitzUnramified.IsUnramifiedAt (rationalPrimePlace p₀) F →
      ∀ c : UnramifiedChart D.toSecondKindInvolution (rationalPrimePlace p₀) n,
      (∃ Kaway : Subgroup (D.rationalInvolution.PrimeToPoints p₀),
        (inverseOpposite U.obj).subgroup.map
            (D.rationalInvolution.finiteAdelicPointsSplit p₀
              (Fact.out : p₀.Prime).ne_zero).toMulEquiv.toMonoidHom =
          (c.level.comap (D.rationalInvolution.dividingLocalMap p₀
            ⟨rationalPrimePlace p₀, natCast_mem_rationalPrimePlace p₀⟩).toMonoidHom).prod
            Kaway) →
      ∀ πp : SmoothRep.{0, 0, 0} K (LocalPoints D.toSecondKindInvolution (rationalPrimePlace p₀)),
      (∃ πaway : Rep.{0} K (D.rationalInvolution.PrimeToPoints p₀),
        Nonempty (πf.Equiv (Representation.tprod
          (πp.representation.comp
            (D.rationalInvolution.finiteLocalMap (rationalPrimePlace p₀)).toMonoidHom)
          (πaway.ρ.comp ((MonoidHom.snd _ _).comp
            (D.rationalInvolution.finiteAdelicPointsSplit p₀
              (Fact.out : p₀.Prime).ne_zero).toMulEquiv.toMonoidHom))))) →
      a ≠ 0 →
        c.IsSphericalIrreducible (AlgebraicClosure K) πp ∧
        ∀ (θ : ℂ →+* PadicAlgCl p₀)
          (s : SqrtPrime (rationalPrimePlace p₀) (AlgebraicClosure K)) (P : Polynomial K),
          IsKottwitzPolynomial c θ hΦ C.hodgeFunction
            (KottwitzDual.harrisCharts_hodgeFunction_add_conjugate hΦ C) πp s P →
          (∀ (ℓ : Global.FinitePlace ℚ) (lam : FinitePlacesAbove K ℓ),
            ℓ ≠ rationalPrimePlace p₀ →
            letI : ∀ U' : SmallCMLevel D, HasDerivedCategory (levelSheaf(ℓ, U')) :=
              fun U' => HasDerivedCategory.standard (levelSheaf(ℓ, U'))
            letI := HasDerivedCategory.standard (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))
            powerTracesAt(vθ, P)) ∧
          ∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances(ℓ)]
            [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
            (lam : FinitePlacesAbove K ℓ), ℓ ≠ rationalPrimePlace p₀ → powerTracesAt(vθ, P)

set_option maxHeartbeats 3500000 in
/-- The exact published trace comparison follows from the uniform power-trace inputs, without
changing the telescope or identifying the two derived-category universes. -/
theorem cmHarrisKottwitzTraceComparison_of_powerTraces
    (hpow : CMHarrisKottwitzPowerTraceInputs.{wS, wR} D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q ρ existence geometry hRigid U) :
    CMHarrisKottwitzTraceComparisonStatement.{wS, wR} D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q ρ existence geometry hRigid U := by
  intro hdiv hn hρ w hw V _ _ πf hadm hirr
  obtain ⟨a, S, haux, hchart⟩ := @hpow hdiv hn hρ w hw V _ _ πf hadm hirr
  refine ⟨a, S, ?_, ?_⟩
  · intro ℓ hS hR lam
    obtain ⟨⟨p, v, hℓ, P, hPm, hPdeg, hP0, hPv⟩, habove⟩ := @haux ℓ hS hR lam
    obtain ⟨j, H, hFrob, hvirt⟩ := cmHarrisKottwitz_atPlace_of_powerTrace
      D C preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor q ρ existence
      geometry hRigid U ℓ lam πf v.1 w a P hPm hP0 hPv
    exact ⟨⟨p, v, hℓ, j, H, P, hPm, hPdeg, hFrob, hvirt⟩, habove⟩
  · intro p₀ hp₀ hp hunr c hlevel πp hπp ha
    obtain ⟨hspherical, hpolys⟩ := @hchart p₀ hp₀ hp hunr c hlevel πp hπp ha
    refine ⟨hspherical, ?_⟩
    intro θ s P hP
    have hPm := hP.monic_and_natDegree.1
    have hP0 : P.eval 0 ≠ 0 := by
      have hnonzero : (P.map (algebraMap K (AlgebraicClosure K))).eval 0 ≠ 0 := by
        obtain ⟨-, t, -, -, heq⟩ := hP
        rw [heq]
        exact kottwitzCharpoly_eval_zero_ne_zero _ _ _ _ _ _ _
      intro hzero
      exact hnonzero (by
        simpa only [map_zero, hzero] using Polynomial.eval_map_apply
          (f := algebraMap K (AlgebraicClosure K)) (p := P) 0)
    obtain ⟨hstd, hall⟩ := hpolys θ s P hP
    constructor
    · obtain ⟨ℓ, lam, hℓ⟩ := choose_coefficient_place_away_from (K := K) (rationalPrimePlace p₀)
      refine ⟨ℓ, lam, hℓ, ?_⟩
      let : ∀ U' : SmallCMLevel D, HasDerivedCategory (levelSheaf(ℓ, U')) :=
        fun U' => HasDerivedCategory.standard (levelSheaf(ℓ, U'))
      let := HasDerivedCategory.standard (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))
      exact cmHarrisKottwitz_atPlace_of_powerTrace D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q ρ existence geometry hRigid U ℓ lam πf
        vθ w a P hPm hP0 (hstd ℓ lam hℓ)
    · intro ℓ hS hR lam hℓ
      exact cmHarrisKottwitz_atPlace_of_powerTrace D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q ρ existence geometry hRigid U ℓ lam πf
        vθ w a P hPm hP0 (@hall ℓ hS hR lam hℓ)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
