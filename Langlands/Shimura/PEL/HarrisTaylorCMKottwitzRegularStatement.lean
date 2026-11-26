import Langlands.Shimura.PEL.HarrisTaylorCMKottwitzTraceComparison
import Langlands.Shimura.Coefficients.RegularHighestWeight
import Langlands.Cohomology.Weights.AlternatingConcentration

/-! # Kottwitz's theorem on the Harris CM tower without purity

Two statements beside the published `CMHarrisKottwitzTraceComparisonStatement` and
`CMHarrisKottwitzLambdaAdicStatement`, without their weight clauses: Kottwitz's
identity for the alternating sum of the cohomology (Kottwitz 1992, (5.1)–(5.6)), and,
for a coefficient system of regular highest weight, the description of the middle
degree (Kottwitz 1992, printed p. 658). The vanishing outside the middle degree is a
named input. See `HarrisTaylorCMKottwitzRegularStatement.md`.
-/

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
open Langlands.GaloisRepresentation (chosenClosureEmbedding HasEulerPolynomialAt)
open Langlands.Shimura.DecompositionGroupAction (geometricFrobenius)
open Langlands.Shimura.KottwitzUnramified (UnramifiedChart LocalPoints SqrtPrime)
open Langlands.Shimura.KottwitzDual (IsKottwitzPolynomial)
open Langlands.Cohomology.Weights (IsWeilNumber alternatingPolynomial)

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
local notation "heckeMultiplicity(" i ")" => cmHarrisLambdaTowerHeckeMultiplicity D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry
  hRigid lam i (FiniteCompletion K lam.1) (τλ) U

set_option hygiene false in
local notation "levelUnramified(" v ", " i ")" => CMHarrisLambdaCohomologyUnramifiedAt D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ ℓ existence geometry
  (hRigid U) lam i v

set_option hygiene false in
local notation "frobeniusComparison(" v ", " H ")" =>
  CMHarrisKottwitzFrobeniusComparison D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q ρ existence geometry hRigid U ℓ lam πf v H

set_option hygiene false in
local notation "traceIdentity(" j ", " P ", " H ")" =>
  CMHarrisKottwitzTraceIdentity (n - 1) a
    (j.comp (algebraMap K (FiniteCompletion K lam.1))) P (fun i => (H i).map j)

set_option hygiene false in
local notation "multiplicityObjects(" i ", " hfix ", " hcont ")" =>
  cmHarrisLambdaHeckeMultiplicityObjects D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence
    geometry hRigid lam i (FiniteCompletion K lam.1) continuous_id hfix U hcont (τλ)

set_option hygiene false in
local notation "levelContinuous(" i ")" => CMHarrisLambdaCohomologyContinuous D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ ℓ existence
  geometry (hRigid U) lam i

set_option hygiene false in
local notation "levelFinite(" i ")" => Module.Finite (FiniteCompletion K lam.1)
  (fixedVectors (τλ) (inverseOpposite U.obj).subgroup →ₗ[
    Langlands.Shimura.LevelHecke.LevelHeckeAlgebra (FiniteCompletion K lam.1)
      (inverseOpposite U.obj).subgroup]
    fixedVectors (cmHarrisLambdaTowerExtendScalars D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry
      hRigid lam i (FiniteCompletion K lam.1)).V.representation (inverseOpposite U.obj).subgroup)

/-- Kottwitz's identity for the alternating sum without weights, at the complex
realization `ι`: the polynomials `H i` (the characteristic polynomials of geometric
Frobenius in the degrees `i ≤ 2d`) are monic and their alternating characteristic
rational function is `ι(P)^a`. The identity implies that for every `m ≥ 1` the
alternating sum of the `m`-th power sums of the roots of the `H i` is `a` times the
`m`-th power sum of the roots of `ι(P)`. Conversely these power-sum identities give the
rational-function identity when `P` is monic and all the polynomials have nonzero
constant terms, as characteristic polynomials of automorphisms do (the published
`alternatingPolynomial_eq_zpow_of_eventual_powerSums`); power sums do not see the root
`0`. -/
def CMHarrisKottwitzTraceIdentity (d : ℕ) (a : ℤ) (ι : K →+* ℂ) (P : Polynomial K)
    (H : Fin (2 * d + 1) → Polynomial ℂ) : Prop :=
  (∀ i, (H i).Monic) ∧
    alternatingPolynomial d H = (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.map ι)) ^ a

/-- **Kottwitz (1992), (5.1)–(5.6)**, without purity, on the Library's CM Shimura
varieties of Harris's signature: the weight-free form of the published
`CMHarrisKottwitzTraceComparisonStatement`. The hypotheses are those of the published
statement without the weight `w`. There are a signed integer `a` and a finite set `S` of
primes such that:

* for every coefficient place `λ` (above `ℓ`) there is an auxiliary place `v` of `F`
  above a prime `p ≠ ℓ` at which the characteristic polynomials `H` of geometric
  Frobenius on the Hecke multiplicity spaces satisfy the identity with a monic
  polynomial `P` of positive degree; and in every degree above `2(n - 1)` the Hecke
  multiplicity space vanishes under the fixed-vector comparison in that degree;
* at every prime `p₀ ∉ S` where `F` is unramified, the level is a standard unramified
  chart level and `π_{p₀}` is a component of `π_f`, for every place `v` of `F` above
  `p₀` and every coefficient place above `ℓ ≠ p₀`: if `a ≠ 0` then `π_{p₀}` is spherical;
  for every Kottwitz polynomial `P = P(π_{p₀}, F_v)` the characteristic polynomials of
  geometric Frobenius on the multiplicity spaces `W^i(π_f)_λ` satisfy the identity with
  `P`, for every `a` including `a = 0` (the virtual representation
  `Σ_i (-1)^i W^i(π_f)_λ` has characteristic rational function `P^a`); and if `π_{p₀}`
  is not spherical, they satisfy the identity with `P = 1` (the characteristic rational
  function is `1`).

No weight of a Frobenius eigenvalue is asserted. -/
def CMHarrisKottwitzTraceIdentityStatement : Prop :=
  ∀ (_hdiv : ∀ a : A, a ≠ 0 → IsUnit a)
    (_hn : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished)
    (_hρ : Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (ρ.act (AlgebraicClosure K))))
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
        ∃ (j : FiniteCompletion K lam.1 →+* ℂ)
          (H : Fin (2 * (n - 1) + 1) → Polynomial (FiniteCompletion K lam.1))
          (P : Polynomial K),
          P.Monic ∧ 0 < P.natDegree ∧ frobeniusComparison(v.1, H) ∧ traceIdentity(j, P, H)) ∧
      ∀ i : ℕ, 2 * (n - 1) < i → fixedComparison(i) → Subsingleton (heckeMultiplicity(i)).V) ∧
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
        (a ≠ 0 → c.IsSphericalIrreducible (AlgebraicClosure K) πp) ∧
        (∀ (θ : ℂ →+* PadicAlgCl p₀)
          (s : SqrtPrime (rationalPrimePlace p₀) (AlgebraicClosure K)) (P : Polynomial K),
          IsKottwitzPolynomial c θ hΦ C.hodgeFunction
            (KottwitzDual.harrisCharts_hodgeFunction_add_conjugate hΦ C) πp s P →
          ∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances(ℓ)]
            [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
            (lam : FinitePlacesAbove K ℓ), ℓ ≠ rationalPrimePlace p₀ →
            ∃ (j : FiniteCompletion K lam.1 →+* ℂ)
              (H : Fin (2 * (n - 1) + 1) → Polynomial (FiniteCompletion K lam.1)),
              frobeniusComparison(vθ, H) ∧ traceIdentity(j, P, H)) ∧
        (¬ c.IsSphericalIrreducible (AlgebraicClosure K) πp →
          ∀ (θ : ℂ →+* PadicAlgCl p₀) (ℓ : Global.FinitePlace ℚ) [derivedInstances(ℓ)]
            [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
            (lam : FinitePlacesAbove K ℓ), ℓ ≠ rationalPrimePlace p₀ →
            ∃ (j : FiniteCompletion K lam.1 →+* ℂ)
              (H : Fin (2 * (n - 1) + 1) → Polynomial (FiniteCompletion K lam.1)),
              frobeniusComparison((harrisPlace p₀ θ (Φ C.distinguished)).1, H) ∧
                traceIdentity(j, (1 : Polynomial K), H))

/-- The vanishing outside the middle degree, a named input: for a coefficient system
of regular highest weight, the Hecke multiplicity spaces `W^i(π_f)_λ` vanish in every
degree `i ≠ n - 1`, under the fixed-vector comparison in that degree. Kottwitz (1992),
printed p. 658, states it as a consequence of the work of Vogan and Zuckerman (1984). A
proof combines their Theorems 5.5 and 5.6 for `SU(n - 1, 1)` with Matsushima's formula
and the comparison of the `λ`-adic cohomology with the cohomology of the complex points.
The statement is not proved here. -/
def CMHarrisKottwitzRegularVanishingStatement : Prop :=
  ∀ (_hdiv : ∀ a : A, a ≠ 0 → IsUnit a)
    (_hn : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished)
    (_hρ : Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (ρ.act (AlgebraicClosure K))))
    (_hreg : Langlands.Shimura.AlgebraInvolution.IsRegularHighestWeight n ρ)
    {V : Type} [AddCommGroup V] [Module K V]
    (πf : Representation K D.rationalInvolution.FiniteAdelicPoints V)
    (_hadm : Langlands.IsAdmissible πf)
    (_hirr : Representation.IsIrreducible
      ((Module.End.baseChangeHom K (AlgebraicClosure K) V).toMonoidHom.comp πf))
    (ℓ : Global.FinitePlace ℚ) [derivedInstances(ℓ)]
    [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
    (lam : FinitePlacesAbove K ℓ) (i : ℕ), i ≠ n - 1 →
    fixedComparison(i) → Subsingleton (heckeMultiplicity(i)).V

/-- **Kottwitz (1992), printed p. 658**, without purity: Theorem 1 when the highest
weight of the coefficient system is regular, a weight-free form of the published
`CMHarrisKottwitzLambdaAdicStatement`. The hypotheses are those of the published
statement without the weight `w`, together with regular highest weight of `ρ`. There is
an integer `a` such that

* for every coefficient place `λ`, `W^i(π_f)_λ = 0` for `i ≠ n - 1`, and `a ≠ 0` exactly
  when `W^{n-1}(π_f)_λ ≠ 0` (under the fixed-vector comparisons);
* there is a finite set `S` of primes such that, if `a ≠ 0`, at every prime `p₀ ∉ S`
  where `F` is unramified, the level is a standard unramified chart level and `π_{p₀}`
  is a component of `π_f`: `π_{p₀}` is spherical, and for every place `v` of `F` above
  `p₀` and every coefficient place above `ℓ ≠ p₀`, `W^{n-1}(π_f)_λ` is unramified at
  `v` with Euler polynomial the reverse of `P^{|a|}`, `P = P(π_{p₀}, F_v)` Kottwitz's
  polynomial.

No weight of a Frobenius eigenvalue is asserted. -/
def CMHarrisKottwitzRegularMiddleDegreeStatement : Prop :=
  ∀ (_hdiv : ∀ a : A, a ≠ 0 → IsUnit a)
    (_hn : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished)
    (_hρ : Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (ρ.act (AlgebraicClosure K))))
    (_hreg : Langlands.Shimura.AlgebraInvolution.IsRegularHighestWeight n ρ)
    {V : Type} [AddCommGroup V] [Module K V]
    (πf : Representation K D.rationalInvolution.FiniteAdelicPoints V)
    (_hadm : Langlands.IsAdmissible πf)
    (_hirr : Representation.IsIrreducible
      ((Module.End.baseChangeHom K (AlgebraicClosure K) V).toMonoidHom.comp πf)),
  ∃ a : ℤ,
    (∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances(ℓ)]
      [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
      (lam : FinitePlacesAbove K ℓ),
      (∀ i : ℕ, i ≠ n - 1 → fixedComparison(i) → Subsingleton (heckeMultiplicity(i)).V) ∧
      ((∀ i : ℕ, fixedComparison(i)) →
        (a ≠ 0 ↔ Nontrivial (heckeMultiplicity(n - 1)).V))) ∧
    ∃ S : Finset ℕ, ∀ (p₀ : ℕ) [Fact p₀.Prime], p₀ ∉ S →
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
          ∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances(ℓ)]
            [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
            (lam : FinitePlacesAbove K ℓ), ℓ ≠ rationalPrimePlace p₀ →
            ∀ (hfix : ∀ i : ℕ, fixedComparison(i)) (hcont : levelContinuous(n - 1))
              [levelFinite(n - 1)],
              HasEulerPolynomialAt (multiplicityObjects(n - 1, hfix (n - 1), hcont)) (vθ)
                (((P ^ a.natAbs).map (algebraMap K (FiniteCompletion K lam.1))).reverse)

/-- A finite-dimensional space that is a subsingleton has characteristic polynomial `1`
for every endomorphism. -/
private theorem charpoly_eq_one_of_subsingleton {M : Type} [Field M] {X : Type} [AddCommGroup X]
    [Module M X] [Module.Finite M X] [Subsingleton X] (f : X →ₗ[M] X) : f.charpoly = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic f)
    (by rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton])

/-- The trace identity and the vanishing outside the middle degree give Kottwitz's theorem
in the middle degree for a coefficient system of regular highest weight. -/
def CMHarrisKottwitzRegularMiddleDegreeReductionStatement : Prop :=
  CMHarrisKottwitzTraceIdentityStatement.{wS, wR} D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q ρ existence geometry hRigid U →
  CMHarrisKottwitzRegularVanishingStatement.{wS, wR} D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q ρ existence geometry hRigid U →
  CMHarrisKottwitzRegularMiddleDegreeStatement.{wS, wR} D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q ρ existence geometry hRigid U

set_option maxHeartbeats 2500000 in
/-- Proof of `CMHarrisKottwitzRegularMiddleDegreeReductionStatement`: outside the middle
degree the multiplicity spaces vanish, so their characteristic polynomials are `1`; the
alternating identity then says that the characteristic polynomial in degree `n - 1` is
`P^{|a|}` (`eq_pow_natAbs_of_alternating`). -/
theorem cmHarrisKottwitzRegularMiddleDegree_of_traceIdentity :
    CMHarrisKottwitzRegularMiddleDegreeReductionStatement.{wS, wR} D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q ρ existence geometry
      hRigid U := by
  classical
  intro htrace hvan hdiv hn hρ hreg V _ _ πf hadm hirr
  obtain ⟨a, S, haux, hcharts⟩ := @htrace hdiv hn hρ V _ _ πf hadm hirr
  have hk : n - 1 < 2 * (n - 1) + 1 := by omega
  let k : Fin (2 * (n - 1) + 1) := ⟨n - 1, hk⟩
  refine ⟨a, fun ℓ hS hR lam => ⟨fun i hi hfix => @hvan hdiv hn hρ hreg V _ _ πf hadm hirr
    ℓ hS hR lam i hi hfix, fun hfix => ?_⟩, S, ?_⟩
  · obtain ⟨⟨p, v, _, j, H, P, hPm, hPdeg, hFrob, hid⟩, -⟩ := @haux ℓ hS hR lam
    -- Outside degree `n - 1` the characteristic polynomials are `1`.
    have hone : ∀ i : Fin (2 * (n - 1) + 1), i ≠ k → (H i).map j = 1 := by
      intro i hik
      obtain ⟨hfin, hpoly⟩ := (hFrob i).2 (hfix i.val)
      have hsub := @hvan hdiv hn hρ hreg V _ _ πf hadm hirr ℓ hS hR lam i.val
        (fun h => hik (Fin.ext h)) (hfix i.val)
      rw [← hpoly, charpoly_eq_one_of_subsingleton, Polynomial.map_one]
    obtain ⟨hfin, hpoly⟩ := (hFrob k).2 (hfix (n - 1))
    have hmon : ((H k).map j).Monic := by
      rw [← hpoly]
      exact (LinearMap.charpoly_monic _).map j
    have hdegiff := Langlands.Cohomology.Weights.natDegree_pos_iff_of_alternating
      (fun i => (H i).map j) k hone hmon (hPm.map _) (by rwa [Polynomial.natDegree_map])
      hid.2
    rw [← hdegiff, Polynomial.natDegree_map, ← hpoly, LinearMap.charpoly_natDegree]
    exact Module.finrank_pos_iff
  · intro p₀ hp₀ hgood hunr c hlevel πp hcomponent ha
    obtain ⟨hspherical, hchart, -⟩ := @hcharts p₀ hp₀ hgood hunr c hlevel πp hcomponent
    refine ⟨hspherical ha, ?_⟩
    intro θ s P hP ℓ hS hR lam hl hfix hcont hfinite
    obtain ⟨hPm, hPdim⟩ := hP.monic_and_natDegree
    have hPdeg : 0 < P.natDegree := by
      rw [hPdim, KottwitzDual.kottwitzDim]
      refine Finset.prod_pos fun τ _ => Nat.choose_pos ?_
      have hsum := KottwitzDual.cmHodge_add hΦ C.hodgeFunction
        (KottwitzDual.harrisCharts_hodgeFunction_add_conjugate hΦ C) τ
      change KottwitzDual.cmHodge hΦ C.hodgeFunction (τ, false) ≤ n
      omega
    obtain ⟨j, H, hFrob, hid⟩ := @hchart θ s P hP ℓ hS hR lam hl
    let f := algebraMap K (FiniteCompletion K lam.1)
    have hone : ∀ i : Fin (2 * (n - 1) + 1), i ≠ k → (H i).map j = 1 := by
      intro i hik
      obtain ⟨hfin, hpoly⟩ := (hFrob i).2 (hfix i.val)
      have hsub := @hvan hdiv hn hρ hreg V _ _ πf hadm hirr ℓ hS hR lam i.val
        (fun h => hik (Fin.ext h)) (hfix i.val)
      rw [← hpoly, charpoly_eq_one_of_subsingleton, Polynomial.map_one]
    have ⟨hu, hcomp⟩ := hFrob k
    obtain ⟨_, hchar⟩ := hcomp (hfix (n - 1))
    have hmon : ((H k).map j).Monic := by
      rw [← hchar]
      exact (LinearMap.charpoly_monic _).map j
    have hpow := Langlands.Cohomology.Weights.eq_pow_natAbs_of_alternating
      (fun i => (H i).map j) k hone hmon (hPm.map _) (by rwa [Polynomial.natDegree_map]) hid.2
    have hlocal : H k = (P ^ a.natAbs).map f := by
      apply Polynomial.map_injective j j.injective
      simpa only [Polynomial.map_map, Polynomial.map_pow] using hpow
    have hEuler := hasEulerPolynomialAt_cmHarrisLambdaHeckeMultiplicityObjects D C preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry hRigid
      lam (n - 1) (FiniteCompletion K lam.1) continuous_id (hfix (n - 1)) U hcont (τλ)
      (chosenClosureEmbedding (NumberField.FinitePlace.embedding (K := F) vθ)) hu
    rw [hchar, hlocal] at hEuler
    exact hEuler

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
