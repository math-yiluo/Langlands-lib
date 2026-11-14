import Langlands.Shimura.PEL.HarrisTaylorCMLambdaTower
import Langlands.Shimura.Unitary.KottwitzHarrisComparison
import Langlands.Shimura.Unitary.KottwitzPolynomial
import Langlands.Shimura.Unitary.KottwitzChart
import Langlands.Cohomology.Weights.Polynomial

/-! # Kottwitz's theorem on the `λ`-adic cohomology of the CM Shimura varieties

Kottwitz (1992), *On the `λ`-adic representations associated to some simple Shimura
varieties*, Theorem 1, printed p. 657, stated for the Library's `λ`-adic cohomology of the CM
Shimura varieties of Harris's signature, with a general algebraic coefficient system `W`.
See `HarrisTaylorCMKottwitzStatement.md`.
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
open Langlands.GaloisRepresentation (Objects HasEulerPolynomialAt)
open Langlands.Shimura.KottwitzUnramified (UnramifiedChart LocalPoints SqrtPrime)
open Langlands.Shimura.KottwitzDual (IsKottwitzPolynomial)
open Langlands.Cohomology.Weights (IsWeilNumber IsPurePolynomial)

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
/-- The derived-category instances of the Library's `λ`-adic cohomology for the coefficient
prime `ℓ`. -/
local notation "derivedInstances" ℓ =>
  ∀ U' : SmallCMLevel D, HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U')
        (HarrisCoefficientIntegers K ℓ))

set_option hygiene false in
/-- `π_f ⊗_K K_λ`. -/
local notation "τλ" =>
  (Module.End.baseChangeHom K (FiniteCompletion K lam.1) V).toMonoidHom.comp πf

set_option hygiene false in
local notation "towerλ" => cmHarrisLambdaTowerExtendScalars D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry hRigid
  lam i (FiniteCompletion K lam.1)

set_option hygiene false in
/-- The place `v` of `F` determined by `θ`, via `Φ τ₁ : F → ℂ`. -/
local notation "vθ" => (harrisPlace p₀ θ (Φ C.distinguished)).1

/-- **Kottwitz (1992), Theorem 1**, printed p. 657, for the Library's CM Shimura varieties
`S_U` of Harris's signature and the Library's `λ`-adic cohomology with coefficients in the
algebraic representation `ρ` of `GG` over the number field `K` (Kottwitz's `ξ` over `L`).

Hypotheses: `A` is a division algebra; `3 ≤ n` or `E` has a real place other than the
distinguished one (so that the reflex field is `Φ τ₁ (F)`); `ρ` is irreducible over `K̄`;
the central scalars `t ∈ K^×` act on `W` by `t^{-w}` (so `w = w(ξ)`); `π_f` is an admissible
representation of `GG(A_f)` over `K`, irreducible over `K̄`.

Conclusion: there is an integer `a` (Kottwitz's `a(π_f)`) such that
(a) for every place `λ` of `K`, `a ≠ 0` if and only if some `W^i(π_f)_λ` is nonzero; and
(b) there is a finite set `S` of primes such that for every prime `p₀ ∉ S` at which `F` is
unramified and the level `U` is `K_{p₀} × K^{p₀}` with `K_{p₀}` the level of a standard
unramified chart `c`, and for every `p₀`-component `π_{p₀}` of `π_f`: if `a ≠ 0`, then `π_{p₀}`
is unramified, and for every place `v` of `F` above `p₀` (given by `θ`) Kottwitz's polynomial
`P = P(π_{p₀}, F_v)` has roots of weight `i + w` with `i ≡ 0` or `1 mod 2` according to the sign
of `a`, factors uniquely as `∏_{i ≤ 2(n-1)} P_i` with `P_i` pure of weight `i + w`, and for
every place `λ` of `K` not above `p₀` the representation `W^i(π_f)_λ` is unramified at `v` with
Euler polynomial the reverse of `P_i^{|a|}`. -/
def CMHarrisKottwitzLambdaAdicStatement : Prop :=
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
  ∃ a : ℤ,
    (∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances ℓ]
      [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
      (lam : FinitePlacesAbove K ℓ),
      (∀ i : ℕ, CMHarrisLambdaTowerFixedVectorComparison D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry
        hRigid lam i) →
      (a ≠ 0 ↔ ∃ i : ℕ, Nontrivial (cmHarrisLambdaTowerHeckeMultiplicity D C preservation
        composition unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry
        hRigid lam i (FiniteCompletion K lam.1) (τλ) U).V)) ∧
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
          (∀ (ι : K →+* ℂ) (z : ℂ), z ∈ (P.map ι).roots →
            ∃ i : ℕ, i ≤ 2 * (n - 1) ∧ (Even i ↔ 0 < a) ∧
              IsWeilNumber (Ideal.absNorm (vθ).asIdeal) ((i : ℤ) + w) z) ∧
          ∃ Pf : Fin (2 * (n - 1) + 1) → Polynomial K,
            ((∏ i, Pf i) = P ∧
              ∀ i, IsPurePolynomial (Ideal.absNorm (vθ).asIdeal) ((i.val : ℤ) + w) (Pf i)) ∧
            (∀ Q : Fin (2 * (n - 1) + 1) → Polynomial K, (∏ i, Q i) = P →
              (∀ i, IsPurePolynomial (Ideal.absNorm (vθ).asIdeal) ((i.val : ℤ) + w) (Q i)) →
              Q = Pf) ∧
            ∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances ℓ]
              [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
              (lam : FinitePlacesAbove K ℓ), ℓ ≠ rationalPrimePlace p₀ →
              ∀ (i : ℕ) (hi : i ≤ 2 * (n - 1))
                (hfix : CMHarrisLambdaTowerFixedVectorComparison D C preservation composition
                  unitCoherence associativity comparison symmetry stability square universality
                  dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence
                  geometry hRigid lam i)
                (hcont : CMHarrisLambdaCohomologyContinuous D C preservation composition
                  unitCoherence associativity comparison symmetry stability square universality
                  dualityNaturality polarizationStability compatibility h htor q U ρ ℓ existence
                  geometry (hRigid U) lam i)
                [Module.Finite (FiniteCompletion K lam.1)
                  (fixedVectors (τλ) (inverseOpposite U.obj).subgroup →ₗ[
                    Langlands.Shimura.LevelHecke.LevelHeckeAlgebra (FiniteCompletion K lam.1)
                      (inverseOpposite U.obj).subgroup]
                    fixedVectors (towerλ).V.representation (inverseOpposite U.obj).subgroup)],
                HasEulerPolynomialAt
                  (cmHarrisLambdaHeckeMultiplicityObjects D C preservation composition
                    unitCoherence associativity comparison symmetry stability square universality
                    dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence
                    geometry hRigid lam i (FiniteCompletion K lam.1) continuous_id hfix U hcont
                    (τλ))
                  (vθ)
                  (((Pf ⟨i, Nat.lt_succ_of_le hi⟩ ^ a.natAbs).map
                    (algebraMap K (FiniteCompletion K lam.1))).reverse)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
