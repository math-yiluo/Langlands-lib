import Langlands.Shimura.PEL.HarrisTaylorCMKottwitzStatement
import Langlands.Cohomology.Weights.Separation

/-! # The Frobenius comparison input to Kottwitz's theorem

The comparison on the actual Harris CM tower, in the form used by the algebraic
weight-separation argument. See `HarrisTaylorCMKottwitzTraceComparison.md`.
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
open Langlands.GaloisRepresentation (chosenClosureEmbedding)
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

/-- Degreewise comparison with the characteristic polynomials of geometric Frobenius on the
actual Hecke multiplicity spaces. The ambient cohomology is unramified. Under the fixed-vector
comparison in a degree, the multiplicity space is finite-dimensional and its characteristic
polynomial in that degree is the specified member of `H`. -/
def CMHarrisKottwitzFrobeniusComparison (ℓ : Global.FinitePlace ℚ) [derivedInstances(ℓ)]
    [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
    (lam : FinitePlacesAbove K ℓ) {V : Type} [AddCommGroup V] [Module K V]
    (πf : Representation K D.rationalInvolution.FiniteAdelicPoints V) (v : Global.FinitePlace F)
    (H : Fin (2 * (n - 1) + 1) → Polynomial (FiniteCompletion K lam.1)) : Prop :=
  ∀ i, levelUnramified(v, i.val) ∧
    (fixedComparison(i.val) →
      ∃ hfin : Module.Finite (FiniteCompletion K lam.1) (heckeMultiplicity(i.val)).V,
        letI := hfin
        (geometricFrobenius (ModuleCat.{0} (FiniteCompletion K lam.1)) v
          (heckeMultiplicity(i.val))
          (chosenClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v))).hom.charpoly =
            H i)

/-- Purity and the alternating characteristic rational-function identity of Kottwitz §5
at the complex realization `ι`. Here `H` gives the complex characteristic polynomials of
geometric Frobenius and `P` is the polynomial on the unramified local Langlands side. -/
def CMHarrisKottwitzVirtualIdentity (d : ℕ) (v : Global.FinitePlace F) (w a : ℤ)
    (ι : K →+* ℂ) (P : Polynomial K) (H : Fin (2 * d + 1) → Polynomial ℂ) : Prop :=
  (∀ i, (H i).Monic ∧ ∀ z ∈ (H i).roots, IsWeilNumber (Ideal.absNorm v.asIdeal) ((i.val : ℤ) + w) z) ∧
    alternatingPolynomial d H = (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.map ι)) ^ a

set_option hygiene false in
local notation "frobeniusComparison(" v ", " H ")" =>
  CMHarrisKottwitzFrobeniusComparison D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q ρ existence geometry hRigid U ℓ lam πf v H

set_option hygiene false in
local notation "virtualIdentity(" v ", " j ", " P ", " H ")" =>
  CMHarrisKottwitzVirtualIdentity (n - 1) v w a
    (j.comp (algebraMap K (FiniteCompletion K lam.1))) P (fun i => (H i).map j)

/-- The projected Frobenius comparison on the Harris CM tower from Kottwitz, §5, with the
spherical support consequence of Lemma 4.2. At an auxiliary away-from-`ℓ` place it supplies a
virtual characteristic polynomial for testing occurrence and a degree bound. At the chart
places it relates the virtual polynomial to the Library's Kottwitz polynomial. -/
def CMHarrisKottwitzTraceComparisonStatement : Prop :=
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
        ∃ (j : FiniteCompletion K lam.1 →+* ℂ)
          (H : Fin (2 * (n - 1) + 1) → Polynomial (FiniteCompletion K lam.1))
          (P : Polynomial K),
          P.Monic ∧ 0 < P.natDegree ∧ frobeniusComparison(v.1, H) ∧ virtualIdentity(v.1, j, P, H)) ∧
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
      a ≠ 0 →
        c.IsSphericalIrreducible (AlgebraicClosure K) πp ∧
        ∀ (θ : ℂ →+* PadicAlgCl p₀)
          (s : SqrtPrime (rationalPrimePlace p₀) (AlgebraicClosure K)) (P : Polynomial K),
          IsKottwitzPolynomial c θ hΦ C.hodgeFunction
            (KottwitzDual.harrisCharts_hodgeFunction_add_conjugate hΦ C) πp s P →
          (∃ (ℓ : Global.FinitePlace ℚ) (lam : FinitePlacesAbove K ℓ),
            ℓ ≠ rationalPrimePlace p₀ ∧
            letI : ∀ U' : SmallCMLevel D, HasDerivedCategory (levelSheaf(ℓ, U')) :=
              fun U' => HasDerivedCategory.standard (levelSheaf(ℓ, U'))
            letI := HasDerivedCategory.standard (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))
            ∃ (j : FiniteCompletion K lam.1 →+* ℂ)
              (H : Fin (2 * (n - 1) + 1) → Polynomial (FiniteCompletion K lam.1)),
              frobeniusComparison(vθ, H) ∧ virtualIdentity(vθ, j, P, H)) ∧
          ∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances(ℓ)]
            [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
            (lam : FinitePlacesAbove K ℓ), ℓ ≠ rationalPrimePlace p₀ →
            ∃ (j : FiniteCompletion K lam.1 →+* ℂ)
              (H : Fin (2 * (n - 1) + 1) → Polynomial (FiniteCompletion K lam.1)),
              frobeniusComparison(vθ, H) ∧ virtualIdentity(vθ, j, P, H)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
