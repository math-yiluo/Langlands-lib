import Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology

/-!
# Prime-to-`m` CM cohomology as level invariants

Fix `m ≠ 0` and a level `K₀` at the places dividing `m`. For a `ℚ`-algebra `R` and a
level-trivial diagram of sheaves of `R`-modules on the Library's geometric CM tower whose
transition maps are isomorphisms, this module states that the Library's comparison from the
prime-to-`m` colimit cohomology, over the levels `e⁻¹ (K₀ × K')`, to the colimit over all small
levels is injective, and that its image is the set of classes fixed by `K₀`. This is
`H^d(Sh_{K₀}) = H^d(Sh)^{K₀}`. The truth argument derives it from
`HarrisCMColimitInvariantsStatement`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Cohomology.HarrisCMPrimeToInvariants

open NumberField _root_.Algebra Langlands.AbelianScheme Langlands.Shimura Langlands.Shimura.PEL
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry Langlands.Geometry.EtalePullback
open Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
open Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

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
  (q : CMRepresentabilityStatement D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})
  (R : Type) [CommRing R]

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "towerEtale" => cmSmallLevelTowerEtale D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion
local notation "coefficients" => cmSmallLevelCoefficientDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "trivialCoefficients" => cmSmallLevelTrivialCoefficients D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "smallColimitCohomology" => cmSmallLevelColimitCohomology D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "primeToComparison" => cmPrimeToCohomologyComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- Prime-to-`m` cohomology as level invariants. Let `R` be a `ℚ`-algebra and `coeff` a
level-trivial diagram of sheaves of `R`-modules on the Library's geometric CM tower all of whose
transition maps are isomorphisms. Let `m ≠ 0` and let `K₀` be a level at the places dividing `m`.
Then in every degree `d`, the Library's comparison from the colimit, over the prime-to-`m` levels
`K'` with `e⁻¹ (K₀ × K')` sufficiently small, of `H^d(X̄_{e⁻¹ (K₀ × K')}, coeff)` to the colimit
over all small levels is injective, and its image is the set of classes fixed by the image in the
finite-adelic group of every element of `K₀`. Here `e` is the splitting `cmPrimeToSplit D m hm`. -/
def HarrisCMPrimeToInvariantsStatement [Algebra ℚ R] : Prop :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  ∀ (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
    (coeff : coefficients), trivialCoefficients coeff →
    (∀ {i j : (SmallCMLevel D)ᵒᵖ} (a : i ⟶ j), IsIso (coeff.map a)) →
    ∀ d : ℕ,
      Function.Injective
          (primeToComparison m hm K₀ existence geometry hRigid criterion R coeff d).hom.hom ∧
        Set.range
            (primeToComparison m hm K₀ existence geometry hRigid criterion R coeff d).hom.hom =
          {z | ∀ k ∈ K₀.subgroup,
            ((smallColimitCohomology coeff d).ρ
              (CompactOpenLevel.factorHom (cmPrimeToSplit D m hm) k)).hom z = z}

end Langlands.Cohomology.HarrisCMPrimeToInvariants
