import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology
import Langlands.Shimura.RestrictedSplitLevelTowerCohomology
import Langlands.Shimura.RestrictedLevelTowerExtension
import Langlands.Shimura.Unitary.OppositePointsSplit

/-! # Prime-to-`m` cohomology of the actual geometric CM tower

For `m ≠ 0`, split `GG(A_f)ᵐᵒᵖ` as the opposite points at the places dividing `m` times the
opposite prime-to-`m` points, and fix a level `K₀` at the places dividing `m`. The actual geometric
CM schemes at the sufficiently small levels `e⁻¹ (K₀ × K')` form a tower over the prime-to-`m`
levels `K'`. Its colimit cohomology carries an action of `GG(A_f^{(m)})ᵐᵒᵖ` and compares with the
shrinking-level cohomology of the CM tower. If `K₀` is sufficiently small at one place dividing
`m`, every prime-to-`m` level occurs. See `HarrisTaylorCMPrimeToCohomology.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry Langlands.Geometry.EtalePullback
open CompactOpenLevel RestrictedSplitLevelTowerCohomology

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

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "small" => D.rationalInvolution.LevelSufficientlySmall
local notation "G" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ

variable (m : ℕ) (hm : m ≠ 0)

/-! ## The splitting at the places dividing `m` and the prime-to-`m` tower -/

section Tower

/-- The splitting of `GG(A_f)ᵐᵒᵖ`, for the rational involution of `D`, as the opposite points at
the places whose prime ideal contains `m` times the opposite prime-to-`m` points. -/
def cmPrimeToSplit :
    G ≃ₜ* (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ × (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  D.rationalInvolution.finiteAdelicPointsOpSplit m hm

/-- A level at the places dividing `m` has no nontrivial element of finite order in its component
at some place whose prime ideal contains `m`. -/
def CMDividingLevelSufficientlySmall
    (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ) : Prop :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  D.rationalInvolution.DividingLevelSufficientlySmall m K₀

variable (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)

/-- The prime-to-`m` levels `K'` for which `e⁻¹ (K₀ × K')` is sufficiently small. -/
abbrev cmPrimeToProperty :
    ObjectProperty (CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) :=
  awayProperty (cmPrimeToSplit D m hm) small K₀

variable {K₀} in
omit [IsCMField F] [IsScalarTower E F A] in
/-- If `K₀` is sufficiently small at a place dividing `m`, every prime-to-`m` level satisfies the
prime-to-`m` property. -/
theorem cmPrimeToProperty_of_dividingSufficientlySmall
    (hK₀ : CMDividingLevelSufficientlySmall D m K₀)
    (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) :
    cmPrimeToProperty D m hm K₀ K' :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  AlgebraInvolution.levelSufficientlySmall_transport_prod (σ := D.rationalInvolution) hm hK₀ K'

/-- The actual geometric CM schemes at the levels `e⁻¹ (K₀ × K')`, as a tower over the
prime-to-`m` levels `K'` in `cmPrimeToProperty D m hm K₀`. -/
abbrev cmPrimeToSchemeTower : (cmPrimeToProperty D m hm K₀).FullSubcategory ⥤ Scheme.{0} :=
  awayLevelTower (cmPrimeToSplit D m hm) K₀ (geometricSchemes)

local notation "primeToSchemes" => cmPrimeToSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀

/-- Each `k ∈ K'` acts on the prime-to-`m` tower at level `K'` by the identity. -/
theorem cmPrimeToSchemeTower_restrictedSelfArrow
    (K' : (cmPrimeToProperty D m hm K₀).FullSubcategory)
    (k : (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) (hk : k ∈ K'.obj.subgroup) :
    (primeToSchemes).map (restrictedSelfArrow (cmPrimeToProperty D m hm K₀) K' k hk) = 𝟙 _ :=
  awayLevelTower_selfArrow (cmPrimeToSplit D m hm) K₀
    (cmGeometricSchemeTower_restrictedSelfArrow D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q) K' k hk

variable {K₀} (hK₀ : CMDividingLevelSufficientlySmall D m K₀)

/-- If `K₀` is sufficiently small at a place dividing `m`, the prime-to-`m` tower is a tower over
all levels of `GG(A_f^{(m)})ᵐᵒᵖ`. -/
abbrev cmPrimeToFullSchemeTower :
    CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ ⥤ Scheme.{0} :=
  RestrictedLevelTowerCohomology.extendTower
    (cmPrimeToProperty_of_dividingSufficientlySmall D m hm hK₀) (primeToSchemes)

end Tower

/-! ## Coefficients and cohomology -/

section Cohomology

variable (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)

local notation "primeToSchemes" => cmPrimeToSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})

include existence geometry hRigid criterion

local notation "towerEtale" => cmSmallLevelTowerEtale D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion

/-- Every transition map of the prime-to-`m` tower is a transition map of the actual geometric
CM tower, hence etale. -/
theorem cmPrimeToTowerEtale :
    ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
  fun a => towerEtale ((awayFunctor (cmPrimeToSplit D m hm) small K₀).map a)

local notation "primeToEtale" => cmPrimeToTowerEtale D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion

variable (R : Type) [CommRing R]

local notation "coefficients" => cmSmallLevelCoefficientDiagram D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "trivialCoefficients" => cmSmallLevelTrivialCoefficients D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "levelCohomology" => cmSmallLevelCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "smallColimitCohomology" => cmSmallLevelColimitCohomology D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R

/-- Compatible module sheaves on the prime-to-`m` tower. -/
abbrev cmPrimeToCoefficientDiagram :=
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  CoefficientDiagram R (primeToSchemes).op

local notation "primeToCoefficients" => cmPrimeToCoefficientDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- The level-triviality property on coefficients on the prime-to-`m` tower. -/
def cmPrimeToTrivialCoefficients : ObjectProperty primeToCoefficients :=
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  RestrictedLevelTowerCohomology.levelTrivialCoefficients (primeToSchemes) R

local notation "primeToTrivialCoefficients" => cmPrimeToTrivialCoefficients D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- Coefficients on the actual geometric CM tower, restricted to the levels `e⁻¹ (K₀ × K')`. -/
def cmPrimeToCoefficients (coeff : coefficients) : primeToCoefficients :=
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  awayCoefficients (cmPrimeToSplit D m hm) K₀ coeff

/-- The restriction of level-trivial coefficients to the prime-to-`m` tower is level-trivial. -/
theorem cmPrimeToCoefficients_trivial {coeff : coefficients}
    (hcoeff : trivialCoefficients coeff) :
    primeToTrivialCoefficients
      (cmPrimeToCoefficients D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
        criterion R coeff) :=
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  isLevelTrivialCoefficients_away (cmPrimeToSplit D m hm) K₀ hcoeff

/-- Degreewise cohomology of coefficients on the prime-to-`m` tower. -/
abbrev cmPrimeToLevelCohomology (coeff' : primeToCoefficients) (d : ℕ) :
    (cmPrimeToProperty D m hm K₀).FullSubcategoryᵒᵖ ⥤ ModuleCat.{0} R :=
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  coeff'.cohomology d

local notation "primeToLevelCohomology" => cmPrimeToLevelCohomology D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- The colimit over the prime-to-`m` levels `K'` with `e⁻¹ (K₀ × K')` sufficiently small of the
degree `d` cohomology of the prime-to-`m` tower, with its action of `GG(A_f^{(m)})ᵐᵒᵖ`. -/
def cmPrimeToColimitCohomology (coeff' : primeToCoefficients) (d : ℕ) :
    Action (ModuleCat.{0} R) (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  exact RestrictedLevelTowerCohomology.colimitCohomology coeff' d

local notation "primeToColimitCohomology" => cmPrimeToColimitCohomology D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- The prime-to-`m` colimit cohomology of level-trivial coefficients, as a smooth
representation of `GG(A_f^{(m)})ᵐᵒᵖ`. -/
def cmPrimeToSmoothCohomology (coeff' : primeToCoefficients)
    (hcoeff' : primeToTrivialCoefficients coeff') (d : ℕ) :
    SmoothRep.{0, 0, 0} R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  exact RestrictedLevelTowerCohomology.smoothColimitCohomology coeff' hcoeff' d

/-! ## Comparison with the shrinking-level cohomology -/

/-- The comparison from the prime-to-`m` colimit cohomology of the restricted coefficients to
the shrinking-level cohomology of the CM tower, equivariant for `GG(A_f^{(m)})ᵐᵒᵖ` acting on the
target through the splitting. -/
def cmPrimeToCohomologyComparison (coeff : coefficients) (d : ℕ) :
    primeToColimitCohomology
        (cmPrimeToCoefficients D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
          criterion R coeff) d ⟶
      (Action.res (ModuleCat.{0} R) (awayHom (cmPrimeToSplit D m hm))).obj
        (smallColimitCohomology coeff d) := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact awayCohomologyComparison (cmPrimeToSplit D m hm) K₀ coeff d

/-- On a class of level `K'`, the comparison is the inclusion of the level `e⁻¹ (K₀ × K')` into
the shrinking-level colimit. -/
theorem ι_cmPrimeToCohomologyComparison (coeff : coefficients) (d : ℕ)
    (K' : (cmPrimeToProperty D m hm K₀).FullSubcategory) :
    RestrictedLevelColimit.ι
        (primeToLevelCohomology
          (cmPrimeToCoefficients D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
            criterion R coeff) d) K' ≫
        (cmPrimeToCohomologyComparison D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
          criterion R coeff d).hom =
      RestrictedLevelColimit.ι (levelCohomology coeff d)
        ((awayFunctor (cmPrimeToSplit D m hm) small K₀).obj K') := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact ι_awayCohomologyComparison (cmPrimeToSplit D m hm) K₀ coeff d K'

/-- For level-trivial coefficients, the image of the comparison is fixed by the elements of
`K₀`, acting through the splitting. -/
theorem cmPrimeToCohomologyComparison_translate_of_mem
    [Nonempty (cmPrimeToProperty D m hm K₀).FullSubcategory] {coeff : coefficients}
    (hcoeff : trivialCoefficients coeff) (d : ℕ)
    {k : (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ} (hk : k ∈ K₀.subgroup)
    (x : (primeToColimitCohomology
      (cmPrimeToCoefficients D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
        criterion R coeff) d).V) :
    ((smallColimitCohomology coeff d).ρ (factorHom (cmPrimeToSplit D m hm) k)).hom
        ((cmPrimeToCohomologyComparison D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
          criterion R coeff d).hom.hom x) =
      (cmPrimeToCohomologyComparison D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
        criterion R coeff d).hom.hom x := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact translate_awayCohomologyComparison_apply_of_mem (cmPrimeToSplit D m hm) K₀ hcoeff d hk x

/-- If every sufficiently small level contains a sufficiently small level `e⁻¹ (K₀ × K')`, the
comparison is an isomorphism. -/
def cmPrimeToCohomologyIso
    (hcof : (awayOver (cmPrimeToSplit D m hm) K₀).IsRestrictedCofinal
      (cmPrimeToProperty D m hm K₀) small)
    (coeff : coefficients) (d : ℕ) :
    primeToColimitCohomology
        (cmPrimeToCoefficients D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
          criterion R coeff) d ≅
      (Action.res (ModuleCat.{0} R) (awayHom (cmPrimeToSplit D m hm))).obj
        (smallColimitCohomology coeff d) := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact awayCohomologyIso (cmPrimeToSplit D m hm) hcof coeff d

theorem cmPrimeToCohomologyIso_hom
    (hcof : (awayOver (cmPrimeToSplit D m hm) K₀).IsRestrictedCofinal
      (cmPrimeToProperty D m hm K₀) small)
    (coeff : coefficients) (d : ℕ) :
    (cmPrimeToCohomologyIso D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
        criterion R hcof coeff d).hom =
      cmPrimeToCohomologyComparison D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
        criterion R coeff d :=
  rfl

end Cohomology

/-! ## The full prime-to-`m` tower -/

section Full

variable {K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ}
  (hK₀ : CMDividingLevelSufficientlySmall D m K₀)

local notation "primeToSchemes" => cmPrimeToSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
local notation "fullSchemes" => cmPrimeToFullSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm hK₀

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})

include existence geometry hRigid criterion

local notation "primeToEtale" => cmPrimeToTowerEtale D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion

variable (R : Type) [CommRing R]

local notation "primeToCoefficients" => cmPrimeToCoefficientDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R
local notation "primeToTrivialCoefficients" => cmPrimeToTrivialCoefficients D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- Compatible module sheaves on the full prime-to-`m` tower. -/
abbrev cmPrimeToFullCoefficientDiagram :=
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  CoefficientDiagram R (fullSchemes).op

local notation "fullCoefficients" => cmPrimeToFullCoefficientDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm hK₀
  existence geometry hRigid criterion R

/-- The level-triviality property on coefficients on the full prime-to-`m` tower. -/
def cmPrimeToFullTrivialCoefficients : ObjectProperty fullCoefficients :=
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  LevelTowerCohomology.levelTrivialCoefficients (fullSchemes) R

local notation "fullTrivialCoefficients" => cmPrimeToFullTrivialCoefficients D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm hK₀
  existence geometry hRigid criterion R

/-- Coefficients on the prime-to-`m` tower, as coefficients on the full prime-to-`m` tower. -/
def cmPrimeToFullCoefficients (coeff' : primeToCoefficients) : fullCoefficients :=
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  RestrictedLevelTowerCohomology.extendCoefficients
    (cmPrimeToProperty_of_dividingSufficientlySmall D m hm hK₀) coeff'

/-- The extension of level-trivial coefficients to the full prime-to-`m` tower is
level-trivial. -/
theorem cmPrimeToFullCoefficients_trivial {coeff' : primeToCoefficients}
    (hcoeff' : primeToTrivialCoefficients coeff') :
    fullTrivialCoefficients
      (cmPrimeToFullCoefficients D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm hK₀ existence geometry hRigid
        criterion R coeff') :=
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  RestrictedLevelTowerCohomology.isLevelTrivialCoefficients_extend
    (cmPrimeToProperty_of_dividingSufficientlySmall D m hm hK₀) hcoeff'

/-- The colimit over all prime-to-`m` levels of the degree `d` cohomology of the full
prime-to-`m` tower, with its action of `GG(A_f^{(m)})ᵐᵒᵖ`. -/
def cmPrimeToFullColimitCohomology (coeff'' : fullCoefficients) (d : ℕ) :
    Action (ModuleCat.{0} R) (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  exact LevelTowerCohomology.colimitCohomology coeff'' d

/-- The colimit over all prime-to-`m` levels of the cohomology of level-trivial coefficients on
the full prime-to-`m` tower, as a smooth representation of `GG(A_f^{(m)})ᵐᵒᵖ`. -/
def cmPrimeToFullSmoothCohomology (coeff'' : fullCoefficients)
    (hcoeff'' : fullTrivialCoefficients coeff'') (d : ℕ) :
    SmoothRep.{0, 0, 0} R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  exact LevelTowerCohomology.smoothColimitCohomology coeff'' hcoeff'' d

/-- If `K₀` is sufficiently small at a place dividing `m` and a prime-to-`m` level exists, the
prime-to-`m` colimit cohomology is the colimit cohomology over all prime-to-`m` levels. -/
def cmPrimeToColimitCohomologyExtendIso
    [Nonempty (CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)]
    (coeff' : primeToCoefficients) (d : ℕ) :
    cmPrimeToColimitCohomology D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
        criterion R coeff' d ≅
      cmPrimeToFullColimitCohomology D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm hK₀ existence geometry hRigid
        criterion R
        (cmPrimeToFullCoefficients D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q m hm hK₀ existence geometry hRigid
          criterion R coeff') d := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  exact RestrictedLevelTowerCohomology.colimitCohomologyExtendIso
    (cmPrimeToProperty_of_dividingSufficientlySmall D m hm hK₀) coeff' d

/-- The same isomorphism of smooth representations for level-trivial coefficients. -/
def cmPrimeToSmoothCohomologyExtendIso
    [Nonempty (CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)]
    (coeff' : primeToCoefficients) (hcoeff' : primeToTrivialCoefficients coeff') (d : ℕ) :
    cmPrimeToSmoothCohomology D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
        criterion R coeff' hcoeff' d ≅
      cmPrimeToFullSmoothCohomology D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm hK₀ existence geometry hRigid
        criterion R
        (cmPrimeToFullCoefficients D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q m hm hK₀ existence geometry hRigid
          criterion R coeff')
        (cmPrimeToFullCoefficients_trivial D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q m hm hK₀ existence geometry hRigid
          criterion R hcoeff') d := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  exact RestrictedLevelTowerCohomology.smoothColimitCohomologyExtendIso
    (cmPrimeToProperty_of_dividingSufficientlySmall D m hm hK₀) coeff' hcoeff' d

end Full

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
