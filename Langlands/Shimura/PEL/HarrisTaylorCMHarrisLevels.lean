import Langlands.Shimura.PEL.HarrisTaylorCMLevelGaloisCohomology
import Langlands.Shimura.Unitary.HarrisPrimeAdelicLevels
import Langlands.Geometry.EtaleInverseImageConstant
import Langlands.Geometry.EtaleConstantCohomology

/-! # Harris's levels `K(N, m)` in the actual CM tower and constant coefficients

For a prime `p`, the place `v` of `ℚ` above it and a level `K_p` of `GG(ℚ_v)`, the opposite of the
level `K_p × K^p` of `GG(A_f)` is the level `e⁻¹ (K₀ × K^pᵐᵒᵖ)` of the prime-to-`p` CM tower, with
the fixed level `K₀` at the places dividing `p` attached to `K_p`. It is sufficiently small as soon
as `K^p` is sufficiently small at one place not dividing `p`. For Harris's `K(N)_p` this places the
schemes `S̄_{K(N, m)}` of Harris 1999, §4, p.309, in the actual geometric CM tower, and gives the
cohomology of a constant sheaf at one level and in the colimit over `K(m)^p`, with the action of
`GG(A_f^p)ᵐᵒᵖ` and of the Galois group. See `HarrisTaylorCMHarrisLevels.md`.
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
open Langlands.Geometry.EtaleDerivedSections

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)

local notation "small" => D.rationalInvolution.LevelSufficientlySmall

/-! ## Levels away from `m` and the levels `K_p × K^p` -/

section Levels

variable (m : ℕ) (hm : m ≠ 0)

/-- A prime-to-`m` level has no nontrivial element of finite order in its component at some
place not dividing `m`. -/
def CMPrimeToLevelSufficientlySmall
    (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) : Prop :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  D.rationalInvolution.PrimeToLevelSufficientlySmall m K'

omit [IsCMField F] [IsScalarTower E F A] in
/-- If `K'` is sufficiently small at a place not dividing `m`, it lies in the prime-to-`m`
property for every level `K₀` at the places dividing `m`. -/
theorem cmPrimeToProperty_of_primeToSufficientlySmall
    (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
    {K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ}
    (hK' : CMPrimeToLevelSufficientlySmall D m K') :
    cmPrimeToProperty D m hm K₀ K' :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  AlgebraInvolution.levelSufficientlySmall_transport_prod_of_primeTo hm K₀ hK'

include hm in
omit [IsCMField F] [IsScalarTower E F A] in
/-- Every level `K'` of `GG(A_f^m)` contains a level whose opposite is sufficiently small at a
place not dividing `m`. -/
theorem exists_cmPrimeToLevelSufficientlySmall_le
    (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)) :
    ∃ L' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m),
      L'.subgroup ≤ K'.subgroup ∧ CMPrimeToLevelSufficientlySmall D m L'.op :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  haveI := D.simple
  AlgebraInvolution.exists_primeToLevelSufficientlySmall_le hm K'

include hm in
omit [IsCMField F] [IsScalarTower E F A] in
/-- A level of `GG(A_f^m)` whose opposite is sufficiently small at a place not dividing `m`
exists. -/
theorem exists_cmPrimeToLevelSufficientlySmall :
    ∃ K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m),
      CMPrimeToLevelSufficientlySmall D m K'.op :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  haveI := D.simple
  D.rationalInvolution.exists_primeToLevelSufficientlySmall hm

variable (p : ℕ) (hp : p.Prime) (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})
  (Kp : CompactOpenLevel (D.rationalInvolution.Points (Global.FiniteCompletion ℚ v.1)))

/-- The level `K_p × K^p` of `GG(A_f)` (`AlgebraInvolution.primeAdelicLevel`). -/
def cmPrimeAdelicLevel (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p)) :
    CompactOpenLevel D.rationalInvolution.FiniteAdelicPoints :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  D.rationalInvolution.primeAdelicLevel p hp v Kp K'

/-- The fixed level `K₀` at the places dividing `p` attached to `K_p`
(`AlgebraInvolution.primeDividingOpLevel`). -/
def cmPrimeDividingLevel : CompactOpenLevel (D.rationalInvolution.DividingPoints p)ᵐᵒᵖ :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  D.rationalInvolution.primeDividingOpLevel p hp v Kp

omit [IsCMField F] [IsScalarTower E F A] in
/-- The level `e⁻¹ (K₀ × K^pᵐᵒᵖ)` of the prime-to-`p` tower is the opposite of `K_p × K^p`. -/
theorem transport_cmPrimeToSplit_symm_prod_cmPrimeDividingLevel
    (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p)) :
    transport (cmPrimeToSplit D p hp.ne_zero).symm
        (prod (cmPrimeDividingLevel D p hp v Kp) K'.op) =
      (cmPrimeAdelicLevel D p hp v Kp K').op :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  D.rationalInvolution.transport_finiteAdelicPointsOpSplit_symm_prod p hp v Kp K'

omit [IsCMField F] [IsScalarTower E F A] in
/-- The opposite `K^pᵐᵒᵖ` lies in the prime-to-`p` property for `K₀` exactly when the opposite of
`K_p × K^p` is sufficiently small. -/
theorem cmPrimeToProperty_op_iff (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p)) :
    cmPrimeToProperty D p hp.ne_zero (cmPrimeDividingLevel D p hp v Kp) K'.op ↔
      small (cmPrimeAdelicLevel D p hp v Kp K').op := by
  rw [cmPrimeToProperty, awayProperty_iff, ← transport_cmPrimeToSplit_symm_prod_cmPrimeDividingLevel]

omit [IsCMField F] [IsScalarTower E F A] in
/-- If `K^p` is sufficiently small at a place not dividing `p`, the opposite of `K_p × K^p` is
sufficiently small, for every level `K_p`. -/
theorem levelSufficientlySmall_cmPrimeAdelicLevel_op
    {K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p)}
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) :
    small (cmPrimeAdelicLevel D p hp v Kp K').op :=
  (cmPrimeToProperty_op_iff D p hp v Kp K').1
    (cmPrimeToProperty_of_primeToSufficientlySmall D p hp.ne_zero _ hK')

/-- The opposite of `K_p × K^p`, as a sufficiently small CM level. -/
def cmPrimeAdelicSmallLevel (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p))
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) : SmallCMLevel D :=
  ⟨(cmPrimeAdelicLevel D p hp v Kp K').op,
    levelSufficientlySmall_cmPrimeAdelicLevel_op D p hp v Kp hK'⟩

/-- The opposite `K^pᵐᵒᵖ`, as a level of the prime-to-`p` tower with fixed level `K₀`. -/
def cmPrimeToLevel (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p))
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) :
    (cmPrimeToProperty D p hp.ne_zero (cmPrimeDividingLevel D p hp v Kp)).FullSubcategory :=
  ⟨K'.op, cmPrimeToProperty_of_primeToSufficientlySmall D p hp.ne_zero _ hK'⟩

omit [IsCMField F] [IsScalarTower E F A] in
/-- The prime-to-`p` level `K^pᵐᵒᵖ` goes to the CM level `(K_p × K^p)ᵐᵒᵖ`. -/
theorem awayFunctor_obj_cmPrimeToLevel
    (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p))
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) :
    (awayFunctor (cmPrimeToSplit D p hp.ne_zero) small (cmPrimeDividingLevel D p hp v Kp)).obj
        (cmPrimeToLevel D p hp v Kp K' hK') =
      cmPrimeAdelicSmallLevel D p hp v Kp K' hK' :=
  ObjectProperty.FullSubcategory.ext
    (transport_cmPrimeToSplit_symm_prod_cmPrimeDividingLevel D p hp v Kp K')

end Levels

/-! ## Harris's levels `K(N, m)` -/

section Harris

open IsDedekindDomain
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality

variable {L : Type} [Field L] [NumberField L] [IsCMField L] [IsQuadraticExtension ℚ L]
  [Algebra L F]
variable (p : ℕ) (hp : p.Prime) (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})
  (𝔭 : FinitePlacesAbove L v.1)
  (h𝔭 : Function.Bijective (FiniteExtension.completionMap v.1 𝔭.1))
  (hdiv : ∀ w : (letI := (algebraMap L F).toAlgebra; FinitePlacesAbove F 𝔭.1), IsDivisionAt A w.1)
  (w₀ : letI := (algebraMap L F).toAlgebra; FinitePlacesAbove F 𝔭.1) (r : ℝ) (hr0 : 0 < r)
  (hr : r < 1)

/-- Harris's level `K(N)_p` of `GG(ℚ_v)` for the rational involution of `D`, with the imaginary
quadratic field `L ⊆ F` and congruence radius `r` (`SecondKindInvolution.harrisLevel`). -/
def cmHarrisLevel : CompactOpenLevel (D.rationalInvolution.Points (Global.FiniteCompletion ℚ v.1)) :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  D.toSecondKindInvolution.harrisLevel (algebraMap L F) v.1 𝔭 h𝔭 hdiv w₀ r hr0 hr

/-- Harris's level `K(N, m) = K(N)_p × K(m)^p` of `GG(A_f)` (Harris 1999, §4, p.309). -/
abbrev cmHarrisAdelicLevel (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p)) :
    CompactOpenLevel D.rationalInvolution.FiniteAdelicPoints :=
  cmPrimeAdelicLevel D p hp v (cmHarrisLevel D p v 𝔭 h𝔭 hdiv w₀ r hr0 hr) K'

omit [IsCMField F] [IsScalarTower E F A] in
/-- This is the published `SecondKindInvolution.harrisPrimeAdelicLevel`. -/
theorem cmHarrisAdelicLevel_eq (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p)) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    cmHarrisAdelicLevel D p hp v 𝔭 h𝔭 hdiv w₀ r hr0 hr K' =
      D.toSecondKindInvolution.harrisPrimeAdelicLevel (algebraMap L F) p hp v 𝔭 h𝔭 hdiv w₀ r hr0 hr K' :=
  rfl

/-- The fixed level `K₀` at the places dividing `p` attached to `K(N)_p`. -/
abbrev cmHarrisDividingLevel : CompactOpenLevel (D.rationalInvolution.DividingPoints p)ᵐᵒᵖ :=
  cmPrimeDividingLevel D p hp v (cmHarrisLevel D p v 𝔭 h𝔭 hdiv w₀ r hr0 hr)

/-- The opposite of Harris's `K(N, m)`, for `K(m)^p` sufficiently small at a place not dividing
`p`, as a sufficiently small CM level. -/
abbrev cmHarrisSmallLevel (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p))
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) : SmallCMLevel D :=
  cmPrimeAdelicSmallLevel D p hp v (cmHarrisLevel D p v 𝔭 h𝔭 hdiv w₀ r hr0 hr) K' hK'

end Harris

/-! ## The CM schemes and constant coefficients at `K_p × K^p` -/

section Cohomology

variable {L : Type} [Field L] [NumberField L] [IsCMField L]
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
local notation "arithmeticGeometricStructure" => cmSmallLevelArithmeticGeometricStructure D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
local notation "base" => Spec (CommRingCat.of F)
local notation "Gamma" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)

variable (p : ℕ) (hp : p.Prime) (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})
  (Kp : CompactOpenLevel (D.rationalInvolution.Points (Global.FiniteCompletion ℚ v.1)))

local notation "primeToSchemes" => cmPrimeToSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p hp.ne_zero
  (cmPrimeDividingLevel D p hp v Kp)
local notation "primeToStructure" => cmPrimeToArithmeticStructure D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p hp.ne_zero
  (cmPrimeDividingLevel D p hp v Kp)

/-- At the prime-to-`p` level `K^pᵐᵒᵖ`, the prime-to-`p` tower is the actual geometric CM scheme
at the level `(K_p × K^p)ᵐᵒᵖ`. -/
theorem cmPrimeToSchemeTower_obj_cmPrimeToLevel
    (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p))
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) :
    (primeToSchemes).obj (cmPrimeToLevel D p hp v Kp K' hK') =
      (geometricSchemes).obj (cmPrimeAdelicSmallLevel D p hp v Kp K' hK') :=
  congrArg (geometricSchemes).obj (awayFunctor_obj_cmPrimeToLevel D p hp v Kp K' hK')

/-- At the prime-to-`p` level `K^pᵐᵒᵖ`, the projection of the prime-to-`p` tower to `Spec F` is
the projection of the actual geometric CM scheme at the level `(K_p × K^p)ᵐᵒᵖ`. -/
theorem cmPrimeToArithmeticStructure_app_cmPrimeToLevel
    (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p))
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) :
    (primeToStructure).app (cmPrimeToLevel D p hp v Kp K' hK') =
      eqToHom (cmPrimeToSchemeTower_obj_cmPrimeToLevel D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor q p hp v Kp K' hK') ≫
        (arithmeticGeometricStructure).app (cmPrimeAdelicSmallLevel D p hp v Kp K' hK') := by
  rw [cmPrimeToArithmeticStructure_app]
  have key : ∀ {U V : SmallCMLevel D} (hUV : U = V),
      (arithmeticGeometricStructure).app U =
        eqToHom (congrArg (geometricSchemes).obj hUV) ≫ (arithmeticGeometricStructure).app V := by
    rintro U V rfl
    simp
  exact key (awayFunctor_obj_cmPrimeToLevel D p hp v Kp K' hK')

variable (R : Type) [CommRing R]

/-- On every scheme `X` over `Spec F`, the inverse image of the constant sheaf with value `𝓛` on
`Spec F` is the constant sheaf with value `𝓛`. -/
def constantInverseImageIso {X : Scheme.{0}} (f : X ⟶ base) (𝓛 : ModuleCat.{0} R) :
    (EtaleInverseImage.inverseImage f R).obj (EtaleCohomologyAction.constant R 𝓛) ≅
      EtaleCohomologyAction.constant R 𝓛 :=
  (EtaleInverseImage.inverseImageConstantIso f R).app 𝓛

/-- The cohomology `H^d(S̄_U, 𝓛)` of the constant sheaf with value `𝓛` on the actual geometric CM
scheme at the level `(K_p × K^p)ᵐᵒᵖ`, with the action of `Gal(F̄/F)`; the coefficients are the
inverse image of the constant sheaf on `Spec F`, which is constant (`constantInverseImageIso`). -/
def cmPrimeAdelicConstantCohomology
    (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p))
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) (𝓛 : ModuleCat.{0} R) (d : ℕ) :
    Action (ModuleCat.{0} R) Gamma :=
  (cmLevelGaloisCohomologyFunctor D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q R (cmPrimeAdelicSmallLevel D p hp v Kp K' hK') d).obj
    (EtaleCohomologyAction.constant R 𝓛)

/-- Its underlying module is the cohomology of the inverse image of the constant sheaf. -/
theorem cmPrimeAdelicConstantCohomology_V
    (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p))
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) (𝓛 : ModuleCat.{0} R) (d : ℕ) :
    (cmPrimeAdelicConstantCohomology D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q p hp v Kp R K' hK' 𝓛 d).V =
      (cohomology ((geometricSchemes).obj (cmPrimeAdelicSmallLevel D p hp v Kp K' hK')) R d).obj
        ((EtaleInverseImage.inverseImage
          ((arithmeticGeometricStructure).app (cmPrimeAdelicSmallLevel D p hp v Kp K' hK')) R).obj
          (EtaleCohomologyAction.constant R 𝓛)) :=
  rfl

/-- The underlying module is the cohomology `H^d(S̄_U, 𝓛)` of the constant sheaf. -/
def cmPrimeAdelicConstantCohomologyIso
    (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p))
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) (𝓛 : ModuleCat.{0} R) (d : ℕ) :
    (cmPrimeAdelicConstantCohomology D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q p hp v Kp R K' hK' 𝓛 d).V ≅
      (cohomology ((geometricSchemes).obj (cmPrimeAdelicSmallLevel D p hp v Kp K' hK')) R d).obj
        (EtaleCohomologyAction.constant R 𝓛) :=
  (cohomology _ R d).mapIso (constantInverseImageIso R _ 𝓛)

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})

/-- The colimit over `K^p` of the cohomology `H^d(S̄_{K_p × K^p}, 𝓛)` of the constant sheaf with
value `𝓛`, as a smooth representation of `GG(A_f^p)ᵐᵒᵖ` with the commuting action of `Gal(F̄/F)`:
the prime-to-`p` Galois cohomology functor with fixed level `K₀ = cmPrimeDividingLevel K_p`,
applied to the constant sheaf on `Spec F`. -/
def cmPrimeAdelicConstantGaloisCohomology (𝓛 : ModuleCat.{0} R) (d : ℕ) :
    Action (SmoothRep.{0, 0, 0} R (D.rationalInvolution.PrimeToPoints p)ᵐᵒᵖ) Gamma :=
  (cmPrimeToGaloisCohomologyFunctor D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q p hp.ne_zero (cmPrimeDividingLevel D p hp v Kp) existence geometry
    hRigid criterion R d).obj (EtaleCohomologyAction.constant R 𝓛)

/-! ### Harris's `K(N, m)` -/

section HarrisCohomology

open IsDedekindDomain
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality

variable (𝔭 : FinitePlacesAbove L v.1)
  (h𝔭 : Function.Bijective (FiniteExtension.completionMap v.1 𝔭.1))
  (hdiv : ∀ w : (letI := (algebraMap L F).toAlgebra; FinitePlacesAbove F 𝔭.1), IsDivisionAt A w.1)
  (w₀ : letI := (algebraMap L F).toAlgebra; FinitePlacesAbove F 𝔭.1) (r : ℝ) (hr0 : 0 < r)
  (hr : r < 1)

/-- The actual geometric CM scheme `X_U ×_F F̄` at the level `U = K(N, m)ᵐᵒᵖ`, where
`K(N, m) = K(N)_p × K(m)^p` and `K(m)^p` is sufficiently small at a place not dividing `p`. This
is the CM-tower counterpart of Harris's `S̄_{K(N, m)}` (Harris 1999, §4, p.309); no comparison
with Harris's canonical model is made. -/
abbrev cmHarrisGeometricScheme (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p))
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) : Scheme.{0} :=
  (geometricSchemes).obj (cmHarrisSmallLevel D p hp v 𝔭 h𝔭 hdiv w₀ r hr0 hr K' hK')

/-- The cohomology `H^d(X_U ×_F F̄, 𝓛)` of the constant sheaf with value `𝓛` at the level
`U = K(N, m)ᵐᵒᵖ`, with the action of `Gal(F̄/F)`: the CM-tower counterpart of Harris's
`H^d(S̄_{K(N, m)}, 𝓛̃)`. -/
abbrev cmHarrisConstantCohomology (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints p))
    (hK' : CMPrimeToLevelSufficientlySmall D p K'.op) (𝓛 : ModuleCat.{0} R) (d : ℕ) :
    Action (ModuleCat.{0} R) Gamma :=
  cmPrimeAdelicConstantCohomology D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q p hp v (cmHarrisLevel D p v 𝔭 h𝔭 hdiv w₀ r hr0 hr) R K' hK' 𝓛 d

/-- The colimit over `K(m)^p` of the cohomology `H^d(X_{K(N, m)ᵐᵒᵖ} ×_F F̄, 𝓛)` of the constant
sheaf, as a smooth representation of `GG(A_f^p)ᵐᵒᵖ` with the commuting action of `Gal(F̄/F)`. -/
abbrev cmHarrisConstantGaloisCohomology (𝓛 : ModuleCat.{0} R) (d : ℕ) :
    Action (SmoothRep.{0, 0, 0} R (D.rationalInvolution.PrimeToPoints p)ᵐᵒᵖ) Gamma :=
  cmPrimeAdelicConstantGaloisCohomology D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q p hp v (cmHarrisLevel D p v 𝔭 h𝔭 hdiv w₀ r hr0 hr) R existence
    geometry hRigid criterion 𝓛 d

end HarrisCohomology

end Cohomology

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
