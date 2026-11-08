import Langlands.Shimura.PEL.HarrisTaylorCMFixedVectorGaloisRepresentation
import Langlands.Shimura.HeckeMultiplicityGaloisRepresentation

/-! # Hecke multiplicity spaces of the cohomology of the actual CM tower as Galois representations

For a subgroup `H` of `GG(A_f)ᵐᵒᵖ` and a module `T` over the Hecke algebra of `H`, the Hecke
multiplicity space `Hom_{H(H)}(T, H^d(M)^H)` of the shrinking-level cohomology of the actual
geometric CM tower carries the action of `Gal(F̄/F)` by composition. Assuming the Library
statement that this Galois action on the cohomology is smooth, and that `T` is finitely
generated, the action on the multiplicity space is smooth; over a topological field a
finite-dimensional multiplicity space is a continuous Galois representation of `F`, whose Euler
polynomial at a finite place where the `H`-fixed vectors are unramified is the reversed
characteristic polynomial of composition with the Hecke-linear Frobenius endomorphism. The same
holds for the prime-to-`m` cohomology and its levels `K'`, given the smoothness of its Galois
action. See `HarrisTaylorCMHeckeMultiplicityGaloisRepresentation.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe uT

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry Langlands.Geometry.EtalePullback
open CompactOpenLevel RestrictedSplitLevelTowerCohomology
open Langlands.Geometry.EtaleDerivedSections
open Langlands.GaloisRepresentation (Objects ClosureEmbedding HasEulerPolynomialAt)
open Langlands.Shimura.IsotypicGaloisAction Langlands.Shimura.HeckeMultiplicityGaloisRepresentation
open Langlands.Shimura.FixedVectorGaloisRepresentation (heckeFrobenius)
open Langlands.Shimura.LevelHecke (fixedVectorsActionFunctor LevelHeckeAlgebra)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong
  geometricFrobenius)
open Langlands.Cohomology.HarrisCMLevelGaloisSmooth (HarrisCMLevelGaloisSmoothStatement)

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

local notation "base" => Spec (CommRingCat.of F)

/-! ## Smoothness -/

section Ring

variable (R : Type) [CommRing R]

local notation "galoisCohomologyFunctor" => cmSmallLevelGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "galoisSmooth" => HarrisCMLevelGaloisSmoothStatement D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
  criterion R

section SmallLevel

variable (H : Subgroup D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) (T : Type uT)
  [AddCommGroup T] [Module (LevelHeckeAlgebra R H) T]

/-- Under the Galois smoothness statement, if `T` is finitely generated over the Hecke algebra of
`H`, then `Gal(F̄/F)` acts smoothly on the Hecke multiplicity spaces `Hom_{H(H)}(T, H^d(M)^H)` of
the shrinking-level cohomology. -/
theorem cmSmallLevelHeckeMultiplicity_isSmooth [Module.Finite (LevelHeckeAlgebra R H) T]
    (hsmooth : galoisSmooth) (d : ℕ) (M : ModuleSheaf base R) :
    IsSmooth (heckeMultiplicityRepresentation H T (Field.absoluteGaloisGroup F)
      ((galoisCohomologyFunctor d).obj M)) :=
  isSmooth_heckeMultiplicityRepresentation H T
    (cmSmallLevelGaloisCohomology_isSmooth D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R hsmooth
      d M)

end SmallLevel

section PrimeTo

variable (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) (T : Type uT)
  [AddCommGroup T] [Module (LevelHeckeAlgebra R K'.subgroup) T]

local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- If `Gal(F̄/F)` acts smoothly on the prime-to-`m` cohomology and `T` is finitely generated
over the Hecke algebra of `K'`, then `Gal(F̄/F)` acts smoothly on the Hecke multiplicity spaces
`Hom_{H(K')}(T, H^d(M)^{K'})`. -/
theorem cmPrimeToHeckeMultiplicity_isSmooth [Module.Finite (LevelHeckeAlgebra R K'.subgroup) T]
    (d : ℕ) (M : ModuleSheaf base R)
    (hM : IsSmooth (galoisRepresentation ((primeToGaloisCohomologyFunctor d).obj M))) :
    IsSmooth (heckeMultiplicityRepresentation K'.subgroup T (Field.absoluteGaloisGroup F)
      ((primeToGaloisCohomologyFunctor d).obj M)) :=
  isSmooth_heckeMultiplicityRepresentation K'.subgroup T hM

/-- The geometric Frobenius endomorphism at `w` along `j` of the Hecke multiplicity space is
composition with the Hecke-linear Frobenius endomorphism `cmPrimeToHeckeFrobenius` of the Hecke
module of `K'`-fixed vectors. -/
theorem cmPrimeToHeckeMultiplicity_geometricFrobenius_apply (w : Global.FinitePlace F) (d : ℕ)
    (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (φ : T →ₗ[LevelHeckeAlgebra R K'.subgroup]
      fixedVectors ((primeToGaloisCohomologyFunctor d).obj M).V.representation K'.subgroup) :
    (geometricFrobenius (ModuleCat.{uT} R) w
        ((heckeMultiplicityActionFunctor K'.subgroup T (Field.absoluteGaloisGroup F)).obj
          ((primeToGaloisCohomologyFunctor d).obj M)) j).hom φ =
      (heckeFrobenius (K := F) K'.subgroup ((primeToGaloisCohomologyFunctor d).obj M) w
        j).comp φ :=
  rfl

end PrimeTo

end Ring

/-! ## Continuous Galois representations on shrinking-level Hecke multiplicity spaces -/

section SmallLevelGalois

variable (R : Type) [Field R] [TopologicalSpace R]
  (H : Subgroup D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) (T : Type uT) [AddCommGroup T]
  [Module (LevelHeckeAlgebra R H) T] [Module.Finite (LevelHeckeAlgebra R H) T]

local notation "galoisCohomologyFunctor" => cmSmallLevelGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R

/-- Under the Galois smoothness statement, a finite-dimensional Hecke multiplicity space
`Hom_{H(H)}(T, H^d(M)^H)` of the shrinking-level cohomology over a topological field, as a
continuous Galois representation of `F` with `Gal(F̄/F)` acting by composition. -/
def cmSmallLevelHeckeMultiplicityGaloisRepresentation
    (hsmooth : HarrisCMLevelGaloisSmoothStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R)
    (d : ℕ) (M : ModuleSheaf base R)
    [Module.Finite R (T →ₗ[LevelHeckeAlgebra R H]
      fixedVectors ((galoisCohomologyFunctor d).obj M).V.representation H)] :
    Objects.{0, 0, uT} F R :=
  heckeMultiplicityObjects (K := F) H T ((galoisCohomologyFunctor d).obj M)
    (cmSmallLevelGaloisCohomology_isSmooth D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R hsmooth
      d M)

variable (hsmooth : HarrisCMLevelGaloisSmoothStatement D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
  criterion R) (d : ℕ) (M : ModuleSheaf (Spec (CommRingCat.of F)) R)
  [Module.Finite R (T →ₗ[LevelHeckeAlgebra R H] fixedVectors
    ((cmSmallLevelGaloisCohomologyFunctor D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R
      d).obj M).V.representation H)]

local notation "heckeMultiplicityGalois" => cmSmallLevelHeckeMultiplicityGaloisRepresentation
  D C preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q existence
  geometry hRigid criterion R H T hsmooth d M

/-- The dimension of the Galois representation is that of the Hecke multiplicity space. -/
theorem cmSmallLevelHeckeMultiplicityGaloisRepresentation_rank :
    (heckeMultiplicityGalois).val.rank = Module.finrank R (T →ₗ[LevelHeckeAlgebra R H]
      fixedVectors ((galoisCohomologyFunctor d).obj M).V.representation H) :=
  rfl

variable (w : Global.FinitePlace F)

/-- The Galois representation on the Hecke multiplicity space has Euler polynomial `P` at `w`
exactly when the multiplicity space is unramified at `w` with Frobenius Euler polynomial `P`. -/
theorem cmSmallLevelHeckeMultiplicityGaloisRepresentation_hasEulerPolynomialAt_iff
    {P : R[X]} :
    HasEulerPolynomialAt (heckeMultiplicityGalois) w P ↔
      IsUnramifiedAt (ModuleCat.{uT} R) w
          ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup F)).obj
            ((galoisCohomologyFunctor d).obj M)) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial w
          ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup F)).obj
            ((galoisCohomologyFunctor d).obj M)) = P :=
  hasEulerPolynomialAt_heckeMultiplicityObjects_iff H T ((galoisCohomologyFunctor d).obj M) _ w

/-- If the `H`-fixed vectors of the cohomology are unramified at `w` along `j`, the Galois
representation on the Hecke multiplicity space has as Euler polynomial at `w` the reversed
characteristic polynomial of its geometric Frobenius endomorphism along `j`. -/
theorem
    cmSmallLevelHeckeMultiplicityGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAlong
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : IsUnramifiedAlong (ModuleCat.{0} R) w
      ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) H).obj
        ((galoisCohomologyFunctor d).obj M)) j) :
    HasEulerPolynomialAt (heckeMultiplicityGalois) w
      (geometricFrobenius (ModuleCat.{uT} R) w
        ((heckeMultiplicityActionFunctor H T (Field.absoluteGaloisGroup F)).obj
          ((galoisCohomologyFunctor d).obj M)) j).hom.charpoly.reverse :=
  hasEulerPolynomialAt_heckeMultiplicityObjects_of_isUnramifiedAlong H T _ _ w hu

end SmallLevelGalois

/-! ## Continuous Galois representations on prime-to-`m` Hecke multiplicity spaces -/

section PrimeToGalois

variable (R : Type) [Field R] [TopologicalSpace R]
  (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) (T : Type uT)
  [AddCommGroup T] [Module (LevelHeckeAlgebra R K'.subgroup) T]
  [Module.Finite (LevelHeckeAlgebra R K'.subgroup) T]

local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- If `Gal(F̄/F)` acts smoothly on the prime-to-`m` cohomology, a finite-dimensional Hecke
multiplicity space `Hom_{H(K')}(T, H^d(M)^{K'})` over a topological field, as a continuous
Galois representation of `F` with `Gal(F̄/F)` acting by composition. -/
def cmPrimeToHeckeMultiplicityGaloisRepresentation (d : ℕ) (M : ModuleSheaf base R)
    (hM : IsSmooth (galoisRepresentation ((primeToGaloisCohomologyFunctor d).obj M)))
    [Module.Finite R (T →ₗ[LevelHeckeAlgebra R K'.subgroup]
      fixedVectors ((primeToGaloisCohomologyFunctor d).obj M).V.representation K'.subgroup)] :
    Objects.{0, 0, uT} F R :=
  heckeMultiplicityObjects (K := F) K'.subgroup T ((primeToGaloisCohomologyFunctor d).obj M) hM

variable (d : ℕ) (M : ModuleSheaf (Spec (CommRingCat.of F)) R)
  (hM : IsSmooth (galoisRepresentation ((cmPrimeToGaloisCohomologyFunctor D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q m hm K₀ existence geometry
    hRigid criterion R d).obj M)))
  [Module.Finite R (T →ₗ[LevelHeckeAlgebra R K'.subgroup] fixedVectors
    ((cmPrimeToGaloisCohomologyFunctor D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid criterion R
      d).obj M).V.representation K'.subgroup)]

local notation "primeToHeckeMultiplicityGalois" =>
  cmPrimeToHeckeMultiplicityGaloisRepresentation D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm K₀ K' T
  d M hM

/-- The dimension of the Galois representation is that of the Hecke multiplicity space. -/
theorem cmPrimeToHeckeMultiplicityGaloisRepresentation_rank :
    (primeToHeckeMultiplicityGalois).val.rank =
      Module.finrank R (T →ₗ[LevelHeckeAlgebra R K'.subgroup]
        fixedVectors ((primeToGaloisCohomologyFunctor d).obj M).V.representation K'.subgroup) :=
  rfl

variable (w : Global.FinitePlace F)

/-- The Galois representation on the Hecke multiplicity space has Euler polynomial `P` at `w`
exactly when the multiplicity space is unramified at `w` with Frobenius Euler polynomial `P`. -/
theorem cmPrimeToHeckeMultiplicityGaloisRepresentation_hasEulerPolynomialAt_iff {P : R[X]} :
    HasEulerPolynomialAt (primeToHeckeMultiplicityGalois) w P ↔
      IsUnramifiedAt (ModuleCat.{uT} R) w
          ((heckeMultiplicityActionFunctor K'.subgroup T (Field.absoluteGaloisGroup F)).obj
            ((primeToGaloisCohomologyFunctor d).obj M)) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial w
          ((heckeMultiplicityActionFunctor K'.subgroup T (Field.absoluteGaloisGroup F)).obj
            ((primeToGaloisCohomologyFunctor d).obj M)) = P :=
  hasEulerPolynomialAt_heckeMultiplicityObjects_iff K'.subgroup T
    ((primeToGaloisCohomologyFunctor d).obj M) _ w

/-- If the `K'`-fixed vectors of the prime-to-`m` cohomology are unramified at `w` along `j`, the
Galois representation on the Hecke multiplicity space has as Euler polynomial at `w` the
reversed characteristic polynomial of its geometric Frobenius endomorphism along `j`, which is
composition with the Hecke-linear Frobenius endomorphism `cmPrimeToHeckeFrobenius`. -/
theorem cmPrimeToHeckeMultiplicityGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAlong
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : IsUnramifiedAlong (ModuleCat.{0} R) w
      ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) K'.subgroup).obj
        ((primeToGaloisCohomologyFunctor d).obj M)) j) :
    HasEulerPolynomialAt (primeToHeckeMultiplicityGalois) w
      (geometricFrobenius (ModuleCat.{uT} R) w
        ((heckeMultiplicityActionFunctor K'.subgroup T (Field.absoluteGaloisGroup F)).obj
          ((primeToGaloisCohomologyFunctor d).obj M)) j).hom.charpoly.reverse :=
  hasEulerPolynomialAt_heckeMultiplicityObjects_of_isUnramifiedAlong K'.subgroup T _ _ w hu

end PrimeToGalois

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
