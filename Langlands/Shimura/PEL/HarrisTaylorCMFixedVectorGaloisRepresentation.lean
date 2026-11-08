import Langlands.Shimura.PEL.HarrisTaylorCMMultiplicityGaloisRepresentation
import Langlands.Shimura.PEL.HarrisTaylorCMIsotypicDecompositionCohomology
import Langlands.Shimura.FixedVectorGaloisRepresentation

/-! # Fixed vectors of the cohomology of the actual CM tower as Galois representations

Assuming the Library statement that `Gal(F̄/F)` acts smoothly on the shrinking-level cohomology
of the actual geometric CM tower, the Galois action on the `H`-fixed vectors of the cohomology
and of each of its isotypic parts is smooth, for every subgroup `H` of `GG(A_f)ᵐᵒᵖ`. Over a
topological field, finite-dimensional fixed vectors are then continuous Galois representations of
`F`, with Euler polynomial at a finite place where the cohomology is unramified the reversed
characteristic polynomial of the geometric Frobenius endomorphism. For the prime-to-`m`
cohomology, given the smoothness of its Galois action, the same holds for the `K'`-fixed vectors
of the cohomology and of its isotypic parts, and the Frobenius endomorphism is the Hecke-linear
Frobenius endomorphism of the Hecke modules of `K'`-fixed vectors, with scalars restricted. See
`HarrisTaylorCMFixedVectorGaloisRepresentation.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe uU

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry Langlands.Geometry.EtalePullback
open CompactOpenLevel RestrictedSplitLevelTowerCohomology
open Langlands.Geometry.EtaleDerivedSections
open Langlands.GaloisRepresentation (Objects ClosureEmbedding HasEulerPolynomialAt)
open Langlands.Shimura.IsotypicGaloisAction Langlands.Shimura.FixedVectorGaloisRepresentation
open Langlands.Shimura.LevelHecke (fixedVectorsActionFunctor)
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

/-! ## Smoothness and Frobenius endomorphisms -/

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

variable (H : Subgroup D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)

/-- Under the Galois smoothness statement, `Gal(F̄/F)` acts smoothly on the `H`-fixed vectors of
the shrinking-level cohomology. -/
theorem cmSmallLevelFixedVectors_isSmooth (hsmooth : galoisSmooth) (d : ℕ)
    (M : ModuleSheaf base R) :
    IsSmooth ((Rep.ActionToRep R (Field.absoluteGaloisGroup F)).obj
      ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) H).obj
        ((galoisCohomologyFunctor d).obj M))).ρ :=
  isSmooth_fixedVectors H
    (cmSmallLevelGaloisCohomology_isSmooth D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R hsmooth
      d M)

variable {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ U)

/-- Under the Galois smoothness statement, `Gal(F̄/F)` acts smoothly on the `H`-fixed vectors of
every isotypic part of the shrinking-level cohomology. -/
theorem cmSmallLevelIsotypicFixedVectors_isSmooth (hsmooth : galoisSmooth) (d : ℕ)
    (M : ModuleSheaf base R) :
    IsSmooth ((Rep.ActionToRep R (Field.absoluteGaloisGroup F)).obj
      ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) H).obj
        ((cmSmallLevelIsotypicCohomologyFunctor D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid criterion R ξ
          d).obj M))).ρ :=
  isSmooth_fixedVectors H
    (cmSmallLevelIsotypicCohomology_isSmooth D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R ξ
      hsmooth d M)

end SmallLevel

section PrimeTo

variable (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)

local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- If `Gal(F̄/F)` acts smoothly on the prime-to-`m` cohomology, it acts smoothly on the
`K'`-fixed vectors. -/
theorem cmPrimeToFixedVectors_isSmooth (d : ℕ) (M : ModuleSheaf base R)
    (hM : IsSmooth (galoisRepresentation ((primeToGaloisCohomologyFunctor d).obj M))) :
    IsSmooth ((Rep.ActionToRep R (Field.absoluteGaloisGroup F)).obj
      ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) K'.subgroup).obj
        ((primeToGaloisCohomologyFunctor d).obj M))).ρ :=
  isSmooth_fixedVectors K'.subgroup hM

/-- The Frobenius endomorphism of the Hecke module of `K'`-fixed vectors of the prime-to-`m`
cohomology is the Hecke-linear Frobenius endomorphism of the generic construction. -/
theorem cmPrimeToHeckeFrobenius_hom_eq (w : Global.FinitePlace F) (d : ℕ)
    (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    (cmPrimeToHeckeFrobenius D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm
        K₀ w K' d M j).hom =
      heckeFrobenius (K := F) K'.subgroup ((primeToGaloisCohomologyFunctor d).obj M) w j :=
  rfl

variable {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ U)

/-- If `Gal(F̄/F)` acts smoothly on the prime-to-`m` cohomology, it acts smoothly on the
`K'`-fixed vectors of every isotypic part. -/
theorem cmPrimeToIsotypicFixedVectors_isSmooth (d : ℕ) (M : ModuleSheaf base R)
    (hM : IsSmooth (galoisRepresentation ((primeToGaloisCohomologyFunctor d).obj M))) :
    IsSmooth ((Rep.ActionToRep R (Field.absoluteGaloisGroup F)).obj
      ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) K'.subgroup).obj
        ((cmPrimeToIsotypicCohomologyFunctor D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm
          K₀ ξ d).obj M))).ρ :=
  isSmooth_fixedVectors K'.subgroup
    (cmPrimeToIsotypicCohomology_isSmooth D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm K₀
      ξ d M hM)

/-- The Frobenius endomorphism of the Hecke module of `K'`-fixed vectors of the `ξ`-isotypic
part is the Hecke-linear Frobenius endomorphism of the generic construction. -/
theorem cmPrimeToIsotypicHeckeFrobenius_hom_eq (w : Global.FinitePlace F) (d : ℕ)
    (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    (cmPrimeToIsotypicHeckeFrobenius D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm
        K₀ ξ w K' d M j).hom =
      heckeFrobenius (K := F) K'.subgroup
        ((cmPrimeToIsotypicCohomologyFunctor D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm
          K₀ ξ d).obj M) w j :=
  rfl

end PrimeTo

end Ring

/-! ## Continuous Galois representations on fixed vectors of the shrinking-level cohomology -/

section SmallLevelGalois

variable (R : Type) [Field R] [TopologicalSpace R]
  (H : Subgroup D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)

local notation "galoisCohomologyFunctor" => cmSmallLevelGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R

/-- Under the Galois smoothness statement, finite-dimensional `H`-fixed vectors of the
shrinking-level cohomology over a topological field, as a continuous Galois representation of
`F`. -/
def cmSmallLevelFixedVectorGaloisRepresentation
    (hsmooth : HarrisCMLevelGaloisSmoothStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R)
    (d : ℕ) (M : ModuleSheaf base R)
    [Module.Finite R (fixedVectors ((galoisCohomologyFunctor d).obj M).V.representation H)] :
    Objects.{0, 0, 0} F R :=
  fixedVectorsObjects (K := F) H ((galoisCohomologyFunctor d).obj M)
    (cmSmallLevelGaloisCohomology_isSmooth D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R hsmooth
      d M)

variable (hsmooth : HarrisCMLevelGaloisSmoothStatement D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
  criterion R) (d : ℕ) (M : ModuleSheaf (Spec (CommRingCat.of F)) R)
  [Module.Finite R (fixedVectors
    ((cmSmallLevelGaloisCohomologyFunctor D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R
      d).obj M).V.representation H)]

local notation "fixedVectorGalois" => cmSmallLevelFixedVectorGaloisRepresentation D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q existence
  geometry hRigid criterion R H hsmooth d M

/-- The dimension of the Galois representation is that of the fixed vectors. -/
theorem cmSmallLevelFixedVectorGaloisRepresentation_rank :
    (fixedVectorGalois).val.rank =
      Module.finrank R (fixedVectors ((galoisCohomologyFunctor d).obj M).V.representation H) :=
  rfl

variable (w : Global.FinitePlace F)

/-- The Galois representation on the fixed vectors has Euler polynomial `P` at `w` exactly when
the fixed vectors are unramified at `w` with Frobenius Euler polynomial `P`. -/
theorem cmSmallLevelFixedVectorGaloisRepresentation_hasEulerPolynomialAt_iff {P : R[X]} :
    HasEulerPolynomialAt (fixedVectorGalois) w P ↔
      IsUnramifiedAt (ModuleCat.{0} R) w
          ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) H).obj
            ((galoisCohomologyFunctor d).obj M)) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial w
          ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) H).obj
            ((galoisCohomologyFunctor d).obj M)) = P :=
  hasEulerPolynomialAt_fixedVectorsObjects_iff H ((galoisCohomologyFunctor d).obj M) _ w

/-- If the fixed vectors are unramified at `w` along `j`, the Galois representation on them has
as Euler polynomial at `w` the reversed characteristic polynomial of their geometric Frobenius
endomorphism along `j`. -/
theorem cmSmallLevelFixedVectorGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAlong
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : IsUnramifiedAlong (ModuleCat.{0} R) w
      ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) H).obj
        ((galoisCohomologyFunctor d).obj M)) j) :
    HasEulerPolynomialAt (fixedVectorGalois) w
      (geometricFrobenius (ModuleCat.{0} R) w
        ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) H).obj
          ((galoisCohomologyFunctor d).obj M)) j).hom.charpoly.reverse :=
  hasEulerPolynomialAt_fixedVectorsObjects_of_isUnramifiedAlong H _ _ w hu

end SmallLevelGalois

/-! ## Continuous Galois representations on fixed vectors of isotypic parts -/

section SmallLevelIsotypicGalois

variable (R : Type) [Field R] [TopologicalSpace R]
  (H : Subgroup D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)
  {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ U)

local notation "galoisCohomologyFunctor" => cmSmallLevelGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "isotypicCohomology" => cmSmallLevelIsotypicCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R ξ

/-- Under the Galois smoothness statement, finite-dimensional `H`-fixed vectors of the
`ξ`-isotypic part of the shrinking-level cohomology over a topological field, as a continuous
Galois representation of `F`. -/
def cmSmallLevelIsotypicFixedVectorGaloisRepresentation
    (hsmooth : HarrisCMLevelGaloisSmoothStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R)
    (d : ℕ) (M : ModuleSheaf base R)
    [Module.Finite R (fixedVectors ((isotypicCohomology d).obj M).V.representation H)] :
    Objects.{0, 0, 0} F R :=
  fixedVectorsObjects (K := F) H ((isotypicCohomology d).obj M)
    (cmSmallLevelIsotypicCohomology_isSmooth D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R ξ
      hsmooth d M)

variable (hsmooth : HarrisCMLevelGaloisSmoothStatement D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
  criterion R) (d : ℕ) (M : ModuleSheaf (Spec (CommRingCat.of F)) R)
  [Module.Finite R (fixedVectors
    ((cmSmallLevelIsotypicCohomologyFunctor D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R ξ
      d).obj M).V.representation H)]

local notation "isotypicFixedVectorGalois" => cmSmallLevelIsotypicFixedVectorGaloisRepresentation
  D C preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q existence
  geometry hRigid criterion R H ξ hsmooth d M

/-- The dimension of the Galois representation is that of the fixed vectors. -/
theorem cmSmallLevelIsotypicFixedVectorGaloisRepresentation_rank :
    (isotypicFixedVectorGalois).val.rank =
      Module.finrank R (fixedVectors ((isotypicCohomology d).obj M).V.representation H) :=
  rfl

variable (w : Global.FinitePlace F)

/-- The Galois representation on the fixed vectors of the isotypic part has Euler polynomial `P`
at `w` exactly when these fixed vectors are unramified at `w` with Frobenius Euler polynomial
`P`. -/
theorem cmSmallLevelIsotypicFixedVectorGaloisRepresentation_hasEulerPolynomialAt_iff
    {P : R[X]} :
    HasEulerPolynomialAt (isotypicFixedVectorGalois) w P ↔
      IsUnramifiedAt (ModuleCat.{0} R) w
          ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) H).obj
            ((isotypicCohomology d).obj M)) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial w
          ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) H).obj
            ((isotypicCohomology d).obj M)) = P :=
  hasEulerPolynomialAt_fixedVectorsObjects_iff H ((isotypicCohomology d).obj M) _ w

/-- If the `H`-fixed vectors of the cohomology are unramified at `w` along `j`, the Galois
representation on the `H`-fixed vectors of the isotypic part has as Euler polynomial at `w` the
reversed characteristic polynomial of the geometric Frobenius endomorphism of these fixed vectors
along `j`. -/
theorem
    cmSmallLevelIsotypicFixedVectorGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAlong
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : IsUnramifiedAlong (ModuleCat.{0} R) w
      ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) H).obj
        ((galoisCohomologyFunctor d).obj M)) j) :
    HasEulerPolynomialAt (isotypicFixedVectorGalois) w
      (geometricFrobenius (ModuleCat.{0} R) w
        ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) H).obj
          ((isotypicCohomology d).obj M)) j).hom.charpoly.reverse :=
  hasEulerPolynomialAt_fixedVectorsObjects_of_isUnramifiedAlong H _ _ w
    (isUnramifiedAlong_fixedVectors_isotypic H ((galoisCohomologyFunctor d).obj M) ξ hu)

end SmallLevelIsotypicGalois

/-! ## Continuous Galois representations on fixed vectors of the prime-to-`m` cohomology -/

section PrimeToGalois

variable (R : Type) [Field R] [TopologicalSpace R]
  (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)

local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- If `Gal(F̄/F)` acts smoothly on the prime-to-`m` cohomology, finite-dimensional `K'`-fixed
vectors over a topological field, as a continuous Galois representation of `F`. -/
def cmPrimeToFixedVectorGaloisRepresentation (d : ℕ) (M : ModuleSheaf base R)
    (hM : IsSmooth (galoisRepresentation ((primeToGaloisCohomologyFunctor d).obj M)))
    [Module.Finite R
      (fixedVectors ((primeToGaloisCohomologyFunctor d).obj M).V.representation K'.subgroup)] :
    Objects.{0, 0, 0} F R :=
  fixedVectorsObjects (K := F) K'.subgroup ((primeToGaloisCohomologyFunctor d).obj M) hM

variable (d : ℕ) (M : ModuleSheaf (Spec (CommRingCat.of F)) R)
  (hM : IsSmooth (galoisRepresentation ((cmPrimeToGaloisCohomologyFunctor D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q m hm K₀ existence geometry
    hRigid criterion R d).obj M)))
  [Module.Finite R (fixedVectors ((cmPrimeToGaloisCohomologyFunctor D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q m hm K₀ existence geometry
    hRigid criterion R d).obj M).V.representation K'.subgroup)]

local notation "primeToFixedVectorGalois" => cmPrimeToFixedVectorGaloisRepresentation D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q existence
  geometry hRigid criterion R m hm K₀ K' d M hM

/-- The dimension of the Galois representation is that of the fixed vectors. -/
theorem cmPrimeToFixedVectorGaloisRepresentation_rank :
    (primeToFixedVectorGalois).val.rank = Module.finrank R
      (fixedVectors ((primeToGaloisCohomologyFunctor d).obj M).V.representation K'.subgroup) :=
  rfl

variable (w : Global.FinitePlace F)

/-- The Galois representation on the `K'`-fixed vectors has Euler polynomial `P` at `w` exactly
when the fixed vectors are unramified at `w` with Frobenius Euler polynomial `P`. -/
theorem cmPrimeToFixedVectorGaloisRepresentation_hasEulerPolynomialAt_iff {P : R[X]} :
    HasEulerPolynomialAt (primeToFixedVectorGalois) w P ↔
      IsUnramifiedAt (ModuleCat.{0} R) w
          ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) K'.subgroup).obj
            ((primeToGaloisCohomologyFunctor d).obj M)) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial w
          ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) K'.subgroup).obj
            ((primeToGaloisCohomologyFunctor d).obj M)) = P :=
  hasEulerPolynomialAt_fixedVectorsObjects_iff K'.subgroup
    ((primeToGaloisCohomologyFunctor d).obj M) _ w

/-- If the `K'`-fixed vectors are unramified at `w` along `j`, the Galois representation on them
has as Euler polynomial at `w` the reversed characteristic polynomial over `R` of the
Hecke-linear Frobenius endomorphism `cmPrimeToHeckeFrobenius` of the Hecke module of `K'`-fixed
vectors along `j`. -/
theorem cmPrimeToFixedVectorGaloisRepresentation_hasEulerPolynomialAt_heckeFrobenius
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : IsUnramifiedAlong (ModuleCat.{0} R) w
      ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) K'.subgroup).obj
        ((primeToGaloisCohomologyFunctor d).obj M)) j) :
    HasEulerPolynomialAt (primeToFixedVectorGalois) w
      ((heckeFrobenius (K := F) K'.subgroup ((primeToGaloisCohomologyFunctor d).obj M) w
        j).restrictScalars R).charpoly.reverse :=
  hasEulerPolynomialAt_fixedVectorsObjects_heckeFrobenius K'.subgroup _ hM w hu

end PrimeToGalois

/-! ## Continuous Galois representations on fixed vectors of prime-to-`m` isotypic parts -/

section PrimeToIsotypicGalois

variable (R : Type) [Field R] [TopologicalSpace R]
  (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)
  {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ U)

local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R
local notation "primeToIsotypicCohomology" => cmPrimeToIsotypicCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R m hm K₀ ξ

/-- If `Gal(F̄/F)` acts smoothly on the prime-to-`m` cohomology, finite-dimensional `K'`-fixed
vectors of the `ξ`-isotypic part over a topological field, as a continuous Galois representation
of `F`. -/
def cmPrimeToIsotypicFixedVectorGaloisRepresentation (d : ℕ) (M : ModuleSheaf base R)
    (hM : IsSmooth (galoisRepresentation ((primeToGaloisCohomologyFunctor d).obj M)))
    [Module.Finite R
      (fixedVectors ((primeToIsotypicCohomology d).obj M).V.representation K'.subgroup)] :
    Objects.{0, 0, 0} F R :=
  fixedVectorsObjects (K := F) K'.subgroup ((primeToIsotypicCohomology d).obj M)
    (cmPrimeToIsotypicCohomology_isSmooth D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm K₀
      ξ d M hM)

variable (d : ℕ) (M : ModuleSheaf (Spec (CommRingCat.of F)) R)
  (hM : IsSmooth (galoisRepresentation ((cmPrimeToGaloisCohomologyFunctor D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q m hm K₀ existence geometry
    hRigid criterion R d).obj M)))
  [Module.Finite R (fixedVectors ((cmPrimeToIsotypicCohomologyFunctor D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
    criterion R m hm K₀ ξ d).obj M).V.representation K'.subgroup)]

local notation "primeToIsotypicFixedVectorGalois" =>
  cmPrimeToIsotypicFixedVectorGaloisRepresentation D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm K₀ K'
  ξ d M hM

/-- The dimension of the Galois representation is that of the fixed vectors. -/
theorem cmPrimeToIsotypicFixedVectorGaloisRepresentation_rank :
    (primeToIsotypicFixedVectorGalois).val.rank = Module.finrank R
      (fixedVectors ((primeToIsotypicCohomology d).obj M).V.representation K'.subgroup) :=
  rfl

variable (w : Global.FinitePlace F)

/-- The Galois representation on the `K'`-fixed vectors of the isotypic part has Euler
polynomial `P` at `w` exactly when these fixed vectors are unramified at `w` with Frobenius Euler
polynomial `P`. -/
theorem cmPrimeToIsotypicFixedVectorGaloisRepresentation_hasEulerPolynomialAt_iff {P : R[X]} :
    HasEulerPolynomialAt (primeToIsotypicFixedVectorGalois) w P ↔
      IsUnramifiedAt (ModuleCat.{0} R) w
          ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) K'.subgroup).obj
            ((primeToIsotypicCohomology d).obj M)) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial w
          ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) K'.subgroup).obj
            ((primeToIsotypicCohomology d).obj M)) = P :=
  hasEulerPolynomialAt_fixedVectorsObjects_iff K'.subgroup
    ((primeToIsotypicCohomology d).obj M) _ w

/-- If the `K'`-fixed vectors of the prime-to-`m` cohomology are unramified at `w` along `j`, the
Galois representation on the `K'`-fixed vectors of the isotypic part has as Euler polynomial at
`w` the reversed characteristic polynomial over `R` of the Hecke-linear Frobenius endomorphism
`cmPrimeToIsotypicHeckeFrobenius` of the Hecke module of these fixed vectors along `j`. -/
theorem cmPrimeToIsotypicFixedVectorGaloisRepresentation_hasEulerPolynomialAt_heckeFrobenius
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : IsUnramifiedAlong (ModuleCat.{0} R) w
      ((fixedVectorsActionFunctor R (Field.absoluteGaloisGroup F) K'.subgroup).obj
        ((primeToGaloisCohomologyFunctor d).obj M)) j) :
    HasEulerPolynomialAt (primeToIsotypicFixedVectorGalois) w
      ((heckeFrobenius (K := F) K'.subgroup ((primeToIsotypicCohomology d).obj M) w
        j).restrictScalars R).charpoly.reverse :=
  hasEulerPolynomialAt_fixedVectorsObjects_heckeFrobenius K'.subgroup _ _ w
    (isUnramifiedAlong_fixedVectors_isotypic K'.subgroup
      ((primeToGaloisCohomologyFunctor d).obj M) ξ hu)

end PrimeToIsotypicGalois

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
