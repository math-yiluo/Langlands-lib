import Langlands.Shimura.PEL.HarrisTaylorCMIsotypicCohomology
import Langlands.Shimura.MultiplicityGaloisRepresentation
import Langlands.Cohomology.HarrisCMLevelGaloisSmooth.Statement

/-! # Multiplicity spaces of the cohomology of the actual CM tower as Galois representations

Assuming the Library statement that `Gal(F̄/F)` acts smoothly on the shrinking-level cohomology
of the actual geometric CM tower, the restricted Galois action on each isotypic part and the
Galois action on each multiplicity space `Hom(ξ, H^d)` of a finitely generated representation
`ξ` of `GG(A_f)ᵐᵒᵖ` are smooth. Over a topological field, a finite-dimensional multiplicity
space is then a continuous Galois representation of `F`, whose Euler polynomial at a finite
place where the cohomology is unramified is the Frobenius Euler polynomial of the multiplicity
space. The same holds for the prime-to-`m` cohomology, given the smoothness of its Galois
action as a hypothesis. See `HarrisTaylorCMMultiplicityGaloisRepresentation.md`.
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
open Langlands.Shimura.IsotypicGaloisAction Langlands.Shimura.MultiplicityGaloisRepresentation
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong
  geometricFrobenius)
open Langlands.Cohomology.HarrisCMLevelGaloisSmooth (HarrisCMLevelGaloisSmoothStatement)

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry Langlands.Geometry.EtalePullback
open CompactOpenLevel RestrictedSplitLevelTowerCohomology
open Langlands.Geometry.EtaleDerivedSections
open Langlands.GaloisRepresentation (LocalGroup ClosureEmbedding IsGeometricFrobeniusLift)
open Langlands.Shimura.IsotypicGaloisAction Langlands.Shimura.IsotypicDecompositionAction

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

/-! ## Smoothness of the Galois actions -/

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

/-- Under the Galois smoothness statement, `Gal(F̄/F)` acts smoothly on the shrinking-level
cohomology of the actual geometric CM tower. -/
theorem cmSmallLevelGaloisCohomology_isSmooth (hsmooth : galoisSmooth) (d : ℕ)
    (M : ModuleSheaf base R) :
    IsSmooth (galoisRepresentation ((galoisCohomologyFunctor d).obj M)) := by
  intro x
  obtain ⟨V, hV⟩ := hsmooth d M x
  exact ⟨V, (Representation.mem_invariants _ _).2 fun σ => hV σ.1 σ.2⟩

section SmallLevel

variable {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ U)

/-- Under the Galois smoothness statement, `Gal(F̄/F)` acts smoothly on every isotypic part of
the shrinking-level cohomology. -/
theorem cmSmallLevelIsotypicCohomology_isSmooth (hsmooth : galoisSmooth) (d : ℕ)
    (M : ModuleSheaf base R) :
    IsSmooth (galoisRepresentation ((cmSmallLevelIsotypicCohomologyFunctor D C preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
      criterion R ξ d).obj M)) :=
  isSmooth_isotypicGaloisRepresentation ξ
    (cmSmallLevelGaloisCohomology_isSmooth D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R hsmooth
      d M)

/-- Under the Galois smoothness statement, if `ξ` is finitely generated over the group algebra,
`Gal(F̄/F)` acts smoothly on the multiplicity spaces `Hom(ξ, H^d)` of the shrinking-level
cohomology. -/
theorem cmSmallLevelMultiplicity_isSmooth
    [Module.Finite (MonoidAlgebra R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) ξ.asModule]
    (hsmooth : galoisSmooth) (d : ℕ) (M : ModuleSheaf base R) :
    IsSmooth ((cmSmallLevelMultiplicityFunctor D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R ξ
      d).obj M).ρ :=
  isSmooth_multiplicityRepresentation ξ
    (cmSmallLevelGaloisCohomology_isSmooth D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R hsmooth
      d M)

end SmallLevel

section PrimeTo

variable (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ U)

local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- If `Gal(F̄/F)` acts smoothly on the prime-to-`m` cohomology, it acts smoothly on every
isotypic part. -/
theorem cmPrimeToIsotypicCohomology_isSmooth (d : ℕ) (M : ModuleSheaf base R)
    (hM : IsSmooth (galoisRepresentation ((primeToGaloisCohomologyFunctor d).obj M))) :
    IsSmooth (galoisRepresentation ((cmPrimeToIsotypicCohomologyFunctor D C preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
      criterion R m hm K₀ ξ d).obj M)) :=
  isSmooth_isotypicGaloisRepresentation ξ hM

/-- If `Gal(F̄/F)` acts smoothly on the prime-to-`m` cohomology and `ξ` is finitely generated
over the group algebra, `Gal(F̄/F)` acts smoothly on the multiplicity spaces `Hom(ξ, H^d)`. -/
theorem cmPrimeToMultiplicity_isSmooth
    [Module.Finite (MonoidAlgebra R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) ξ.asModule]
    (d : ℕ) (M : ModuleSheaf base R)
    (hM : IsSmooth (galoisRepresentation ((primeToGaloisCohomologyFunctor d).obj M))) :
    IsSmooth ((cmPrimeToMultiplicityFunctor D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm K₀
      ξ d).obj M).ρ :=
  isSmooth_multiplicityRepresentation ξ hM

end PrimeTo

end Ring

/-! ## Continuous Galois representations on the shrinking-level multiplicity spaces -/

section SmallLevelGalois

variable (R : Type) [Field R] [TopologicalSpace R] {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ U)
  [Module.Finite (MonoidAlgebra R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) ξ.asModule]

local notation "galoisCohomologyFunctor" => cmSmallLevelGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R

/-- Under the Galois smoothness statement, a finite-dimensional multiplicity space
`Hom(ξ, H^d)` of the shrinking-level cohomology over a topological field, as a continuous
Galois representation of `F` with `Gal(F̄/F)` acting by composition. -/
def cmSmallLevelMultiplicityGaloisRepresentation
    (hsmooth : HarrisCMLevelGaloisSmoothStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R)
    (d : ℕ) (M : ModuleSheaf base R)
    [Module.Finite R (ξ.IntertwiningMap ((galoisCohomologyFunctor d).obj M).V.representation)] :
    Objects.{0, 0, uU} F R :=
  multiplicityObjects (K := F) ξ ((galoisCohomologyFunctor d).obj M)
    (cmSmallLevelGaloisCohomology_isSmooth D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R hsmooth
      d M)

variable (hsmooth : HarrisCMLevelGaloisSmoothStatement D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
  criterion R) (d : ℕ) (M : ModuleSheaf (Spec (CommRingCat.of F)) R)
  [Module.Finite R (ξ.IntertwiningMap
    ((cmSmallLevelGaloisCohomologyFunctor D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R
      d).obj M).V.representation)]

local notation "multiplicityGalois" => cmSmallLevelMultiplicityGaloisRepresentation D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q existence
  geometry hRigid criterion R ξ hsmooth d M

/-- A Galois element acts on an intertwining map by composition with its action on the
cohomology. -/
theorem cmSmallLevelMultiplicityGaloisRepresentation_apply (σ : Field.absoluteGaloisGroup F)
    (φ : ξ.IntertwiningMap ((galoisCohomologyFunctor d).obj M).V.representation) :
    (multiplicityGalois).val.representation σ φ =
      (SmoothRep.hom (((galoisCohomologyFunctor d).obj M).ρ σ)).comp φ :=
  rfl

/-- The dimension of the Galois representation is that of the multiplicity space. -/
theorem cmSmallLevelMultiplicityGaloisRepresentation_rank :
    (multiplicityGalois).val.rank =
      Module.finrank R (ξ.IntertwiningMap ((galoisCohomologyFunctor d).obj M).V.representation) :=
  rfl

variable (w : Global.FinitePlace F)

/-- The Galois representation on the multiplicity space has Euler polynomial `P` at `w` exactly
when the multiplicity space is unramified at `w` with Frobenius Euler polynomial `P`. -/
theorem cmSmallLevelMultiplicityGaloisRepresentation_hasEulerPolynomialAt_iff {P : R[X]} :
    HasEulerPolynomialAt (multiplicityGalois) w P ↔
      IsUnramifiedAt (ModuleCat.{uU} R) w
          ((multiplicityActionFunctor ξ (Field.absoluteGaloisGroup F)).obj
            ((galoisCohomologyFunctor d).obj M)) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial w
          ((multiplicityActionFunctor ξ (Field.absoluteGaloisGroup F)).obj
            ((galoisCohomologyFunctor d).obj M)) = P :=
  hasEulerPolynomialAt_multiplicityObjects_iff ξ ((galoisCohomologyFunctor d).obj M) _ w

/-- If the cohomology is unramified at `w` along `j`, the Galois representation on the
multiplicity space has as Euler polynomial at `w` the reversed characteristic polynomial of the
geometric Frobenius endomorphism of the multiplicity space along `j`. -/
theorem cmSmallLevelMultiplicityGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAlong
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : IsUnramifiedAlong _ w ((galoisCohomologyFunctor d).obj M) j) :
    HasEulerPolynomialAt (multiplicityGalois) w
      (geometricFrobenius (ModuleCat.{uU} R) w
        ((multiplicityActionFunctor ξ (Field.absoluteGaloisGroup F)).obj
          ((galoisCohomologyFunctor d).obj M)) j).hom.charpoly.reverse :=
  hasEulerPolynomialAt_multiplicityObjects_of_isUnramifiedAlong ξ _ _ w hu

/-- If the cohomology is unramified at `w`, the Galois representation on the multiplicity space
has as Euler polynomial at `w` the Frobenius Euler polynomial of the multiplicity space. -/
theorem cmSmallLevelMultiplicityGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAt
    (hu : IsUnramifiedAt _ w ((galoisCohomologyFunctor d).obj M)) :
    HasEulerPolynomialAt (multiplicityGalois) w
      (FrobeniusPolynomial.frobeniusEulerPolynomial w
        ((multiplicityActionFunctor ξ (Field.absoluteGaloisGroup F)).obj
          ((galoisCohomologyFunctor d).obj M))) :=
  hasEulerPolynomialAt_multiplicityObjects_of_isUnramifiedAt ξ _ _ w hu

end SmallLevelGalois

/-! ## Continuous Galois representations on the prime-to-`m` multiplicity spaces -/

section PrimeToGalois

variable (R : Type) [Field R] [TopologicalSpace R]
  (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ U)
  [Module.Finite (MonoidAlgebra R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) ξ.asModule]

local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- If `Gal(F̄/F)` acts smoothly on the prime-to-`m` cohomology, a finite-dimensional
multiplicity space `Hom(ξ, H^d)` over a topological field, as a continuous Galois representation
of `F` with `Gal(F̄/F)` acting by composition. -/
def cmPrimeToMultiplicityGaloisRepresentation (d : ℕ) (M : ModuleSheaf base R)
    (hM : IsSmooth (galoisRepresentation ((primeToGaloisCohomologyFunctor d).obj M)))
    [Module.Finite R
      (ξ.IntertwiningMap ((primeToGaloisCohomologyFunctor d).obj M).V.representation)] :
    Objects.{0, 0, uU} F R :=
  multiplicityObjects (K := F) ξ ((primeToGaloisCohomologyFunctor d).obj M) hM

variable (d : ℕ) (M : ModuleSheaf (Spec (CommRingCat.of F)) R)
  (hM : IsSmooth (galoisRepresentation ((cmPrimeToGaloisCohomologyFunctor D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q m hm K₀ existence geometry
    hRigid criterion R d).obj M)))
  [Module.Finite R (ξ.IntertwiningMap ((cmPrimeToGaloisCohomologyFunctor D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q m hm K₀ existence geometry
    hRigid criterion R d).obj M).V.representation)]

local notation "primeToMultiplicityGalois" => cmPrimeToMultiplicityGaloisRepresentation D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q existence
  geometry hRigid criterion R m hm K₀ ξ d M hM

/-- A Galois element acts on an intertwining map by composition with its action on the
cohomology. -/
theorem cmPrimeToMultiplicityGaloisRepresentation_apply (σ : Field.absoluteGaloisGroup F)
    (φ : ξ.IntertwiningMap ((primeToGaloisCohomologyFunctor d).obj M).V.representation) :
    (primeToMultiplicityGalois).val.representation σ φ =
      (SmoothRep.hom (((primeToGaloisCohomologyFunctor d).obj M).ρ σ)).comp φ :=
  rfl

/-- The dimension of the Galois representation is that of the multiplicity space. -/
theorem cmPrimeToMultiplicityGaloisRepresentation_rank :
    (primeToMultiplicityGalois).val.rank = Module.finrank R
      (ξ.IntertwiningMap ((primeToGaloisCohomologyFunctor d).obj M).V.representation) :=
  rfl

variable (w : Global.FinitePlace F)

/-- The Galois representation on the multiplicity space has Euler polynomial `P` at `w` exactly
when the multiplicity space is unramified at `w` with Frobenius Euler polynomial `P`. -/
theorem cmPrimeToMultiplicityGaloisRepresentation_hasEulerPolynomialAt_iff {P : R[X]} :
    HasEulerPolynomialAt (primeToMultiplicityGalois) w P ↔
      IsUnramifiedAt (ModuleCat.{uU} R) w
          ((multiplicityActionFunctor ξ (Field.absoluteGaloisGroup F)).obj
            ((primeToGaloisCohomologyFunctor d).obj M)) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial w
          ((multiplicityActionFunctor ξ (Field.absoluteGaloisGroup F)).obj
            ((primeToGaloisCohomologyFunctor d).obj M)) = P :=
  hasEulerPolynomialAt_multiplicityObjects_iff ξ ((primeToGaloisCohomologyFunctor d).obj M) _ w

/-- If the prime-to-`m` cohomology is unramified at `w` along `j`, the Galois representation on
the multiplicity space has as Euler polynomial at `w` the reversed characteristic polynomial of
the geometric Frobenius endomorphism of the multiplicity space along `j`. -/
theorem cmPrimeToMultiplicityGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAlong
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : IsUnramifiedAlong _ w ((primeToGaloisCohomologyFunctor d).obj M) j) :
    HasEulerPolynomialAt (primeToMultiplicityGalois) w
      (geometricFrobenius (ModuleCat.{uU} R) w
        ((multiplicityActionFunctor ξ (Field.absoluteGaloisGroup F)).obj
          ((primeToGaloisCohomologyFunctor d).obj M)) j).hom.charpoly.reverse :=
  hasEulerPolynomialAt_multiplicityObjects_of_isUnramifiedAlong ξ _ _ w hu

/-- If the prime-to-`m` cohomology is unramified at `w`, the Galois representation on the
multiplicity space has as Euler polynomial at `w` the Frobenius Euler polynomial of the
multiplicity space. -/
theorem cmPrimeToMultiplicityGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAt
    (hu : IsUnramifiedAt _ w ((primeToGaloisCohomologyFunctor d).obj M)) :
    HasEulerPolynomialAt (primeToMultiplicityGalois) w
      (FrobeniusPolynomial.frobeniusEulerPolynomial w
        ((multiplicityActionFunctor ξ (Field.absoluteGaloisGroup F)).obj
          ((primeToGaloisCohomologyFunctor d).obj M))) :=
  hasEulerPolynomialAt_multiplicityObjects_of_isUnramifiedAt ξ _ _ w hu

end PrimeToGalois

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
