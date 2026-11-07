import Langlands.Shimura.PEL.HarrisTaylorCMIsotypicCohomology
import Langlands.Shimura.PEL.HarrisTaylorCMDecompositionCohomology
import Langlands.Shimura.IsotypicDecompositionAction

/-! # Decomposition groups acting on isotypic parts of the cohomology of the actual CM tower

At a finite place `w` of the CM field `F`, the `ξ`-isotypic parts of the shrinking-level and
prime-to-`m` cohomology of the actual geometric CM tower carry the action of the absolute Galois
group of the actual completion `F_w`, restricted along a specified embedding of algebraic
closures. This is the restriction of the Galois action on the isotypic part, and changing the
embedding is the action of the element of `Gal(F̄/F)` relating the embeddings. Unramifiedness
passes to isotypic parts, and the inclusion of the isotypic part intertwines the geometric
Frobenius endomorphisms. On the Hecke modules of `K'`-fixed vectors of the prime-to-`m`
isotypic part, the Frobenius endomorphism commutes with the Hecke algebra and is the restriction
of the Frobenius endomorphism of the full Hecke module. See
`HarrisTaylorCMIsotypicDecompositionCohomology.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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
  (R : Type) [CommRing R]


local notation "base" => Spec (CommRingCat.of F)
local notation "G" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "galoisCohomologyFunctor" => cmSmallLevelGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R

/-! ## The shrinking-level cohomology -/

section SmallLevel

variable {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ U)
  (w : Global.FinitePlace F)

local notation "isotypicCohomology" => cmSmallLevelIsotypicCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R ξ
local notation "decompositionFunctor" => cmSmallLevelDecompositionCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R w

/-- The `ξ`-isotypic part of the shrinking-level cohomology of the actual geometric CM tower with
coefficients pulled back from `Spec F`, with the action of the absolute Galois group of the
actual completion `F_w` restricted along the closure embedding `j`, natural in the sheaf. -/
def cmSmallLevelIsotypicDecompositionFunctor (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    ModuleSheaf base R ⥤ Action (SmoothRep.{0, 0, 0} R G) (LocalGroup w) :=
  decompositionFunctor d j ⋙ isotypicActionFunctor ξ (LocalGroup w)

local notation "isotypicDecomposition" => cmSmallLevelIsotypicDecompositionFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R ξ w

/-- An element of the local Galois group acts on the isotypic part by the restriction of the
action of its image in `Gal(F̄/F)` along `j`. -/
theorem cmSmallLevelIsotypicDecompositionFunctor_ρ (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) (g : LocalGroup w) :
    ((isotypicDecomposition d j).obj M).ρ g =
      isotypicMap ξ (((galoisCohomologyFunctor d).obj M).ρ
        (DecompositionGroupAction.localRestriction w j g)) :=
  rfl

/-- The local Galois action on the isotypic part is the restriction to the decomposition group
of the Galois action on the isotypic part. -/
def cmSmallLevelIsotypicDecompositionIso (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    isotypicDecomposition d j ≅
      isotypicCohomology d ⋙ DecompositionGroupAction.atFinitePlace _ w j :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (isotypicAtFinitePlaceIso w ξ j).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Changing the closure embedding from `k` to `j` is the action of the element of `Gal(F̄/F)`
relating them. -/
def cmSmallLevelIsotypicDecompositionChangeIso (d : ℕ)
    (j k : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    isotypicDecomposition d k ≅ isotypicDecomposition d j :=
  Functor.isoWhiskerRight
    (cmSmallLevelDecompositionChangeIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R w d j k)
    (isotypicActionFunctor ξ (LocalGroup w))

@[simp] theorem cmSmallLevelIsotypicDecompositionChangeIso_hom_app_hom (d : ℕ)
    (j k : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) :
    ((cmSmallLevelIsotypicDecompositionChangeIso D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid criterion R ξ w d
        j k).hom.app M).hom =
      isotypicMap ξ (((galoisCohomologyFunctor d).obj M).ρ
        (DecompositionGroupAction.localClosureChange w j k)) :=
  rfl

/-- If the cohomology is unramified at `w` along `j`, so is its `ξ`-isotypic part. -/
theorem cmSmallLevelIsotypicCohomology_isUnramifiedAlong (d : ℕ) (M : ModuleSheaf base R)
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hM : DecompositionGroupAction.IsUnramifiedAlong _ w ((galoisCohomologyFunctor d).obj M) j) :
    DecompositionGroupAction.IsUnramifiedAlong _ w ((isotypicCohomology d).obj M) j :=
  hM.isotypic ξ

/-- The inclusion of the `ξ`-isotypic part intertwines the geometric Frobenius endomorphisms at
`w` along `j`. -/
theorem cmSmallLevelIsotypicCohomology_geometricFrobenius_ι (d : ℕ) (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    DecompositionGroupAction.geometricFrobenius _ w ((isotypicCohomology d).obj M) j ≫
        ((cmSmallLevelIsotypicCohomologyι D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid criterion R ξ
          d).app M).hom =
      ((cmSmallLevelIsotypicCohomologyι D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid criterion R ξ
          d).app M).hom ≫
        DecompositionGroupAction.geometricFrobenius _ w ((galoisCohomologyFunctor d).obj M) j :=
  DecompositionGroupAction.geometricFrobenius_naturality _ j

end SmallLevel

/-! ## The prime-to-`m` cohomology -/

section PrimeTo

variable (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  {U : Type uU} [AddCommGroup U] [Module R U]
  (ξ : Representation R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ U)
  (w : Global.FinitePlace F)

local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R
local notation "primeToIsotypicCohomology" => cmPrimeToIsotypicCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R m hm K₀ ξ
local notation "primeToDecompositionFunctor" => cmPrimeToDecompositionCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R m hm K₀ w

/-- The `ξ`-isotypic part of the prime-to-`m` colimit cohomology of sheaves pulled back from
`Spec F`, with the action of the absolute Galois group of `F_w` restricted along `j`, natural in
the sheaf. -/
def cmPrimeToIsotypicDecompositionFunctor (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    ModuleSheaf base R ⥤
      Action (SmoothRep.{0, 0, 0} R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) (LocalGroup w) :=
  primeToDecompositionFunctor d j ⋙ isotypicActionFunctor ξ (LocalGroup w)

local notation "primeToIsotypicDecomposition" => cmPrimeToIsotypicDecompositionFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R m hm K₀ ξ w

/-- An element of the local Galois group acts on the isotypic part by the restriction of the
action of its image in `Gal(F̄/F)` along `j`. -/
theorem cmPrimeToIsotypicDecompositionFunctor_ρ (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) (g : LocalGroup w) :
    ((primeToIsotypicDecomposition d j).obj M).ρ g =
      isotypicMap ξ (((primeToGaloisCohomologyFunctor d).obj M).ρ
        (DecompositionGroupAction.localRestriction w j g)) :=
  rfl

/-- The local Galois action on the isotypic part is the restriction to the decomposition group
of the Galois action on the isotypic part. -/
def cmPrimeToIsotypicDecompositionIso (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    primeToIsotypicDecomposition d j ≅
      primeToIsotypicCohomology d ⋙ DecompositionGroupAction.atFinitePlace _ w j :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (isotypicAtFinitePlaceIso w ξ j).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Changing the closure embedding from `k` to `j` is the action of the element of `Gal(F̄/F)`
relating them. -/
def cmPrimeToIsotypicDecompositionChangeIso (d : ℕ)
    (j k : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    primeToIsotypicDecomposition d k ≅ primeToIsotypicDecomposition d j :=
  Functor.isoWhiskerRight
    (cmPrimeToDecompositionChangeIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm K₀
      w d j k)
    (isotypicActionFunctor ξ (LocalGroup w))

@[simp] theorem cmPrimeToIsotypicDecompositionChangeIso_hom_app_hom (d : ℕ)
    (j k : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) :
    ((cmPrimeToIsotypicDecompositionChangeIso D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm
        K₀ ξ w d j k).hom.app M).hom =
      isotypicMap ξ (((primeToGaloisCohomologyFunctor d).obj M).ρ
        (DecompositionGroupAction.localClosureChange w j k)) :=
  rfl

/-- If the prime-to-`m` cohomology is unramified at `w` along `j`, so is its `ξ`-isotypic
part. -/
theorem cmPrimeToIsotypicCohomology_isUnramifiedAlong (d : ℕ) (M : ModuleSheaf base R)
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hM : DecompositionGroupAction.IsUnramifiedAlong _ w
      ((primeToGaloisCohomologyFunctor d).obj M) j) :
    DecompositionGroupAction.IsUnramifiedAlong _ w ((primeToIsotypicCohomology d).obj M) j :=
  hM.isotypic ξ

/-- The inclusion of the `ξ`-isotypic part intertwines the geometric Frobenius endomorphisms at
`w` along `j`. -/
theorem cmPrimeToIsotypicCohomology_geometricFrobenius_ι (d : ℕ) (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    DecompositionGroupAction.geometricFrobenius _ w ((primeToIsotypicCohomology d).obj M) j ≫
        ((cmPrimeToIsotypicCohomologyι D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm
          K₀ ξ d).app M).hom =
      ((cmPrimeToIsotypicCohomologyι D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm
          K₀ ξ d).app M).hom ≫
        DecompositionGroupAction.geometricFrobenius _ w
          ((primeToGaloisCohomologyFunctor d).obj M) j :=
  DecompositionGroupAction.geometricFrobenius_naturality _ j

/-! ### Hecke modules and Frobenius -/

variable (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)

local notation "primeToIsotypicHeckeModuleFunctor" => cmPrimeToIsotypicHeckeModuleFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R m hm K₀ ξ K'
local notation "primeToGaloisHeckeModuleFunctor" => cmPrimeToGaloisHeckeModuleFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R K'

/-- The `K'`-fixed vectors of the `ξ`-isotypic part of the prime-to-`m` cohomology as modules
over the Hecke algebra of `K'`, with the action of the absolute Galois group of `F_w`
restricted along `j`, natural in the sheaf. -/
def cmPrimeToIsotypicDecompositionHeckeModuleFunctor (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    ModuleSheaf base R ⥤
      Action (ModuleCat.{0} (LevelHecke.LevelHeckeAlgebra R K'.subgroup)) (LocalGroup w) :=
  primeToIsotypicHeckeModuleFunctor d ⋙ DecompositionGroupAction.atFinitePlace _ w j

/-- Each element of the local Galois group commutes with every element of the Hecke algebra of
`K'` on the `K'`-fixed vectors of the `ξ`-isotypic part. -/
theorem cmPrimeToIsotypicDecompositionHeckeModule_ρ_smul (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) (g : LocalGroup w)
    (a : LevelHecke.LevelHeckeAlgebra R K'.subgroup)
    (x : ((cmPrimeToIsotypicDecompositionHeckeModuleFunctor D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
      criterion R m hm K₀ ξ w K' d j).obj M).V) :
    (((cmPrimeToIsotypicDecompositionHeckeModuleFunctor D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
        criterion R m hm K₀ ξ w K' d j).obj M).ρ g).hom (a • x) =
      a • (((cmPrimeToIsotypicDecompositionHeckeModuleFunctor D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
        criterion R m hm K₀ ξ w K' d j).obj M).ρ g).hom x :=
  map_smul _ a x

/-- The endomorphism of the Hecke module of `K'`-fixed vectors of the `ξ`-isotypic part by
which the chosen geometric Frobenius lift at `w` acts after restriction along `j`. -/
def cmPrimeToIsotypicHeckeFrobenius (d : ℕ) (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    ((primeToIsotypicHeckeModuleFunctor d).obj M).V ⟶
      ((primeToIsotypicHeckeModuleFunctor d).obj M).V :=
  DecompositionGroupAction.geometricFrobenius _ w ((primeToIsotypicHeckeModuleFunctor d).obj M) j

local notation "isotypicHeckeFrobenius" => cmPrimeToIsotypicHeckeFrobenius D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
  criterion R m hm K₀ ξ w K'

/-- The Frobenius endomorphism commutes with every element of the Hecke algebra of `K'`. -/
theorem cmPrimeToIsotypicHeckeFrobenius_smul (d : ℕ) (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (a : LevelHecke.LevelHeckeAlgebra R K'.subgroup)
    (x : ((primeToIsotypicHeckeModuleFunctor d).obj M).V) :
    (isotypicHeckeFrobenius d M j).hom (a • x) = a • (isotypicHeckeFrobenius d M j).hom x :=
  map_smul _ a x

/-- If the prime-to-`m` cohomology is unramified at `w` along `j`, so is the Hecke module of
`K'`-fixed vectors of its `ξ`-isotypic part. -/
theorem cmPrimeToIsotypicHeckeModule_isUnramifiedAlong (d : ℕ) (M : ModuleSheaf base R)
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hM : DecompositionGroupAction.IsUnramifiedAlong _ w
      ((primeToGaloisCohomologyFunctor d).obj M) j) :
    DecompositionGroupAction.IsUnramifiedAlong _ w
      ((primeToIsotypicHeckeModuleFunctor d).obj M) j :=
  (hM.isotypic ξ).mapAction (LevelHecke.heckeModuleFunctor R K'.subgroup)

/-- If the Hecke module is unramified at `w`, every geometric Frobenius lift acts by the
Frobenius endomorphism. -/
theorem cmPrimeToIsotypicHeckeFrobenius_eq_of_lift (d : ℕ) (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (hM : DecompositionGroupAction.IsUnramifiedAlong _ w
      ((primeToIsotypicHeckeModuleFunctor d).obj M) j)
    {g : LocalGroup w} (hg : IsGeometricFrobeniusLift w g) :
    ((cmPrimeToIsotypicDecompositionHeckeModuleFunctor D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
        criterion R m hm K₀ ξ w K' d j).obj M).ρ g = isotypicHeckeFrobenius d M j :=
  DecompositionGroupAction.geometricFrobenius_eq_of_lift hM hg

/-- Natural transformations of sheaves on `Spec F` intertwine the Frobenius endomorphisms. -/
theorem cmPrimeToIsotypicHeckeFrobenius_naturality (d : ℕ) {M N : ModuleSheaf base R}
    (α : M ⟶ N) (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    isotypicHeckeFrobenius d M j ≫ ((primeToIsotypicHeckeModuleFunctor d).map α).hom =
      ((primeToIsotypicHeckeModuleFunctor d).map α).hom ≫ isotypicHeckeFrobenius d N j :=
  DecompositionGroupAction.geometricFrobenius_naturality _ j

/-- The Frobenius endomorphisms along two closure embeddings are conjugate by the action of the
element of `Gal(F̄/F)` relating them. -/
theorem cmPrimeToIsotypicHeckeFrobenius_conj (d : ℕ) (M : ModuleSheaf base R)
    (j k : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    isotypicHeckeFrobenius d M k ≫ ((primeToIsotypicHeckeModuleFunctor d).obj M).ρ
        (DecompositionGroupAction.localClosureChange w j k) =
      ((primeToIsotypicHeckeModuleFunctor d).obj M).ρ
        (DecompositionGroupAction.localClosureChange w j k) ≫ isotypicHeckeFrobenius d M j :=
  DecompositionGroupAction.geometricFrobenius_conj _ j k

/-- The map of Hecke modules induced by the inclusion of the `ξ`-isotypic part intertwines its
Frobenius endomorphism with the Frobenius endomorphism of the Hecke module of `K'`-fixed
vectors of the whole prime-to-`m` cohomology. -/
theorem cmPrimeToIsotypicHeckeFrobenius_ι (d : ℕ) (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    isotypicHeckeFrobenius d M j ≫
        ((LevelHecke.heckeModuleActionFunctor R (Field.absoluteGaloisGroup F) K'.subgroup).map
          ((cmPrimeToIsotypicCohomologyι D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality dualityNaturality
            polarizationStability compatibility h htor q existence geometry hRigid criterion R m
            hm K₀ ξ d).app M)).hom =
      ((LevelHecke.heckeModuleActionFunctor R (Field.absoluteGaloisGroup F) K'.subgroup).map
          ((cmPrimeToIsotypicCohomologyι D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality dualityNaturality
            polarizationStability compatibility h htor q existence geometry hRigid criterion R m
            hm K₀ ξ d).app M)).hom ≫
        cmPrimeToHeckeFrobenius D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid criterion R m hm
          K₀ w K' d M j :=
  DecompositionGroupAction.geometricFrobenius_naturality _ j

end PrimeTo

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
