import Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology
import Langlands.Shimura.DecompositionGroupAction

/-! # Decomposition groups acting on the cohomology of the actual CM tower

At a finite place `w` of the CM field `F`, the Galois actions on the shrinking-level cohomology
of the actual geometric CM tower, on its prime-to-`m` cohomology and on the Hecke modules of
`K'`-fixed vectors are restricted to the absolute Galois group of the actual completion `F_w`
along a specified embedding of algebraic closures. Changing the embedding is the action of the
element of `Gal(F̄/F)` relating the embeddings. The restricted actions commute with the
finite-adelic actions, with the comparison between the two cohomologies and with the Hecke
algebra, and so do the geometric Frobenius endomorphisms at `w`. See
`HarrisTaylorCMDecompositionCohomology.md`.
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
open Langlands.GaloisRepresentation (LocalGroup ClosureEmbedding IsGeometricFrobeniusLift)

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

variable (w : Global.FinitePlace F)

/-- The shrinking-level cohomology of the actual geometric CM tower with coefficients pulled back
from `Spec F`, with the action of the absolute Galois group of the actual completion `F_w`
restricted along the closure embedding `j`, natural in the sheaf. -/
def cmSmallLevelDecompositionCohomologyFunctor (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    ModuleSheaf base R ⥤ Action (SmoothRep.{0, 0, 0} R G) (LocalGroup w) :=
  galoisCohomologyFunctor d ⋙ DecompositionGroupAction.atFinitePlace _ w j

local notation "decompositionFunctor" => cmSmallLevelDecompositionCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R w

@[simp] theorem cmSmallLevelDecompositionCohomologyFunctor_obj_V (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) :
    ((decompositionFunctor d j).obj M).V = ((galoisCohomologyFunctor d).obj M).V :=
  rfl

/-- An element of the local Galois group acts as its restriction to `Gal(F̄/F)` along `j`. -/
theorem cmSmallLevelDecompositionCohomologyFunctor_ρ (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) (g : LocalGroup w) :
    ((decompositionFunctor d j).obj M).ρ g =
      ((galoisCohomologyFunctor d).obj M).ρ (DecompositionGroupAction.localRestriction w j g) :=
  rfl

/-- Changing the closure embedding from `k` to `j` is the action of the element of `Gal(F̄/F)`
relating them. -/
def cmSmallLevelDecompositionChangeIso (d : ℕ)
    (j k : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    decompositionFunctor d k ≅ decompositionFunctor d j :=
  Functor.isoWhiskerLeft _ (DecompositionGroupAction.atFinitePlaceChangeIso _ w j k)

@[simp] theorem cmSmallLevelDecompositionChangeIso_hom_app_hom (d : ℕ)
    (j k : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) :
    ((cmSmallLevelDecompositionChangeIso D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid criterion R w d
        j k).hom.app M).hom =
      ((galoisCohomologyFunctor d).obj M).ρ (DecompositionGroupAction.localClosureChange w j k) :=
  rfl

/-- The local Galois action commutes with the action of `GG(A_f)ᵐᵒᵖ`. -/
theorem cmSmallLevelDecompositionCohomology_commutes (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) (g : LocalGroup w) (x : G)
    (y : ((decompositionFunctor d j).obj M).V) :
    SmoothRep.hom (((decompositionFunctor d j).obj M).ρ g)
        (((decompositionFunctor d j).obj M).V.obj.ρ x y) =
      ((decompositionFunctor d j).obj M).V.obj.ρ x
        (SmoothRep.hom (((decompositionFunctor d j).obj M).ρ g) y) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom (((decompositionFunctor d j).obj M).ρ g)) x y

end SmallLevel

/-! ## The prime-to-`m` cohomology -/

section PrimeTo

variable (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  (w : Global.FinitePlace F)

local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- The prime-to-`m` colimit cohomology of sheaves pulled back from `Spec F`, with the action of
the absolute Galois group of the actual completion `F_w` restricted along the closure embedding
`j`, natural in the sheaf. -/
def cmPrimeToDecompositionCohomologyFunctor (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    ModuleSheaf base R ⥤
      Action (SmoothRep.{0, 0, 0} R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) (LocalGroup w) :=
  primeToGaloisCohomologyFunctor d ⋙ DecompositionGroupAction.atFinitePlace _ w j

local notation "primeToDecompositionFunctor" => cmPrimeToDecompositionCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R m hm K₀ w

@[simp] theorem cmPrimeToDecompositionCohomologyFunctor_obj_V (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) :
    ((primeToDecompositionFunctor d j).obj M).V = ((primeToGaloisCohomologyFunctor d).obj M).V :=
  rfl

/-- An element of the local Galois group acts as its restriction to `Gal(F̄/F)` along `j`. -/
theorem cmPrimeToDecompositionCohomologyFunctor_ρ (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) (g : LocalGroup w) :
    ((primeToDecompositionFunctor d j).obj M).ρ g =
      ((primeToGaloisCohomologyFunctor d).obj M).ρ
        (DecompositionGroupAction.localRestriction w j g) :=
  rfl

/-- Changing the closure embedding from `k` to `j` is the action of the element of `Gal(F̄/F)`
relating them. -/
def cmPrimeToDecompositionChangeIso (d : ℕ)
    (j k : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    primeToDecompositionFunctor d k ≅ primeToDecompositionFunctor d j :=
  Functor.isoWhiskerLeft _ (DecompositionGroupAction.atFinitePlaceChangeIso _ w j k)

@[simp] theorem cmPrimeToDecompositionChangeIso_hom_app_hom (d : ℕ)
    (j k : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) :
    ((cmPrimeToDecompositionChangeIso D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid criterion R
        m hm K₀ w d j k).hom.app M).hom =
      ((primeToGaloisCohomologyFunctor d).obj M).ρ
        (DecompositionGroupAction.localClosureChange w j k) :=
  rfl

/-- The local Galois action commutes with the action of `GG(A_f^{(m)})ᵐᵒᵖ`. -/
theorem cmPrimeToDecompositionCohomology_commutes (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) (g : LocalGroup w)
    (x : (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)
    (y : ((primeToDecompositionFunctor d j).obj M).V) :
    SmoothRep.hom (((primeToDecompositionFunctor d j).obj M).ρ g)
        (((primeToDecompositionFunctor d j).obj M).V.obj.ρ x y) =
      ((primeToDecompositionFunctor d j).obj M).V.obj.ρ x
        (SmoothRep.hom (((primeToDecompositionFunctor d j).obj M).ρ g) y) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom (((primeToDecompositionFunctor d j).obj M).ρ g)) x y

/-- The comparison from the prime-to-`m` cohomology to the shrinking-level cohomology of the
actual CM tower commutes with the local Galois action. -/
theorem cmPrimeToDecompositionCohomologyComparison_apply (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) (g : LocalGroup w)
    (x : ((primeToDecompositionFunctor d j).obj M).V.obj) :
    (cmPrimeToCohomologyComparison D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
        criterion R (cmSmallLevelArithmeticCoefficients D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor q existence geometry
          hRigid criterion R M) d).hom.hom
        ((((primeToDecompositionFunctor d j).obj M).ρ g).hom.hom x) =
      (((cmSmallLevelDecompositionCohomologyFunctor D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q existence geometry hRigid criterion R w
          d j).obj M).ρ g).hom.hom
        ((cmPrimeToCohomologyComparison D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
          criterion R (cmSmallLevelArithmeticCoefficients D C preservation composition
            unitCoherence associativity comparison symmetry stability square universality
            dualityNaturality polarizationStability compatibility h htor q existence geometry
            hRigid criterion R M) d).hom.hom x) :=
  cmPrimeToGaloisCohomologyComparison_apply D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid criterion R
    d M (DecompositionGroupAction.localRestriction w j g) x

/-! ## Hecke modules and Frobenius -/

variable (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)

local notation "primeToGaloisHeckeModuleFunctor" => cmPrimeToGaloisHeckeModuleFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R K'

/-- The `K'`-fixed vectors of the prime-to-`m` cohomology as modules over the Hecke algebra of
`K'`, with the action of the absolute Galois group of `F_w` restricted along `j`, natural in the
sheaf. -/
def cmPrimeToDecompositionHeckeModuleFunctor (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    ModuleSheaf base R ⥤
      Action (ModuleCat.{0} (LevelHecke.LevelHeckeAlgebra R K'.subgroup)) (LocalGroup w) :=
  primeToGaloisHeckeModuleFunctor d ⋙ DecompositionGroupAction.atFinitePlace _ w j

local notation "primeToDecompositionHeckeModuleFunctor" =>
  cmPrimeToDecompositionHeckeModuleFunctor D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q existence geometry hRigid criterion R
    m hm K₀ w K'

/-- These are the `K'`-fixed vectors of the prime-to-`m` cohomology with the local Galois
action, as Hecke modules. -/
def cmPrimeToDecompositionHeckeModuleIso (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    primeToDecompositionHeckeModuleFunctor d j ≅
      primeToDecompositionFunctor d j ⋙
        LevelHecke.heckeModuleActionFunctor R (LocalGroup w) K'.subgroup :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DecompositionGroupAction.mapActionResIso _
      (LevelHecke.heckeModuleFunctor R K'.subgroup)
      (DecompositionGroupAction.localRestriction w j)) ≪≫
    (Functor.associator _ _ _).symm

/-- Each element of the local Galois group commutes with every element of the Hecke algebra of
`K'`. -/
theorem cmPrimeToDecompositionHeckeModule_ρ_smul (d : ℕ)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (M : ModuleSheaf base R) (g : LocalGroup w)
    (a : LevelHecke.LevelHeckeAlgebra R K'.subgroup)
    (x : ((primeToDecompositionHeckeModuleFunctor d j).obj M).V) :
    (((primeToDecompositionHeckeModuleFunctor d j).obj M).ρ g).hom (a • x) =
      a • (((primeToDecompositionHeckeModuleFunctor d j).obj M).ρ g).hom x :=
  map_smul _ a x

/-- The endomorphism of the Hecke module of `K'`-fixed vectors by which the chosen geometric
Frobenius lift at `w` acts after restriction along `j`. -/
def cmPrimeToHeckeFrobenius (d : ℕ) (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    ((primeToGaloisHeckeModuleFunctor d).obj M).V ⟶ ((primeToGaloisHeckeModuleFunctor d).obj M).V :=
  DecompositionGroupAction.geometricFrobenius _ w ((primeToGaloisHeckeModuleFunctor d).obj M) j

local notation "heckeFrobenius" => cmPrimeToHeckeFrobenius D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
  criterion R m hm K₀ w K'

/-- The Frobenius endomorphism commutes with every element of the Hecke algebra of `K'`. -/
theorem cmPrimeToHeckeFrobenius_smul (d : ℕ) (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (a : LevelHecke.LevelHeckeAlgebra R K'.subgroup)
    (x : ((primeToGaloisHeckeModuleFunctor d).obj M).V) :
    (heckeFrobenius d M j).hom (a • x) = a • (heckeFrobenius d M j).hom x :=
  map_smul _ a x

/-- If the Hecke module is unramified at `w`, every geometric Frobenius lift acts by the
Frobenius endomorphism. -/
theorem cmPrimeToHeckeFrobenius_eq_of_lift (d : ℕ) (M : ModuleSheaf base R)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w))
    (hM : DecompositionGroupAction.IsUnramifiedAlong _ w
      ((primeToGaloisHeckeModuleFunctor d).obj M) j)
    {g : LocalGroup w} (hg : IsGeometricFrobeniusLift w g) :
    ((primeToDecompositionHeckeModuleFunctor d j).obj M).ρ g = heckeFrobenius d M j :=
  DecompositionGroupAction.geometricFrobenius_eq_of_lift hM hg

/-- Natural transformations of sheaves on `Spec F` intertwine the Frobenius endomorphisms. -/
theorem cmPrimeToHeckeFrobenius_naturality (d : ℕ) {M N : ModuleSheaf base R} (α : M ⟶ N)
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    heckeFrobenius d M j ≫ ((primeToGaloisHeckeModuleFunctor d).map α).hom =
      ((primeToGaloisHeckeModuleFunctor d).map α).hom ≫ heckeFrobenius d N j :=
  DecompositionGroupAction.geometricFrobenius_naturality _ j

/-- The Frobenius endomorphisms along two closure embeddings are conjugate by the action of the
element of `Gal(F̄/F)` relating them. -/
theorem cmPrimeToHeckeFrobenius_conj (d : ℕ) (M : ModuleSheaf base R)
    (j k : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    heckeFrobenius d M k ≫ ((primeToGaloisHeckeModuleFunctor d).obj M).ρ
        (DecompositionGroupAction.localClosureChange w j k) =
      ((primeToGaloisHeckeModuleFunctor d).obj M).ρ
        (DecompositionGroupAction.localClosureChange w j k) ≫ heckeFrobenius d M j :=
  DecompositionGroupAction.geometricFrobenius_conj _ j k

end PrimeTo

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
