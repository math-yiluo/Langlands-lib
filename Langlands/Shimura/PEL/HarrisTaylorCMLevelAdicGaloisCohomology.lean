import Langlands.Shimura.PEL.HarrisTaylorCMLevelGaloisCohomology
import Langlands.Cohomology.DivisibleSystem.ContinuousLimit
import Langlands.Geometry.EtaleAdicSystem

/-! # Continuous Galois actions on inverse limits of fixed-level cohomology of the actual CM tower

For an inverse system `m ↦ M_m` of sheaves on `Spec F`, for instance the constant sheaves
`M / ℓ^m M`, the fixed-level cohomology modules `H^d(X_U ×_F Spec F̄, p_U^* M_m)` with their
Galois actions form an inverse system. Its inverse limit, with the inverse limit topology of the
discrete levels, is Hausdorff, and the action of `Gal(F̄/F)` on it is jointly continuous for the
Krull topology when every level is a smooth Galois representation. The same holds at the levels
of the prime-to-`m` tower. See `HarrisTaylorCMLevelAdicGaloisCohomology.md`.
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
open Langlands.Cohomology

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

local notation "base" => Spec (CommRingCat.of F)
local notation "Gamma" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)

/-! ## The shrinking-level tower at a fixed level -/

section SmallLevel

variable (R : Type) [CommRing R] (U : SmallCMLevel D) (d : ℕ)

/-- For an inverse system of sheaves on `Spec F`, the inverse system of their fixed-level
cohomology modules `H^d(X_U ×_F Spec F̄, p_U^* M_m)` with the Galois actions. -/
def cmLevelAdicSystem :
    (ℕᵒᵖ ⥤ ModuleSheaf base R) ⥤ (ℕᵒᵖ ⥤ Action (ModuleCat.{0} R) Gamma) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (cmLevelGaloisCohomologyFunctor D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q R U d)

local notation "adicSystem" => cmLevelAdicSystem D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q R U d

@[simp] theorem cmLevelAdicSystem_obj_obj (M : ℕᵒᵖ ⥤ ModuleSheaf base R) (k : ℕᵒᵖ) :
    ((adicSystem).obj M).obj k =
      (cmLevelGaloisCohomologyFunctor D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q R U d).obj (M.obj k) :=
  rfl

/-- The inverse limit over the system of the fixed-level cohomology modules, with the inverse
limit topology of the discrete levels. -/
abbrev CMLevelAdicSpace (M : ℕᵒᵖ ⥤ ModuleSheaf (Spec (CommRingCat.of F)) R) : Type :=
  ContinuousLimit.ConeSpace (limit.cone ((cmLevelAdicSystem D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q R U d).obj M))

local notation "adicSpace" => CMLevelAdicSpace D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q R U d

/-- The inverse limit is Hausdorff. -/
instance (M : ℕᵒᵖ ⥤ ModuleSheaf (Spec (CommRingCat.of F)) R) : T2Space (adicSpace M) :=
  ContinuousLimit.t2Space_of_isLimit (limit.isLimit _)

/-- If every level is a smooth Galois representation, the action of `Gal(F̄/F)` on the inverse
limit is jointly continuous for the Krull topology. -/
theorem continuous_cmLevelAdicAction (M : ℕᵒᵖ ⥤ ModuleSheaf base R)
    (hM : ∀ k, IsSmooth ((Rep.ActionToRep R Gamma).obj (((adicSystem).obj M).obj k)).ρ) :
    Continuous fun x : Gamma × adicSpace M =>
      ContinuousLimit.act (limit.cone ((adicSystem).obj M)) x.1 x.2 :=
  ContinuousLimit.continuous_action _ hM

/-- The Galois representation on the inverse limit by continuous linear maps. -/
abbrev cmLevelAdicContRepresentation (M : ℕᵒᵖ ⥤ ModuleSheaf base R) :
    ContRepresentation R Gamma (adicSpace M) :=
  ContinuousLimit.contRepresentation _

/-- For a topological coefficient ring acting continuously, and smooth levels, the inverse limit
with its jointly continuous Galois action. -/
def cmLevelAdicContAction [TopologicalSpace R] (M : ℕᵒᵖ ⥤ ModuleSheaf base R)
    [ContinuousSMul R (adicSpace M)]
    (hM : ∀ k, IsSmooth ((Rep.ActionToRep R Gamma).obj (((adicSystem).obj M).obj k)).ρ) :
    ContAction (TopModuleCat.{0} R) Gamma :=
  ContinuousLimit.contAction (limit.cone ((adicSystem).obj M)) hM

/-- For a discrete coefficient ring, the inverse limit as a functor from inverse systems of
sheaves on `Spec F` to topological representations of `Gal(F̄/F)`. -/
def cmLevelAdicTopRepFunctor [TopologicalSpace R] [DiscreteTopology R] :
    (ℕᵒᵖ ⥤ ModuleSheaf base R) ⥤ TopRep.{0} R Gamma :=
  adicSystem ⋙ ContinuousLimit.limitTopRepFunctor R Gamma ℕᵒᵖ

/-- The inverse limit for the constant sheaves `N / ℓ^m N` on `Spec F` of an `R`-module `N`. -/
abbrev CMLevelEllAdicSpace (ell : ℕ) (N : ModuleCat.{0} R) : Type :=
  adicSpace (EtaleAdicSystem.ellPowerConstantSystem (Spec (CommRingCat.of F)) ell N)

end SmallLevel

/-! ## The prime-to-`m` tower at a fixed level -/

section PrimeTo

variable (R : Type) [CommRing R] (m : ℕ) (hm : m ≠ 0)
  (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  (K' : (cmPrimeToProperty D m hm K₀).FullSubcategory) (d : ℕ)

/-- For an inverse system of sheaves on `Spec F`, the inverse system of their cohomology modules
at the prime-to-`m` level `K'`, with the Galois actions. -/
def cmPrimeToLevelAdicSystem :
    (ℕᵒᵖ ⥤ ModuleSheaf base R) ⥤ (ℕᵒᵖ ⥤ Action (ModuleCat.{0} R) Gamma) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (cmPrimeToLevelGaloisCohomologyFunctor D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q R m hm K₀ K' d)

local notation "primeToAdicSystem" => cmPrimeToLevelAdicSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q R m hm K₀ K' d

@[simp] theorem cmPrimeToLevelAdicSystem_obj_obj (M : ℕᵒᵖ ⥤ ModuleSheaf base R) (k : ℕᵒᵖ) :
    ((primeToAdicSystem).obj M).obj k =
      (cmPrimeToLevelGaloisCohomologyFunctor D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q R m hm K₀ K' d).obj (M.obj k) :=
  rfl

/-- The inverse limit over the system of the cohomology modules at the level `K'`, with the
inverse limit topology of the discrete levels. -/
abbrev CMPrimeToLevelAdicSpace (M : ℕᵒᵖ ⥤ ModuleSheaf (Spec (CommRingCat.of F)) R) : Type :=
  ContinuousLimit.ConeSpace (limit.cone ((cmPrimeToLevelAdicSystem D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q R m hm K₀ K' d).obj M))

local notation "primeToAdicSpace" => CMPrimeToLevelAdicSpace D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q R m hm K₀ K' d

/-- The inverse limit is Hausdorff. -/
instance (M : ℕᵒᵖ ⥤ ModuleSheaf (Spec (CommRingCat.of F)) R) : T2Space (primeToAdicSpace M) :=
  ContinuousLimit.t2Space_of_isLimit (limit.isLimit _)

/-- If every level is a smooth Galois representation, the action of `Gal(F̄/F)` on the inverse
limit is jointly continuous for the Krull topology. -/
theorem continuous_cmPrimeToLevelAdicAction (M : ℕᵒᵖ ⥤ ModuleSheaf base R)
    (hM : ∀ k, IsSmooth ((Rep.ActionToRep R Gamma).obj (((primeToAdicSystem).obj M).obj k)).ρ) :
    Continuous fun x : Gamma × primeToAdicSpace M =>
      ContinuousLimit.act (limit.cone ((primeToAdicSystem).obj M)) x.1 x.2 :=
  ContinuousLimit.continuous_action _ hM

/-- The Galois representation on the inverse limit by continuous linear maps. -/
abbrev cmPrimeToLevelAdicContRepresentation (M : ℕᵒᵖ ⥤ ModuleSheaf base R) :
    ContRepresentation R Gamma (primeToAdicSpace M) :=
  ContinuousLimit.contRepresentation _

/-- For a topological coefficient ring acting continuously, and smooth levels, the inverse limit
with its jointly continuous Galois action. -/
def cmPrimeToLevelAdicContAction [TopologicalSpace R] (M : ℕᵒᵖ ⥤ ModuleSheaf base R)
    [ContinuousSMul R (primeToAdicSpace M)]
    (hM : ∀ k, IsSmooth ((Rep.ActionToRep R Gamma).obj (((primeToAdicSystem).obj M).obj k)).ρ) :
    ContAction (TopModuleCat.{0} R) Gamma :=
  ContinuousLimit.contAction (limit.cone ((primeToAdicSystem).obj M)) hM

/-- For a discrete coefficient ring, the inverse limit as a functor from inverse systems of
sheaves on `Spec F` to topological representations of `Gal(F̄/F)`. -/
def cmPrimeToLevelAdicTopRepFunctor [TopologicalSpace R] [DiscreteTopology R] :
    (ℕᵒᵖ ⥤ ModuleSheaf base R) ⥤ TopRep.{0} R Gamma :=
  primeToAdicSystem ⋙ ContinuousLimit.limitTopRepFunctor R Gamma ℕᵒᵖ

/-- The inverse limit for the constant sheaves `N / ℓ^m N` on `Spec F` of an `R`-module `N`. -/
abbrev CMPrimeToLevelEllAdicSpace (ell : ℕ) (N : ModuleCat.{0} R) : Type :=
  primeToAdicSpace (EtaleAdicSystem.ellPowerConstantSystem (Spec (CommRingCat.of F)) ell N)

end PrimeTo

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
