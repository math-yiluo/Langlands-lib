import Langlands.Shimura.PEL.HarrisTaylorCMUniversalClass
import Langlands.AbelianScheme.RelativePower
import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange

/-! # Relative powers of the universal CM abelian family and their factor maps -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme

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

local notation "component" => componentCMBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

/-- The inclusion of a connected component of a locally Noetherian scheme is a
closed immersion. -/
theorem componentι_isClosedImmersion (X : Scheme.{0}) [IsLocallyNoetherian X]
    (c : _root_.ConnectedComponents X) : IsClosedImmersion (componentι X c) := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [componentOpen_mk]
  exact isClosed_connectedComponent

section Powers
variable {U : SmallCMLevel D}
  (rep : CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor U)

local notation "family" => cmUniversalAbelianFamily D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor rep

/-- The relative `m`-th power of the abelian family over the component `c`,
with its structure map to that component; the zeroth power is the component itself. -/
def cmUniversalComponentPower (c : _root_.ConnectedComponents rep.base.obj.left) (m : ℕ) :
    Over (component rep.base c).obj.left :=
  relativePower (family c) m

local notation "power" => cmUniversalComponentPower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor rep

/-- The map from the power over the component `c` to the whole represented level: its
structure map followed by the actual inclusion of the component. -/
def cmUniversalComponentPowerToLevel
    (c : _root_.ConnectedComponents rep.base.obj.left) (m : ℕ) :
    (power c m).left ⟶ rep.base.obj.left :=
  (power c m).hom ≫ componentι rep.base.obj.left c

local notation "toLevel" => cmUniversalComponentPowerToLevel D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor rep

/-- On its component, the map to the level is the structure map of the power. -/
theorem cmUniversalComponentPowerToLevel_eq
    (c : _root_.ConnectedComponents rep.base.obj.left) (m : ℕ) :
    toLevel c m = (power c m).hom ≫ componentι rep.base.obj.left c := rfl

/-- The zeroth power is the component itself, mapped to the level by its inclusion. -/
theorem cmUniversalComponentPowerToLevel_zero
    (c : _root_.ConnectedComponents rep.base.obj.left) :
    toLevel c 0 = 𝟙 _ ≫ componentι rep.base.obj.left c := rfl

/-- The power over a component is smooth and proper over that component. -/
theorem cmUniversalComponentPower_hom_smooth_proper
    (c : _root_.ConnectedComponents rep.base.obj.left) (m : ℕ) :
    Smooth (power c m).hom ∧ IsProper (power c m).hom :=
  relativePower_smooth_proper (family c) m

/-- Each power is smooth and proper over the whole represented level and over the CM
field, using the smoothness and projectivity in the representing evidence. -/
theorem cmUniversalComponentPower_smooth_proper
    (c : _root_.ConnectedComponents rep.base.obj.left) (m : ℕ) :
    Smooth (toLevel c m) ∧ IsProper (toLevel c m) ∧
      Smooth (toLevel c m ≫ rep.base.obj.hom) ∧
      IsProper (toLevel c m ≫ rep.base.obj.hom) := by
  have geometry := relativePower_smooth_proper (family c) m
  let incl := componentι rep.base.obj.left c
  have : IsOpenImmersion incl := componentιOpenImmersion _ _
  have : IsClosedImmersion incl := componentι_isClosedImmersion _ c
  have smooth : Smooth (toLevel c m) :=
    MorphismProperty.comp_mem @Smooth (power c m).hom incl geometry.1
      (inferInstance : Smooth incl)
  have proper : IsProper (toLevel c m) :=
    MorphismProperty.comp_mem @IsProper (power c m).hom incl geometry.2
      (inferInstance : IsProper incl)
  exact ⟨smooth, proper, MorphismProperty.comp_mem @Smooth _ _ smooth rep.smooth,
    MorphismProperty.comp_mem @IsProper _ _ proper (IsHProjective.isProper rep.projective)⟩

/-- The scheme map multiplying the factor `i` of the power by two. -/
def cmUniversalComponentPowerDouble (c : _root_.ConnectedComponents rep.base.obj.left)
    (m : ℕ) (i : Fin m) : (power c m).left ⟶ (power c m).left :=
  (relativePowerDouble (family c) m i).left

/-- The scheme map permuting the factors of the power: its factor `j` is the original
factor `σ j`. -/
def cmUniversalComponentPowerPermute (c : _root_.ConnectedComponents rep.base.obj.left)
    (m : ℕ) (σ : Equiv.Perm (Fin m)) : (power c m).left ⟶ (power c m).left :=
  (relativePowerPermute (family c) m σ).left

/-- Multiplication by two on a factor commutes with the map to the level. -/
@[reassoc] theorem cmUniversalComponentPowerDouble_toLevel
    (c : _root_.ConnectedComponents rep.base.obj.left) (m : ℕ) (i : Fin m) :
    cmUniversalComponentPowerDouble D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor rep c m i ≫ toLevel c m = toLevel c m := by
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ componentι rep.base.obj.left c)
    (Over.w (relativePowerDouble (family c) m i)))

/-- The permutation maps commute with the map to the level. -/
@[reassoc] theorem cmUniversalComponentPowerPermute_toLevel
    (c : _root_.ConnectedComponents rep.base.obj.left) (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    cmUniversalComponentPowerPermute D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor rep c m σ ≫ toLevel c m = toLevel c m := by
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ componentι rep.base.obj.left c)
    (Over.w (relativePowerPermute (family c) m σ)))

/-- The scheme permutation maps compose as the permutations multiply. -/
theorem cmUniversalComponentPowerPermute_comp
    (c : _root_.ConnectedComponents rep.base.obj.left) (m : ℕ) (σ τ : Equiv.Perm (Fin m)) :
    cmUniversalComponentPowerPermute D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor rep c m σ ≫
      cmUniversalComponentPowerPermute D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor rep c m τ =
    cmUniversalComponentPowerPermute D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor rep c m (σ * τ) := by
  change (relativePowerPermute (family c) m σ).left ≫ (relativePowerPermute (family c) m τ).left =
    (relativePowerPermute (family c) m (σ * τ)).left
  rw [← Over.comp_left, relativePowerPermute_comp]

/-- The identity permutation gives the identity map. -/
@[simp] theorem cmUniversalComponentPowerPermute_one
    (c : _root_.ConnectedComponents rep.base.obj.left) (m : ℕ) :
    cmUniversalComponentPowerPermute D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor rep c m 1 = 𝟙 _ := by
  change (relativePowerPermute (family c) m 1).left = 𝟙 _
  rw [relativePowerPermute_one, Over.id_left]

/-- The permutation maps carry multiplication by two on the factor `σ i` to
multiplication by two on the factor `i`. -/
theorem cmUniversalComponentPowerPermute_double
    (c : _root_.ConnectedComponents rep.base.obj.left) (m : ℕ) (σ : Equiv.Perm (Fin m))
    (i : Fin m) :
    cmUniversalComponentPowerPermute D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor rep c m σ ≫
      cmUniversalComponentPowerDouble D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor rep c m i =
    cmUniversalComponentPowerDouble D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor rep c m (σ i) ≫
      cmUniversalComponentPowerPermute D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor rep c m σ := by
  change (relativePowerPermute (family c) m σ).left ≫
      (relativePowerMultiply (family c) m i 2).left =
    (relativePowerMultiply (family c) m (σ i) 2).left ≫
      (relativePowerPermute (family c) m σ).left
  rw [← Over.comp_left, ← Over.comp_left, relativePowerPermute_multiply]

end Powers

/-! ### Powers over the levels of the scheme tower -/

section Chosen
variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

local notation "schemeTower" => cmSchemeTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q

/-- The relative power over the component `c` of the level `U` of the scheme tower. -/
abbrev cmSchemeTowerComponentPower (U : SmallCMLevel D)
    (c : _root_.ConnectedComponents (chosen U).base.obj.left) (m : ℕ) :=
  cmUniversalComponentPower D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor (chosen U) c m

/-- Its map to the level `U` of the actual scheme tower. -/
def cmSchemeTowerComponentPowerToLevel (U : SmallCMLevel D)
    (c : _root_.ConnectedComponents (chosen U).base.obj.left) (m : ℕ) :
    (cmSchemeTowerComponentPower D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q U c m).left ⟶ (schemeTower).obj U :=
  cmUniversalComponentPowerToLevel D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor (chosen U) c m

/-- The powers over the scheme tower are smooth and proper over the level and over the
CM field. -/
theorem cmSchemeTowerComponentPower_smooth_proper (U : SmallCMLevel D)
    (c : _root_.ConnectedComponents (chosen U).base.obj.left) (m : ℕ) :
    Smooth (cmSchemeTowerComponentPowerToLevel D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U c m) ∧
      IsProper (cmSchemeTowerComponentPowerToLevel D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U c m) ∧
      Smooth (cmSchemeTowerComponentPowerToLevel D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U c m ≫ (chosen U).base.obj.hom) ∧
      IsProper (cmSchemeTowerComponentPowerToLevel D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U c m ≫ (chosen U).base.obj.hom) :=
  cmUniversalComponentPower_smooth_proper D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (chosen U) c m

end Chosen

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
