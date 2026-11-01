import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Langlands.AlgebraicGeometry.Modules.OpenCohomologyVanishing
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Actual module-sheaf closure of an ideal on an open subscheme -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.OpenImmersionIdeal

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  {D : Y.Modules} (s : D ⟶ SheafOfModules.unit Y.ringCatSheaf)

/-- The inverse image of the pushed-forward ideal inside the structure module. -/
def closure : X.Modules :=
  pullback (Langlands.Scheme.Modules.unitToPushforwardUnit j)
    ((Scheme.Modules.pushforward j).map s)

/-- The actual inclusion of the closure into the structure module. -/
def inclusion : closure j s ⟶ SheafOfModules.unit X.ringCatSheaf :=
  pullback.fst _ _

/-- The closure's second projection into the pushed-forward original module. -/
def projection : closure j s ⟶ (Scheme.Modules.pushforward j).obj D :=
  pullback.snd _ _

omit [IsOpenImmersion j] in
lemma condition : inclusion j s ≫ Langlands.Scheme.Modules.unitToPushforwardUnit j =
    projection j s ≫ (Scheme.Modules.pushforward j).map s :=
  pullback.condition

instance [Mono s] : Mono (inclusion j s) := by
  dsimp only [inclusion]
  infer_instance

/-- Restriction along an open immersion preserves finite limits. -/
instance preservesFiniteLimits_restrict :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) :=
  Langlands.AlgebraicGeometry.Modules.DerivedSections.OpenCohomologyVanishing.preservesFiniteLimits_pushforward _

/-- Pullback along an open immersion preserves finite limits. -/
instance preservesFiniteLimits_pullback :
    PreservesFiniteLimits (Scheme.Modules.pullback j) :=
  preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback j)

omit [IsOpenImmersion j] in
/-- The structure map restricts to the canonical unit comparison. -/
lemma map_unitToPushforwardUnit_counit :
    (Scheme.Modules.pullback j).map (Langlands.Scheme.Modules.unitToPushforwardUnit j) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction j).counit.app
          (SheafOfModules.unit Y.ringCatSheaf) =
      (Langlands.Scheme.Modules.pullbackUnitIso j).hom := by
  have h := congrArg
    ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).symm
    (Langlands.Scheme.Modules.pullbackUnitAdjunction Y X j)
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] using h.symm

instance isIso_map_unitToPushforwardUnit :
    IsIso ((Scheme.Modules.pullback j).map
      (Langlands.Scheme.Modules.unitToPushforwardUnit j)) :=
  IsIso.of_isIso_fac_right (map_unitToPushforwardUnit_counit j)

/-- The second projection of the closure becomes invertible on the original open. -/
instance isIso_pullback_projection :
    IsIso ((Scheme.Modules.pullback j).map (projection j s)) := by
  exact ((IsPullback.of_hasPullback
    (Langlands.Scheme.Modules.unitToPushforwardUnit j)
    ((Scheme.Modules.pushforward j).map s)).map
      (Scheme.Modules.pullback j)).isIso_snd_of_isIso

/-- The actual pullback of the closure is the original module. -/
def restrictionIso : (Scheme.Modules.pullback j).obj (closure j s) ≅ D :=
  asIso ((Scheme.Modules.pullback j).map (projection j s)) ≪≫
    asIso ((Scheme.Modules.pullbackPushforwardAdjunction j).counit.app D)

/-- The restriction comparison preserves the original inclusion. -/
lemma restrictionIso_hom_inclusion :
    (Scheme.Modules.pullback j).map (inclusion j s) ≫
        (Langlands.Scheme.Modules.pullbackUnitIso j).hom =
      (restrictionIso j s).hom ≫ s := by
  change (Scheme.Modules.pullback j).map (inclusion j s) ≫
      (Langlands.Scheme.Modules.pullbackUnitIso j).hom =
    ((Scheme.Modules.pullback j).map (projection j s) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction j).counit.app D) ≫ s
  rw [← map_unitToPushforwardUnit_counit j, ← Category.assoc,
    ← Functor.map_comp, condition, Functor.map_comp, Category.assoc,
    (Scheme.Modules.pullbackPushforwardAdjunction j).counit_naturality s,
    Category.assoc]

end Langlands.AlgebraicGeometry.Picard.OpenImmersionIdeal
