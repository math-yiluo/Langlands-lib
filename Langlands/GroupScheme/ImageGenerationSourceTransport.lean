import Langlands.GroupScheme.ImageGenerationDominant
import Langlands.GroupScheme.ImageGenerationActions
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Generated-image factors across a schematically dominant source -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B : Scheme.{u}} {V W : Over B} {G : GroupScheme B}

/-- Apply a source morphism to every coordinate of the actual finite power. -/
def finitePowerMap (p : V ⟶ W) (n : ℕ) : finitePower V n ⟶ finitePower W n :=
  Pi.lift fun i : Fin n => Pi.π (fun _ : Fin n => V) i ≫ p

@[simp] theorem finitePowerMap_π (p : V ⟶ W) (n : ℕ) (i : Fin n) :
    finitePowerMap p n ≫ Pi.π (fun _ : Fin n => W) i =
      Pi.π (fun _ : Fin n => V) i ≫ p :=
  Pi.lift_comp_π _ i

/-- Ordered products commute with a morphism of their source schemes. -/
theorem orderedPowerMap_precomp (p : V ⟶ W) (f : W ⟶ G.X) (n : ℕ) :
    finitePowerMap p n ≫ orderedPowerMap f n = orderedPowerMap (p ≫ f) n := by
  rw [orderedPowerMap_points]
  simp only [finitePowerMap_π, Category.assoc]
  rfl

namespace GeneratedImage

variable (p : V ⟶ W) [IsSchemeTheoreticallyDominant p.left]
    (f : W ⟶ G.X) (D : GeneratedImage (p ≫ f))

private theorem sourceFactor_exists :
    ∃ q : W ⟶ D.group.X, q ≫ D.inclusion.hom.hom = f := by
  let : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
  exact exists_over_factor_of_schematic_precomp
    D.inclusion.hom.hom p f D.factor D.factor_comp.symm

/-- The canonical generated-image factor descends through a schematically
dominant source morphism. The intermediate source need not be a group. -/
def sourceFactor : W ⟶ D.group.X :=
  Classical.choose (sourceFactor_exists p f D)

theorem sourceFactor_comp : D.sourceFactor p f ≫ D.inclusion.hom.hom = f :=
  Classical.choose_spec (sourceFactor_exists p f D)

theorem sourceFactor_precomp : p ≫ D.sourceFactor p f = D.factor := by
  exact D.factor_unique _ (by rw [Category.assoc, D.sourceFactor_comp p f])

/-- The original ordered power factors through the intermediate source power. -/
theorem sourceFactor_power (n : ℕ) :
    finitePowerMap p n ≫ orderedPowerMap (D.sourceFactor p f) n = D.powerMap n := by
  rw [orderedPowerMap_precomp, D.sourceFactor_precomp p f]
  rfl

/-- Dominance of the original power implies dominance of the descended power;
no separability or geometric property of the intermediate source is required. -/
theorem sourceFactor_power_isDominant (n : ℕ)
    (hn : IsDominant (D.powerMap n).left) :
    IsDominant (orderedPowerMap (D.sourceFactor p f) n).left := by
  have : IsDominant ((finitePowerMap p n).left ≫
      (orderedPowerMap (D.sourceFactor p f) n).left) := by
    change IsDominant
      (finitePowerMap p n ≫ orderedPowerMap (D.sourceFactor p f) n).left
    rw [D.sourceFactor_power p f n]
    exact hn
  exact IsDominant.of_comp (finitePowerMap p n).left
    (orderedPowerMap (D.sourceFactor p f) n).left

/-- A source point mapping to the ambient identity also maps to the identity
of the generated representative. -/
theorem sourceFactor_point (w₀ : 𝟙_ (Over B) ⟶ W) (hw₀ : w₀ ≫ f = 1) :
    w₀ ≫ D.sourceFactor p f = 1 := by
  let : Mono D.inclusion.hom.hom := D.represents.1
  apply (cancel_mono D.inclusion.hom.hom).1
  rw [Category.assoc, D.sourceFactor_comp p f, hw₀, MonObj.one_comp]

variable {S : GroupScheme B} (a : PointwiseSchemeAction S W)
    (b : AutomorphicAction S G)
    (hstable : b.IsStable (closedImageEnvelope (p ≫ f)))

/-- The descended factor is equivariant under the actual restricted action
whenever its ambient composite is equivariant. -/
theorem sourceFactor_equivariant
    (hf : a.IsEquivariant b.toPointwiseSchemeAction f) :
    a.IsEquivariant (D.action b hstable).toPointwiseSchemeAction
      (D.sourceFactor p f) := by
  let : Mono D.inclusion.hom.hom := D.represents.1
  intro T s w
  apply (cancel_mono D.inclusion.hom.hom).1
  change (a.act s w ≫ D.sourceFactor p f) ≫ D.inclusion.hom.hom =
    (D.action b hstable).act s (w ≫ D.sourceFactor p f) ≫ D.inclusion.hom.hom
  rw [Category.assoc, D.sourceFactor_comp p f, D.action_act_comp,
    Category.assoc, D.sourceFactor_comp p f]
  exact hf T s w

end GeneratedImage

end Langlands.GroupScheme
