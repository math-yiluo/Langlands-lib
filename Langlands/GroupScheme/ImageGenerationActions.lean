import Langlands.GroupScheme.PointwiseSchemeAction
import Langlands.GroupScheme.ImageGenerationProducts
import Langlands.GroupScheme.RepresentedAction

/-! # Scheme actions and equivariant generated-image product maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B : Scheme.{u}} {H G : GroupScheme B} {V W : Over B}

namespace PointwiseSchemeAction

variable (a : PointwiseSchemeAction H V)

/-- Equivariance on every test scheme. -/
def IsEquivariant (b : PointwiseSchemeAction H W) (f : V ⟶ W) : Prop :=
  ∀ (T : Over B) (h : T ⟶ H.X) (v : T ⟶ V), a.act h v ≫ f = b.act h (v ≫ f)

/-- All-test equivariance is equivalent to an equality of actual morphisms. -/
theorem isEquivariant_iff (b : PointwiseSchemeAction H W) (f : V ⟶ W) :
    a.IsEquivariant b f ↔
      a.hom ≫ f = b.act (fst H.X V) (snd H.X V ≫ f) := by
  constructor
  · intro hf
    simpa only [act, lift_fst_snd, Category.id_comp] using
      hf (H.X ⊗ V) (fst H.X V) (snd H.X V)
  · intro hf T h v
    have e := congrArg (fun g => lift h v ≫ g) hf
    change (lift h v ≫ a.hom) ≫ f = b.act h (v ≫ f)
    simpa only [Category.assoc, b.naturality, lift_fst, lift_snd_assoc] using e

private def finitePowerHom (n : ℕ) : H.X ⊗ finitePower V n ⟶ finitePower V n :=
  Pi.lift fun i : Fin n =>
    a.act (fst H.X (finitePower V n))
      (snd H.X (finitePower V n) ≫ Pi.π (fun _ : Fin n => V) i)

private theorem lift_finitePowerHom_π (n : ℕ) {T : Over B}
    (h : T ⟶ H.X) (x : T ⟶ finitePower V n) (i : Fin n) :
    (lift h x ≫ a.finitePowerHom n) ≫ Pi.π (fun _ : Fin n => V) i =
      a.act h (x ≫ Pi.π (fun _ : Fin n => V) i) := by
  rw [Category.assoc, finitePowerHom, Pi.lift_comp_π, a.naturality,
    lift_fst, lift_snd_assoc]

/-- The diagonal action on the actual finite power of the source. -/
def finitePower (n : ℕ) : PointwiseSchemeAction H (GroupScheme.finitePower V n) where
  hom := a.finitePowerHom n
  one_left x := by
    apply Pi.hom_ext
    intro i
    rw [a.lift_finitePowerHom_π, a.act_one_left]
  mul_left h h' x := by
    apply Pi.hom_ext
    intro i
    rw [a.lift_finitePowerHom_π, a.lift_finitePowerHom_π,
      a.lift_finitePowerHom_π, a.act_mul_left]

theorem finitePower_act_π (n : ℕ) {T : Over B} (h : T ⟶ H.X)
    (x : T ⟶ GroupScheme.finitePower V n) (i : Fin n) :
    (a.finitePower n).act h x ≫ Pi.π (fun _ : Fin n => V) i =
      a.act h (x ≫ Pi.π (fun _ : Fin n => V) i) :=
  a.lift_finitePowerHom_π n h x i

end PointwiseSchemeAction

namespace AutomorphicAction

theorem act_ofFn_prod (b : AutomorphicAction H G) {T : Over B}
    (h : T ⟶ H.X) {n : ℕ} (g : Fin n → (T ⟶ G.X)) :
    b.act h (List.ofFn g).prod = (List.ofFn fun i => b.act h (g i)).prod := by
  change (b.pointAut T h) (List.ofFn g).prod =
    (List.ofFn fun i => (b.pointAut T h) (g i)).prod
  simpa only [List.map_ofFn, Function.comp_def] using
    map_list_prod (b.pointAut T h) (List.ofFn g)

end AutomorphicAction

/-- Equivariance of ordered products for an arbitrary source action and an
automorphic action on the target. -/
theorem orderedPowerMap_equivariant (a : PointwiseSchemeAction H V) (b : AutomorphicAction H G)
    (f : V ⟶ G.X) (hf : a.IsEquivariant b.toPointwiseSchemeAction f) (n : ℕ) :
    (a.finitePower n).IsEquivariant b.toPointwiseSchemeAction (orderedPowerMap f n) := by
  intro T h x
  change (a.finitePower n).act h x ≫ orderedPowerMap f n =
    b.act h (x ≫ orderedPowerMap f n)
  rw [orderedPowerMap_points, orderedPowerMap_points, b.act_ofFn_prod]
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [a.finitePower_act_π]
  exact hf T h (x ≫ Pi.π (fun _ : Fin n => V) i)

namespace GeneratedImage

variable {f : V ⟶ G.X} (D : GeneratedImage f) (b : AutomorphicAction H G)
    (hStable : b.IsStable (closedImageEnvelope f))

/-- The restricted actual action on a stable representative of the envelope. -/
def action : AutomorphicAction H D.group :=
  b.onRepresentedSubgroup D.inclusion D.represents hStable

theorem action_act_comp {T : Over B} (h : T ⟶ H.X) (g : T ⟶ D.group.X) :
    (D.action b hStable).act h g ≫ D.inclusion.hom.hom =
      b.act h (g ≫ D.inclusion.hom.hom) :=
  b.onRepresentedSubgroup_act_comp D.inclusion D.represents hStable h g

theorem inclusion_equivariant :
    (D.action b hStable).toPointwiseSchemeAction.IsEquivariant b.toPointwiseSchemeAction D.inclusion.hom.hom :=
  fun _ h g => D.action_act_comp b hStable h g

theorem factor_equivariant (a : PointwiseSchemeAction H V)
    (hf : a.IsEquivariant b.toPointwiseSchemeAction f) :
    a.IsEquivariant (D.action b hStable).toPointwiseSchemeAction D.factor := by
  let : Mono D.inclusion.hom.hom := D.represents.1
  intro T h v
  apply (cancel_mono D.inclusion.hom.hom).1
  change (a.act h v ≫ D.factor) ≫ D.inclusion.hom.hom =
    (D.action b hStable).act h (v ≫ D.factor) ≫ D.inclusion.hom.hom
  rw [D.factor_comp_points, D.action_act_comp, D.factor_comp_points]
  exact hf T h v

theorem powerMap_equivariant (a : PointwiseSchemeAction H V)
    (hf : a.IsEquivariant b.toPointwiseSchemeAction f) (n : ℕ) :
    (a.finitePower n).IsEquivariant (D.action b hStable).toPointwiseSchemeAction (D.powerMap n) :=
  orderedPowerMap_equivariant a (D.action b hStable) D.factor
    (D.factor_equivariant b hStable a hf) n

end GeneratedImage

end Langlands.GroupScheme
