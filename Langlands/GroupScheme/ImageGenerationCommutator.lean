import Langlands.GroupScheme.ImageGenerationActions

/-! # Actual commutator sources and equivariance -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B : Scheme.{u}} {H G H₁ H₂ : GroupScheme B} {V W : Over B}

namespace PointwiseSchemeAction

variable (a : PointwiseSchemeAction H V) (c : PointwiseSchemeAction H W)

private def prodHom : H.X ⊗ (V ⊗ W) ⟶ V ⊗ W :=
  lift (a.act (fst H.X (V ⊗ W)) (snd H.X (V ⊗ W) ≫ fst V W))
    (c.act (fst H.X (V ⊗ W)) (snd H.X (V ⊗ W) ≫ snd V W))

private theorem lift_prodHom {T : Over B} (h : T ⟶ H.X) (x : T ⟶ V ⊗ W) :
    lift h x ≫ a.prodHom c =
      lift (a.act h (x ≫ fst V W)) (c.act h (x ≫ snd V W)) := by
  rw [prodHom, comp_lift, a.naturality, c.naturality,
    lift_fst, lift_snd_assoc, lift_snd_assoc]

/-- The diagonal action on the actual binary product of two source schemes. -/
def prod : PointwiseSchemeAction H (V ⊗ W) where
  hom := a.prodHom c
  one_left x := by
    rw [a.lift_prodHom c, a.act_one_left, c.act_one_left]
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  mul_left h h' x := by
    rw [a.lift_prodHom c, a.lift_prodHom c, a.lift_prodHom c,
      lift_fst, lift_snd, a.act_mul_left, c.act_mul_left]

theorem prod_act {T : Over B} (h : T ⟶ H.X) (x : T ⟶ V ⊗ W) :
    (a.prod c).act h x =
      lift (a.act h (x ≫ fst V W)) (c.act h (x ≫ snd V W)) :=
  a.lift_prodHom c h x

theorem prod_act_fst {T : Over B} (h : T ⟶ H.X) (x : T ⟶ V ⊗ W) :
    (a.prod c).act h x ≫ fst V W = a.act h (x ≫ fst V W) := by
  rw [prod_act, lift_fst]

theorem prod_act_snd {T : Over B} (h : T ⟶ H.X) (x : T ⟶ V ⊗ W) :
    (a.prod c).act h x ≫ snd V W = c.act h (x ≫ snd V W) := by
  rw [prod_act, lift_snd]

end PointwiseSchemeAction

/-- The actual commutator morphism on the product of two group schemes mapped
to the same ambient group. -/
def commutatorMap (j₁ : H₁ ⟶ G) (j₂ : H₂ ⟶ G) : H₁.X ⊗ H₂.X ⟶ G.X :=
  lift (fst H₁.X H₂.X ≫ j₁.hom.hom) (snd H₁.X H₂.X ≫ j₂.hom.hom) ≫
    GrpObj.commutator G.X

/-- The commutator formula on every test scheme, including nonreduced tests. -/
theorem commutatorMap_points (j₁ : H₁ ⟶ G) (j₂ : H₂ ⟶ G)
    {T : Over B} (x : T ⟶ H₁.X ⊗ H₂.X) :
    x ≫ commutatorMap j₁ j₂ =
      ((x ≫ fst H₁.X H₂.X) ≫ j₁.hom.hom) *
      ((x ≫ snd H₁.X H₂.X) ≫ j₂.hom.hom) *
      ((x ≫ fst H₁.X H₂.X) ≫ j₁.hom.hom)⁻¹ *
      ((x ≫ snd H₁.X H₂.X) ≫ j₂.hom.hom)⁻¹ := by
  rw [commutatorMap, ← Category.assoc, comp_lift,
    GrpObj.lift_commutator_eq_mul_mul_inv_inv]
  simp only [Category.assoc]

theorem commutatorMap_lift (j₁ : H₁ ⟶ G) (j₂ : H₂ ⟶ G)
    {T : Over B} (x : T ⟶ H₁.X) (y : T ⟶ H₂.X) :
    lift x y ≫ commutatorMap j₁ j₂ =
      (x ≫ j₁.hom.hom) * (y ≫ j₂.hom.hom) *
      (x ≫ j₁.hom.hom)⁻¹ * (y ≫ j₂.hom.hom)⁻¹ := by
  rw [commutatorMap_points, lift_fst, lift_snd]

@[simp] theorem commutatorMap_one_left (j₁ : H₁ ⟶ G) (j₂ : H₂ ⟶ G)
    {T : Over B} (y : T ⟶ H₂.X) :
    lift (1 : T ⟶ H₁.X) y ≫ commutatorMap j₁ j₂ = 1 := by
  simp [commutatorMap_lift, MonObj.one_comp]

@[simp] theorem commutatorMap_one_right (j₁ : H₁ ⟶ G) (j₂ : H₂ ⟶ G)
    {T : Over B} (x : T ⟶ H₁.X) :
    lift x (1 : T ⟶ H₂.X) ≫ commutatorMap j₁ j₂ = 1 := by
  simp [commutatorMap_lift, MonObj.one_comp]

/-- A common automorphic ambient action makes the actual commutator morphism
equivariant whenever both input homomorphisms are equivariant. -/
theorem commutatorMap_equivariant (a₁ : AutomorphicAction H H₁)
    (a₂ : AutomorphicAction H H₂) (b : AutomorphicAction H G)
    (j₁ : H₁ ⟶ G) (j₂ : H₂ ⟶ G)
    (hj₁ : a₁.toPointwiseSchemeAction.IsEquivariant b.toPointwiseSchemeAction j₁.hom.hom)
    (hj₂ : a₂.toPointwiseSchemeAction.IsEquivariant b.toPointwiseSchemeAction j₂.hom.hom) :
    (a₁.toPointwiseSchemeAction.prod a₂.toPointwiseSchemeAction).IsEquivariant b.toPointwiseSchemeAction
      (commutatorMap j₁ j₂) := by
  intro T h x
  change (a₁.toPointwiseSchemeAction.prod a₂.toPointwiseSchemeAction).act h x ≫ commutatorMap j₁ j₂ =
    b.act h (x ≫ commutatorMap j₁ j₂)
  rw [commutatorMap_points, commutatorMap_points, PointwiseSchemeAction.prod_act_fst,
    PointwiseSchemeAction.prod_act_snd, hj₁ T h _, hj₂ T h _]
  simp only [AutomorphicAction.toPointwiseSchemeAction_act, b.act_mul_right, b.act_inv]

end Langlands.GroupScheme
