import Langlands.Geometry.FormalGroup.AtlasMorphism
import Langlands.Geometry.FormalGroup.OrderAction

/-! # Order actions on actual formal coordinate atlases -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Actual order actions on the chart laws, commuting with formal transitions. -/
structure OrderAction (D : Type w) [Ring D] [Algebra O D]
    (X : BasicAtlas O R σ) where
  chart : ∀ b : X.opens, ModuleLaw.OrderAction D (X.chart b)
  transition : ∀ (B : CommAlgCat.{v} R) (b c : X.opens)
    (hb : IsUnit (algebraMap R B b.val)) (hc : IsUnit (algebraMap R B c.val)) (a : D),
    (X.transition B b c hb hc).hom.comp
      (((chart b).map (coefficientLift (O := O) b.val B hb)).action a) =
      (((chart c).map (coefficientLift (O := O) c.val B hc)).action a).comp
        (X.transition B b c hb hc).hom

namespace OrderAction

variable {X : BasicAtlas O R σ} (E : OrderAction D X)

/-- Every order element gives an actual formal endomorphism of the atlas. -/
def endomorphism (a : D) : BasicAtlas.Hom X X rfl where
  hom B b hb := ((E.chart b).map (coefficientLift (O := O) b.val B hb)).action a
  natural φ b ha hb := by
    change (((E.chart b).action a).toHom.toCoordinateMap.map
      (coefficientLift (O := O) b.val _ ha).toRingHom).map φ.hom.toRingHom =
      ((E.chart b).action a).toHom.toCoordinateMap.map
        (coefficientLift (O := O) b.val _ hb).toRingHom
    rw [CoordinateMap.map_ringHom_comp]
    exact congrArg (fun f : Localization.Away b.val →ₐ[O] _ =>
      ((E.chart b).action a).toHom.toCoordinateMap.map f.toRingHom)
        (coefficientLift_comp (O := O) b.val φ ha hb)
  transition B b c hb hc := E.transition B b c hb hc a

/-- Compatible families, carrying the action constructed from formal chart maps. -/
@[nolint unusedArguments]
def Point (_E : OrderAction D X) (B : CommAlgCat.{v} R) := X.Point B

instance (B : CommAlgCat.{v} R) : AddCommGroup (E.Point B) :=
  inferInstanceAs (AddCommGroup (X.Point B))

instance (B : CommAlgCat.{v} R) : SMul D (E.Point B) :=
  ⟨fun a x => (E.endomorphism a).onPoints B x⟩

@[simp]
theorem smul_apply (B : CommAlgCat.{v} R) (a : D) (x : E.Point B) (t : X.ChartTest B) :
    (a • x).val t =
      (((E.chart t.chart).map (coefficientLift (O := O) t.chart.val t.algebra t.isUnit)).action a).onPoints
        (x.val t) := rfl

instance (B : CommAlgCat.{v} R) : Module D (E.Point B) where
  one_smul x := by
    apply Subtype.ext
    funext t
    change (((E.chart t.chart).map _).action 1).onPoints (x.val t) = x.val t
    rw [_root_.map_one]
    exact ModuleLaw.Hom.onPoints_id _
  mul_smul a b x := by
    apply Subtype.ext
    funext t
    change (((E.chart t.chart).map _).action (a * b)).onPoints (x.val t) =
      (((E.chart t.chart).map _).action a).onPoints
        ((((E.chart t.chart).map _).action b).onPoints (x.val t))
    rw [_root_.map_mul]
    exact ModuleLaw.Hom.onPoints_comp _ _ _
  smul_zero a := (E.endomorphism a).onPoints B |>.map_zero
  smul_add a x y := (E.endomorphism a).onPoints B |>.map_add x y
  add_smul a b x := by
    apply Subtype.ext
    funext t
    change (((E.chart t.chart).map _).action (a + b)).onPoints (x.val t) =
      (((E.chart t.chart).map _).action a).onPoints (x.val t) +
        (((E.chart t.chart).map _).action b).onPoints (x.val t)
    rw [_root_.map_add]
    exact ModuleLaw.Hom.onPoints_add _ _ _
  zero_smul x := by
    apply Subtype.ext
    funext t
    change (((E.chart t.chart).map _).action 0).onPoints (x.val t) = 0
    rw [_root_.map_zero]
    exact ModuleLaw.Hom.onPoints_zero _

/-- The order action restricts to the original O-action on compatible families. -/
theorem scalar_point (B : CommAlgCat.{v} R) (a : O) (x : E.Point B) :
    (algebraMap O D a) • x = (a • (show X.Point B from x) : X.Point B) := by
  apply Subtype.ext
  funext t
  change (((E.chart t.chart).map _).action (algebraMap O D a)).toHom.onPoints (x.val t) =
    (((X.chart t.chart).map _).action a).onPoints (x.val t)
  rw [ModuleLaw.OrderAction.extends_scalars]

/-- Coefficient maps of compatible families are linear over the full order. -/
def mapPoints {B C : CommAlgCat.{v} R} (φ : B ⟶ C) : E.Point B →ₗ[D] E.Point C where
  toFun := X.mapPoints φ
  map_add' := (X.mapPoints φ).map_add
  map_smul' a x := (E.endomorphism a).onPoints_natural φ x

/-- The constructed order-module functor on coefficient algebras. -/
def pointFunctor : CommAlgCat.{v} R ⥤ ModuleCat.{v + 1} D where
  obj B := ModuleCat.of D (E.Point B)
  map φ := ModuleCat.ofHom (E.mapPoints φ)
  map_id B := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact X.mapPoints_id B x
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact X.mapPoints_comp φ ψ x

/-- Restrict the actual order-module functor to algebras where pi is nilpotent. -/
def nilpPointFunctor (π : R) : Nilp.{v, v} R π ⥤ ModuleCat.{v + 1} D :=
  Nilp.forget R π ⋙ E.pointFunctor

/-- The chart module obtained by evaluating its actual formal order action. -/
abbrev ChartPoint (B : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R B b.val)) :=
  ((E.chart b).map (coefficientLift (O := O) b.val B hb)).Point Empty

/-- Evaluation at any chart test is linear for the order action. -/
def evaluation (B : CommAlgCat.{v} R) (t : X.ChartTest B) :
    E.Point B →ₗ[D] E.ChartPoint t.algebra t.chart t.isUnit where
  toFun x := x.val t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Over a principal open, the original chart equivalence is order-linear. -/
def chartEquiv {B : CommAlgCat.{v} R} (b : X.opens)
    (hb : IsUnit (algebraMap R B b.val)) : E.Point B ≃ₗ[D] E.ChartPoint B b hb :=
  LinearEquiv.ofBijective (E.evaluation B ⟨B, 𝟙 B, b, hb⟩) (X.chartEquiv b hb).bijective

end OrderAction

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
