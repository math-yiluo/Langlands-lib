import Langlands.Geometry.FormalGroup.AtlasMorphism

/-! # The integral module of formal atlas homomorphisms -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

omit [Finite σ] [Finite τ] in
private theorem map_coefficientLift {a : R}
    (f : CoordinateMap (Localization.Away a) σ τ)
    {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (ha : IsUnit (algebraMap R A a)) (hb : IsUnit (algebraMap R B a)) :
    (f.map (coefficientLift (O := O) a A ha).toRingHom).map φ.hom.toRingHom =
      f.map (coefficientLift (O := O) a B hb).toRingHom := by
  rw [CoordinateMap.map_ringHom_comp]
  exact congrArg (fun g : Localization.Away a →ₐ[O] B => f.map g.toRingHom)
    (coefficientLift_comp (O := O) a φ ha hb)

namespace Hom

variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

/-- The zero map consists of zero formal homomorphisms on every test chart. -/
instance : Zero (Hom X Y h) :=
  ⟨{ hom := fun _ _ _ => 0
     natural := fun φ _ _ _ => CoordinateMap.map_zero φ.hom.toRingHom
     transition := by intro A b c hb hc; simp }⟩

/-- Addition uses each target chart's formal group law. -/
instance : Add (Hom X Y h) :=
  ⟨fun f g => {
    hom := fun A b hb => f.hom A b hb + g.hom A b hb
    natural := by
      intro A B φ b ha hb
      change (((Y.chart b).groupLaw.addition.map
        (coefficientLift (O := O) b.val A ha).toRingHom).comp
        ((f.hom A b ha).toHom.toCoordinateMap.pair
          (g.hom A b ha).toHom.toCoordinateMap)).map φ.hom.toRingHom =
        ((Y.chart b).groupLaw.addition.map
          (coefficientLift (O := O) b.val B hb).toRingHom).comp
          ((f.hom B b hb).toHom.toCoordinateMap.pair
            (g.hom B b hb).toHom.toCoordinateMap)
      rw [CoordinateMap.map_comp, CoordinateMap.map_pair,
        map_coefficientLift, f.natural, g.natural]
    transition := by
      intro A b c hb hc
      rw [ModuleLaw.Hom.comp_add, ModuleLaw.Hom.add_comp,
        f.transition, g.transition] }⟩

/-- Scalars postcompose each actual chart map with its target O-action. -/
instance : SMul O (Hom X Y h) :=
  ⟨fun a f => {
    hom := fun A b hb => a • f.hom A b hb
    natural := by
      intro A B φ b ha hb
      change ((((Y.chart b).action a).toCoordinateMap.map
        (coefficientLift (O := O) b.val A ha).toRingHom).comp
        (f.hom A b ha).toHom.toCoordinateMap).map φ.hom.toRingHom =
        (((Y.chart b).action a).toCoordinateMap.map
          (coefficientLift (O := O) b.val B hb).toRingHom).comp
          (f.hom B b hb).toHom.toCoordinateMap
      rw [CoordinateMap.map_comp, map_coefficientLift, f.natural]
    transition := by
      intro A b c hb hc
      rw [ModuleLaw.Hom.comp_smul, ModuleLaw.Hom.smul_comp, f.transition] }⟩

/-- Negation is multiplication by minus one on the actual formal maps. -/
instance : Neg (Hom X Y h) := ⟨fun f => (-1 : O) • f⟩

@[simp]
theorem zero_hom (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (0 : Hom X Y h).hom A b hb = 0 := rfl

@[simp]
theorem add_hom (f g : Hom X Y h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (f + g).hom A b hb = f.hom A b hb + g.hom A b hb := rfl

@[simp]
theorem smul_hom (a : O) (f : Hom X Y h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (a • f).hom A b hb = a • f.hom A b hb := rfl

@[simp]
theorem neg_hom (f : Hom X Y h) (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (-f).hom A b hb = -(f.hom A b hb) := neg_one_smul O _

instance : AddCommGroup (Hom X Y h) where
  add_assoc f g q := by apply ext; intro A b hb; exact add_assoc _ _ _
  zero_add f := by apply ext; intro A b hb; exact zero_add _
  add_zero f := by apply ext; intro A b hb; exact add_zero _
  neg_add_cancel f := by
    apply ext
    intro A b hb
    rw [add_hom, neg_hom, zero_hom, neg_add_cancel]
  add_comm f g := by apply ext; intro A b hb; exact add_comm _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module O (Hom X Y h) where
  one_smul f := by apply ext; intro A b hb; exact one_smul O _
  mul_smul a b f := by apply ext; intro A c hc; exact mul_smul _ _ _
  smul_zero a := by apply ext; intro A b hb; exact smul_zero _
  smul_add a f g := by apply ext; intro A b hb; exact smul_add _ _ _
  add_smul a b f := by apply ext; intro A c hc; exact add_smul _ _ _
  zero_smul f := by apply ext; intro A b hb; exact zero_smul O _

/-- Evaluation on a test chart is linear in the actual formal atlas map. -/
def chartLinear (A : CommAlgCat.{v} R) (b : Y.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    Hom X Y h →ₗ[O] ModuleLaw.Hom
      ((X.chart (sourceChart h b)).map (coefficientLift (O := O) b.val A hb))
      ((Y.chart b).map (coefficientLift (O := O) b.val A hb)) where
  toFun f := f.hom A b hb
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem onPoints_zero (A : CommAlgCat.{v} R) (x : X.Point A) :
    (0 : Hom X Y h).onPoints A x = 0 := by
  apply Subtype.ext
  funext t
  exact ModuleLaw.Hom.onPoints_zero _

@[simp]
theorem onPoints_add (f g : Hom X Y h) (A : CommAlgCat.{v} R) (x : X.Point A) :
    (f + g).onPoints A x = f.onPoints A x + g.onPoints A x := by
  apply Subtype.ext
  funext t
  exact ModuleLaw.Hom.onPoints_add _ _ _

@[simp]
theorem onPoints_neg (f : Hom X Y h) (A : CommAlgCat.{v} R) (x : X.Point A) :
    (-f).onPoints A x = -(f.onPoints A x) := by
  apply Subtype.ext
  funext t
  change ((-f).hom t.algebra t.chart t.isUnit).onPoints _ = _
  rw [neg_hom]
  exact ModuleLaw.Hom.onPoints_neg _ _

@[simp]
theorem onPoints_smul (a : O) (f : Hom X Y h) (A : CommAlgCat.{v} R) (x : X.Point A) :
    (a • f).onPoints A x = a • f.onPoints A x := by
  apply Subtype.ext
  funext t
  exact ModuleLaw.Hom.onPoints_smul _ _ _

/-- Evaluation on all compatible families is O-linear in the formal atlas map. -/
def onPointsLinear (A : CommAlgCat.{v} R) :
    Hom X Y h →ₗ[O] (X.Point A →ₗ[O] Y.Point A) where
  toFun f := f.onPoints A
  map_add' f g := by apply LinearMap.ext; intro x; exact onPoints_add f g A x
  map_smul' a f := by apply LinearMap.ext; intro x; exact onPoints_smul a f A x

@[simp]
theorem comp_add (g : Hom Y Z k) (f₁ f₂ : Hom X Y h) :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ := by
  apply ext
  intro A b hb
  exact ModuleLaw.Hom.comp_add _ _ _

@[simp]
theorem add_comp (g₁ g₂ : Hom Y Z k) (f : Hom X Y h) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := by
  apply ext
  intro A b hb
  exact ModuleLaw.Hom.add_comp _ _ _

@[simp]
theorem comp_smul (g : Hom Y Z k) (a : O) (f : Hom X Y h) :
    g.comp (a • f) = a • g.comp f := by
  apply ext
  intro A b hb
  exact ModuleLaw.Hom.comp_smul _ _ _

@[simp]
theorem smul_comp (a : O) (g : Hom Y Z k) (f : Hom X Y h) :
    (a • g).comp f = a • g.comp f := by
  apply ext
  intro A b hb
  exact ModuleLaw.Hom.smul_comp _ _ _

@[simp]
theorem comp_zero (g : Hom Y Z k) : g.comp (0 : Hom X Y h) = 0 := by
  apply ext
  intro A b hb
  exact ModuleLaw.Hom.comp_zero _

@[simp]
theorem zero_comp (f : Hom X Y h) : (0 : Hom Y Z k).comp f = 0 := by
  apply ext
  intro A b hb
  exact ModuleLaw.Hom.zero_comp _

/-- Composition is O-bilinear on actual formal atlas maps. -/
def compLinear : Hom Y Z k →ₗ[O] Hom X Y h →ₗ[O] Hom X Z (h.trans k) where
  toFun g := {
    toFun := g.comp
    map_add' := comp_add g
    map_smul' := comp_smul g }
  map_add' g₁ g₂ := by
    apply LinearMap.ext
    intro f
    exact add_comp g₁ g₂ f
  map_smul' a g := by
    apply LinearMap.ext
    intro f
    exact smul_comp a g f

/-- Formal atlas endomorphisms form a ring under their actual composition. -/
instance : Ring (Hom X X rfl) where
  mul := comp
  one := id X
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  left_distrib := comp_add
  right_distrib := add_comp
  zero_mul := zero_comp
  mul_zero := comp_zero

end Hom

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
