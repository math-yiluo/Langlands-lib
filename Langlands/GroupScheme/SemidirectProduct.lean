import Langlands.GroupScheme.SubgroupFunctor
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.GroupTheory.SemidirectProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-!
# Semidirect products of group objects

A morphism `H ⊗ N ⟶ N` acting by group automorphisms on generalized points makes `N ⊗ H`
a group object whose generalized points form the semidirect product of the point groups.
For two homomorphisms `i : H ⟶ G` and `j : N ⟶ G` of group schemes, with `j` monic and
`range j` stable under conjugation by points of `range i`, conjugation gives such an action
and `(n, h) ↦ j n * i h` is a homomorphism from the semidirect product to `G`.
-/

noncomputable section

universe v u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Semidirect

section Generic

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A morphism of monoid objects that is multiplicative on generalized points is a monoid
morphism. -/
theorem isMonHom_of_mul_comp {M N : C} [MonObj M] [GrpObj N] (f : M ⟶ N)
    (h : ∀ {X : C} (x y : X ⟶ M), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f where
  one_hom := by
    have h1 := h (1 : 𝟙_ C ⟶ M) 1
    rw [_root_.mul_one] at h1
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact left_eq_mul.mp h1
  mul_hom := by
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, h, MonObj.comp_mul]
    simp

/-- An action of the group object `H` on the group object `N` by group automorphisms,
expressed on generalized points. -/
structure AutAction (H N : C) [GrpObj H] [GrpObj N] where
  /-- The action morphism. -/
  act : H ⊗ N ⟶ N
  one_act : ∀ {T : C} (n : T ⟶ N), lift 1 n ≫ act = n
  mul_act : ∀ {T : C} (h h' : T ⟶ H) (n : T ⟶ N),
    lift (h * h') n ≫ act = lift h (lift h' n ≫ act) ≫ act
  act_mul : ∀ {T : C} (h : T ⟶ H) (n n' : T ⟶ N),
    lift h (n * n') ≫ act = (lift h n ≫ act) * (lift h n' ≫ act)

namespace AutAction

variable {H N : C} [GrpObj H] [GrpObj N] (a : AutAction H N)

/-- The action of `T`-points of `H` on `T`-points of `N` by group automorphisms. -/
def autHom (T : C) : (T ⟶ H) →* MulAut (T ⟶ N) where
  toFun h :=
    { toFun := fun n => lift h n ≫ a.act
      invFun := fun n => lift h⁻¹ n ≫ a.act
      left_inv := fun n => by
        simp only
        rw [← a.mul_act, inv_mul_cancel, a.one_act]
      right_inv := fun n => by
        simp only
        rw [← a.mul_act, mul_inv_cancel, a.one_act]
      map_mul' := a.act_mul h }
  map_one' := MulEquiv.ext fun n => a.one_act n
  map_mul' h h' := MulEquiv.ext fun n => a.mul_act h h' n

theorem autHom_apply {T : C} (h : T ⟶ H) (n : T ⟶ N) :
    a.autHom T h n = lift h n ≫ a.act :=
  rfl

/-- Precomposition with a morphism of tests, as a group homomorphism of point groups. -/
def precomp {T T' : C} (f : T' ⟶ T) (X : C) [GrpObj X] : (T ⟶ X) →* (T' ⟶ X) where
  toFun x := f ≫ x
  map_one' := MonObj.comp_one f
  map_mul' x y := MonObj.comp_mul f x y

/-- The presheaf of semidirect products of point groups. -/
def pointsFunctor : Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of ((unop T ⟶ N) ⋊[a.autHom (unop T)] (unop T ⟶ H))
  map f := GrpCat.ofHom (SemidirectProduct.map (precomp f.unop N) (precomp f.unop H)
    (fun h => by
      ext n
      simp [autHom, precomp, comp_lift_assoc]))
  map_id T := by
    ext x
    · exact Category.id_comp _
    · exact Category.id_comp _
  map_comp f g := by
    ext x
    · exact (Category.assoc _ _ _)
    · exact (Category.assoc _ _ _)

/-- The object `N ⊗ H` represents the presheaf of semidirect products. -/
def representableBy : (a.pointsFunctor ⋙ forget _).RepresentableBy (N ⊗ H) where
  homEquiv {T} :=
    { toFun := fun x =>
        (⟨x ≫ fst N H, x ≫ snd N H⟩ : (T ⟶ N) ⋊[a.autHom T] (T ⟶ H))
      invFun := fun p => lift (SemidirectProduct.left p) (SemidirectProduct.right p)
      left_inv := fun x => lift_comp_fst_snd x
      right_inv := fun p => by
        apply SemidirectProduct.ext
        · exact lift_fst _ _
        · exact lift_snd _ _ }
  homEquiv_comp f x := by
    apply SemidirectProduct.ext
    · exact Category.assoc _ _ _
    · exact Category.assoc _ _ _

/-- The underlying object `N ⊗ H` of the semidirect product. -/
def obj (_ : AutAction H N) : C := N ⊗ H

instance instSemidirectProduct1 : GrpObj a.obj :=
  GrpObj.ofRepresentableBy (N ⊗ H) a.pointsFunctor a.representableBy

/-- The `N`-coordinate of the semidirect product. -/
def left : a.obj ⟶ N := fst N H

/-- The `H`-coordinate of the semidirect product. -/
def right : a.obj ⟶ H := snd N H

/-- The point of the semidirect product with given coordinates. -/
def pt {T : C} (n : T ⟶ N) (h : T ⟶ H) : T ⟶ a.obj := lift n h

@[simp, reassoc]
theorem pt_left {T : C} (n : T ⟶ N) (h : T ⟶ H) : a.pt n h ≫ a.left = n :=
  lift_fst _ _

@[simp, reassoc]
theorem pt_right {T : C} (n : T ⟶ N) (h : T ⟶ H) : a.pt n h ≫ a.right = h :=
  lift_snd _ _

theorem hom_ext {T : C} {x y : T ⟶ a.obj} (hl : x ≫ a.left = y ≫ a.left)
    (hr : x ≫ a.right = y ≫ a.right) : x = y :=
  CartesianMonoidalCategory.hom_ext _ _ hl hr

theorem eta {T : C} (x : T ⟶ a.obj) : a.pt (x ≫ a.left) (x ≫ a.right) = x :=
  lift_comp_fst_snd x

private theorem homEquiv_mul {T : C} (x y : T ⟶ a.obj) :
    a.representableBy.homEquiv (x * y) =
      a.representableBy.homEquiv x * a.representableBy.homEquiv y :=
  ((yonedaGrpObjIsoOfRepresentableBy (N ⊗ H) a.pointsFunctor a.representableBy).hom.app
    (op T)).hom.map_mul x y

private theorem homEquiv_one {T : C} :
    a.representableBy.homEquiv (1 : T ⟶ a.obj) = 1 :=
  ((yonedaGrpObjIsoOfRepresentableBy (N ⊗ H) a.pointsFunctor a.representableBy).hom.app
    (op T)).hom.map_one

/-- The `N`-coordinate of a product of points. -/
theorem mul_left {T : C} (x y : T ⟶ a.obj) :
    (x * y) ≫ a.left = (x ≫ a.left) * (lift (x ≫ a.right) (y ≫ a.left) ≫ a.act) :=
  congrArg SemidirectProduct.left (a.homEquiv_mul x y)

/-- The `H`-coordinate of a product of points. -/
theorem mul_right {T : C} (x y : T ⟶ a.obj) :
    (x * y) ≫ a.right = (x ≫ a.right) * (y ≫ a.right) :=
  congrArg SemidirectProduct.right (a.homEquiv_mul x y)

theorem one_left {T : C} : (1 : T ⟶ a.obj) ≫ a.left = 1 :=
  congrArg SemidirectProduct.left (a.homEquiv_one (T := T))

theorem one_right {T : C} : (1 : T ⟶ a.obj) ≫ a.right = 1 :=
  congrArg SemidirectProduct.right (a.homEquiv_one (T := T))

instance instSemidirectProduct2 : IsMonHom a.right :=
  isMonHom_of_mul_comp _ fun x y => a.mul_right x y

/-- The inclusion of `N` into the semidirect product. -/
def inl : N ⟶ a.obj := a.pt (𝟙 N) 1

/-- The inclusion of `H` into the semidirect product. -/
def inr : H ⟶ a.obj := a.pt 1 (𝟙 H)

end AutAction

end Generic

section GroupScheme

variable {S : Scheme.{u}} {G H N : GroupScheme S} (i : H ⟶ G) (j : N ⟶ G) [Mono j.hom.hom]

/-- Conjugation by points of `range i` preserves `range j`. -/
def ConjStable : Prop :=
  ∀ (T : Over S) (h : T ⟶ H.X) (n : T ⟶ N.X),
    (h ≫ i.hom.hom) * (n ≫ j.hom.hom) * (h ≫ i.hom.hom)⁻¹ ∈
      (SubgroupFunctor.range j).carrier T

omit [Mono j.hom.hom] in
theorem conjStable_of_isNormal (hN : (SubgroupFunctor.range j).IsNormal) : ConjStable i j :=
  fun T _ n => hN T _ _ (Subgroup.mem_top _) (SubgroupFunctor.mem_range.mpr ⟨n, rfl⟩)

variable {i j}

/-- The conjugation action morphism `H ⊗ N ⟶ N`, `(h, n) ↦ i h * n * (i h)⁻¹`. -/
def conjAct (hc : ConjStable i j) : H.X ⊗ N.X ⟶ N.X :=
  Classical.choose (SubgroupFunctor.mem_range.mp (hc _ (fst H.X N.X) (snd H.X N.X)))

omit [Mono j.hom.hom] in
theorem conjAct_comp (hc : ConjStable i j) {T : Over S} (h : T ⟶ H.X) (n : T ⟶ N.X) :
    (lift h n ≫ conjAct hc) ≫ j.hom.hom =
      (h ≫ i.hom.hom) * (n ≫ j.hom.hom) * (h ≫ i.hom.hom)⁻¹ := by
  rw [Category.assoc, conjAct,
    Classical.choose_spec (SubgroupFunctor.mem_range.mp (hc _ (fst H.X N.X) (snd H.X N.X))),
    MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc]

/-- Conjugation by `range i` as an action of `H` on `N` by automorphisms. -/
def conjAction (hc : ConjStable i j) : AutAction H.X N.X where
  act := conjAct hc
  one_act n := by
    apply (cancel_mono j.hom.hom).mp
    rw [conjAct_comp, MonObj.one_comp, _root_.one_mul, inv_one, _root_.mul_one]
  mul_act h h' n := by
    apply (cancel_mono j.hom.hom).mp
    rw [conjAct_comp, conjAct_comp, conjAct_comp, MonObj.mul_comp]
    group
  act_mul h n n' := by
    apply (cancel_mono j.hom.hom).mp
    rw [conjAct_comp, MonObj.mul_comp, MonObj.mul_comp, conjAct_comp, conjAct_comp]
    group

@[simp]
theorem conjAction_act (hc : ConjStable i j) : (conjAction hc).act = conjAct hc :=
  rfl

/-- The semidirect product group scheme `N ⋊ H` for the conjugation action. -/
abbrev group (hc : ConjStable i j) : GroupScheme S := Grp.mk (conjAction hc).obj

/-- The morphism `(n, h) ↦ j n * i h`. -/
def mulMap (hc : ConjStable i j) : (group hc).X ⟶ G.X :=
  ((conjAction hc).left ≫ j.hom.hom) * ((conjAction hc).right ≫ i.hom.hom)

theorem mulMap_mul (hc : ConjStable i j) {T : Over S} (x y : T ⟶ (group hc).X) :
    (x * y) ≫ mulMap hc = (x ≫ mulMap hc) * (y ≫ mulMap hc) := by
  simp only [mulMap, MonObj.comp_mul, ← Category.assoc, AutAction.mul_left,
    AutAction.mul_right]
  rw [MonObj.mul_comp, MonObj.mul_comp, conjAction_act, conjAct_comp]
  group

instance instSemidirectProduct3 (hc : ConjStable i j) : IsMonHom (mulMap hc) :=
  isMonHom_of_mul_comp _ fun x y => mulMap_mul hc x y

/-- The homomorphism `N ⋊ H ⟶ G`, `(n, h) ↦ j n * i h`. -/
def mulHom (hc : ConjStable i j) : group hc ⟶ G :=
  Grp.homMk (mulMap hc)

@[simp]
theorem mulHom_hom_hom (hc : ConjStable i j) : (mulHom hc).hom.hom = mulMap hc :=
  rfl

@[reassoc]
theorem pt_mulMap (hc : ConjStable i j) {T : Over S} (n : T ⟶ N.X) (h : T ⟶ H.X) :
    (conjAction hc).pt n h ≫ mulMap hc = (n ≫ j.hom.hom) * (h ≫ i.hom.hom) := by
  rw [mulMap, MonObj.comp_mul, AutAction.pt_left_assoc, AutAction.pt_right_assoc]

@[reassoc]
theorem inl_mulMap (hc : ConjStable i j) : (conjAction hc).inl ≫ mulMap hc = j.hom.hom := by
  rw [AutAction.inl, pt_mulMap, Category.id_comp, MonObj.one_comp, _root_.mul_one]

@[reassoc]
theorem inr_mulMap (hc : ConjStable i j) : (conjAction hc).inr ≫ mulMap hc = i.hom.hom := by
  rw [AutAction.inr, pt_mulMap, Category.id_comp, MonObj.one_comp, _root_.one_mul]

end GroupScheme

end Langlands.GroupScheme.Semidirect
