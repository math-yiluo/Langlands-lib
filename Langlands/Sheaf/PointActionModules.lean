import Langlands.MathlibBase

/-!
# Fibres of sheaves of modules at a point with a group action

Let `Φ` be a point of a site `(C, J)` and let a group `G` act on its fibre functor through
`act : G →* End Φ.fiber`. For a commutative ring `Λ`, `G` acts on the fibre `Φ.presheafFiber.obj P`
of every presheaf of `Λ`-modules `P` by `[X, x, t] ↦ [X, σ • x, t]`
(`Langlands.Sheaf.PointActionModules.fiberRepresentation`), which gives a functor
`sheafFiberRep` from sheaves of `Λ`-modules to `Rep Λ G`. In the other direction, a
representation `M` gives the sheaf `equivariantSheaf` of `G`-equivariant maps `Φ.fiber.obj X → M`.
The unit `toEquivariantSheaf` (a section goes to its germs) and the counit `fromEquivariantSheaf`
(`[X, x, f] ↦ f x`) are natural and satisfy the triangle identity
`sheafFiberRep_map_toEquivariantSheaf_comp_fromEquivariantSheaf`.

These are the `Λ`-linear versions of the constructions of weil-conjectures's
`CategoryTheory.GrothendieckTopology.Point.sheafFiberAction` and
`CategoryTheory.GrothendieckTopology.Point.equivariantSheaf` for abelian sheaves.
-/

noncomputable section

universe w v u u' uΛ

open CategoryTheory Limits Opposite

namespace Langlands.Sheaf.PointActionModules

open GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {G : Type u'} [Group G] (act : G →* End Φ.fiber)

/-- The endomorphism of the point `Φ` given by the action of `σ` on its fibre functor. -/
def actHom (σ : G) : Φ ⟶ Φ :=
  ⟨(act σ).asHom⟩

/-- `σ * τ` acts on the fibre by `τ` first, then `σ`. -/
lemma act_mul_app (σ τ : G) (X : C) (x : Φ.fiber.obj X) :
    (act (σ * τ)).asHom.app X x = (act σ).asHom.app X ((act τ).asHom.app X x) := by
  rw [map_mul, End.mul_asHom]
  rfl

@[simp]
lemma act_one_app (X : C) (x : Φ.fiber.obj X) : (act 1).asHom.app X x = x := by
  rw [map_one, End.one_asHom]
  rfl

section general

variable {A : Type*} [Category A] [HasColimitsOfSize.{w, w} A]

/-- The action of `σ` on the fibre of a presheaf: `[X, x, t] ↦ [X, σ • x, t]`. -/
def fiberAct (P : Cᵒᵖ ⥤ A) (σ : G) : Φ.presheafFiber.obj P ⟶ Φ.presheafFiber.obj P :=
  (Point.Hom.presheafFiber (actHom Φ act σ)).app P

/-- `fiberAct` sends the germ at `(X, x)` to the germ at `(X, σ • x)`. -/
@[reassoc (attr := simp)]
lemma toPresheafFiber_fiberAct (P : Cᵒᵖ ⥤ A) (σ : G) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ fiberAct Φ act P σ =
      Φ.toPresheafFiber X ((act σ).asHom.app X x) P := by
  simp [fiberAct, actHom]

/-- The identity acts trivially on fibres. -/
lemma fiberAct_one (P : Cᵒᵖ ⥤ A) : fiberAct Φ act P 1 = 𝟙 _ :=
  Φ.presheafFiber_hom_ext fun X x ↦ by
    rw [toPresheafFiber_fiberAct, act_one_app, Category.comp_id]

/-- The action on fibres is multiplicative: `σ * τ` acts by `τ`, then `σ`. -/
lemma fiberAct_mul (P : Cᵒᵖ ⥤ A) (σ τ : G) :
    fiberAct Φ act P (σ * τ) = fiberAct Φ act P τ ≫ fiberAct Φ act P σ :=
  Φ.presheafFiber_hom_ext fun X x ↦ by
    rw [toPresheafFiber_fiberAct, toPresheafFiber_fiberAct_assoc, toPresheafFiber_fiberAct,
      act_mul_app]

/-- The action on fibres commutes with the fibres of morphisms of presheaves. -/
@[reassoc]
lemma presheafFiber_map_fiberAct {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) (σ : G) :
    Φ.presheafFiber.map f ≫ fiberAct Φ act Q σ = fiberAct Φ act P σ ≫ Φ.presheafFiber.map f :=
  Φ.presheafFiber_hom_ext fun X x ↦ by
    rw [Point.toPresheafFiber_naturality_assoc, toPresheafFiber_fiberAct,
      toPresheafFiber_fiberAct_assoc, Point.toPresheafFiber_naturality]

end general

variable (Λ : Type uΛ) [CommRing Λ]

/-- The representation of `G` on the fibre at `Φ` of a presheaf of `Λ`-modules. -/
def fiberRepresentation (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) :
    Representation Λ G ((Φ.presheafFiber (A := ModuleCat.{w} Λ)).obj P) where
  toFun σ := (fiberAct Φ act P σ).hom
  map_one' := by rw [fiberAct_one]; rfl
  map_mul' σ τ := by rw [fiberAct_mul]; rfl

/-- `σ` sends the germ of `z` at `(X, x)` to the germ of `z` at `(X, σ • x)`. -/
lemma fiberRepresentation_toPresheafFiber (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) (σ : G) (X : C)
    (x : Φ.fiber.obj X) (z : P.obj (op X)) :
    fiberRepresentation Φ act Λ P σ (Φ.toPresheafFiber X x P z) =
      Φ.toPresheafFiber X ((act σ).asHom.app X x) P z :=
  congr($(toPresheafFiber_fiberAct Φ act P σ X x).hom z)

/-- The fibre at `Φ` of sheaves of `Λ`-modules, with its representation of `G`. -/
@[simps]
def sheafFiberRep : Sheaf J (ModuleCat.{w} Λ) ⥤ Rep.{w} Λ G where
  obj F := Rep.of (fiberRepresentation Φ act Λ F.obj)
  map {F F'} f := Rep.ofHom
    { toLinearMap := (Φ.presheafFiber.map f.hom).hom
      isIntertwining' := fun σ ↦
        congrArg ModuleCat.Hom.hom (presheafFiber_map_fiberAct Φ act f.hom σ).symm }
  map_id F := by
    ext v
    change (Φ.presheafFiber.map (𝟙 F.obj)).hom v = v
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    ext v
    change (Φ.presheafFiber.map (f.hom ≫ g.hom)).hom v = _
    rw [CategoryTheory.Functor.map_comp]
    rfl

section equivariant

variable (M : Rep.{w} Λ G)

/-- The `G`-equivariant maps `Φ.fiber.obj X → M`, a `Λ`-submodule of all maps. -/
def equivariantMaps (X : C) : Submodule Λ (Φ.fiber.obj X → M) where
  carrier := {f | ∀ (σ : G) (x : Φ.fiber.obj X), f ((act σ).asHom.app X x) = M.ρ σ (f x)}
  zero_mem' σ x := by simp
  add_mem' {f g} hf hg σ x := by simp [hf σ x, hg σ x]
  smul_mem' c f hf σ x := by simp [hf σ x]

/-- Precomposition with `Φ.fiber.map g` on equivariant maps. -/
def equivariantMapsComap {X Y : C} (g : Y ⟶ X) :
    equivariantMaps Φ act Λ M X →ₗ[Λ] equivariantMaps Φ act Λ M Y where
  toFun f := ⟨fun y ↦ f.1 (Φ.fiber.map g y), fun σ y ↦ by
    dsimp only
    rw [← f.2 σ, ← NatTrans.naturality_apply]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma equivariantMapsComap_apply_coe {X Y : C} (g : Y ⟶ X) (f : equivariantMaps Φ act Λ M X)
    (y : Φ.fiber.obj Y) :
    (equivariantMapsComap Φ act Λ M g f).1 y = f.1 (Φ.fiber.map g y) :=
  rfl

/-- The presheaf of `Λ`-modules of `G`-equivariant maps from the fibres of `Φ` to `M`. -/
@[simps]
def equivariantPresheaf : Cᵒᵖ ⥤ ModuleCat.{w} Λ where
  obj X := ModuleCat.of Λ (equivariantMaps Φ act Λ M X.unop)
  map g := ModuleCat.ofHom (equivariantMapsComap Φ act Λ M g.unop)
  map_id X := by
    ext f x
    simp
  map_comp f g := by
    ext h x
    simp

/-- Two elements of the fibre over `X` coming from the fibres over `Y₁` and `Y₂` come from a
common object over both. -/
lemma exists_of_fiber_map_eq {X Y₁ Y₂ : C} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) (y₁ : Φ.fiber.obj Y₁)
    (y₂ : Φ.fiber.obj Y₂) (h : Φ.fiber.map f₁ y₁ = Φ.fiber.map f₂ y₂) :
    ∃ (Z : C) (p₁ : Z ⟶ Y₁) (p₂ : Z ⟶ Y₂) (z : Φ.fiber.obj Z), p₁ ≫ f₁ = p₂ ≫ f₂ ∧
      Φ.fiber.map p₁ z = y₁ ∧ Φ.fiber.map p₂ z = y₂ := by
  let α₁ : Φ.fiber.elementsMk _ y₁ ⟶ Φ.fiber.elementsMk _ (Φ.fiber.map f₁ y₁) := ⟨f₁, rfl⟩
  let α₂ : Φ.fiber.elementsMk _ y₂ ⟶ Φ.fiber.elementsMk _ (Φ.fiber.map f₁ y₁) := ⟨f₂, h.symm⟩
  obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
  exact ⟨z.obj, q₁.hom, q₂.hom, z.val, congrArg (fun f ↦ f.hom) fac, q₁.map_val,
    q₂.map_val⟩

/-- The presheaf of equivariant maps is a sheaf: a compatible family of equivariant maps on a
covering sieve glues, since every point of the fibre over `X` lifts to the sieve. -/
lemma isSheaf_equivariantPresheaf : Presheaf.IsSheaf J (equivariantPresheaf Φ act Λ M) := by
  refine Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ?_
  refine Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{w}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  intro X R hR s hs
  have key {Y₁ Y₂ : C} {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X} (h₁ : R f₁) (h₂ : R f₂)
      (y₁ : Φ.fiber.obj Y₁) (y₂ : Φ.fiber.obj Y₂)
      (h : Φ.fiber.map f₁ y₁ = Φ.fiber.map f₂ y₂) :
      (s f₁ h₁).1 y₁ = (s f₂ h₂).1 y₂ := by
    obtain ⟨Z, p₁, p₂, z, fac, rfl, rfl⟩ := exists_of_fiber_map_eq Φ f₁ f₂ y₁ y₂ h
    exact congr_arg (fun g ↦ (Subtype.val g) z) (hs p₁ p₂ h₁ h₂ fac)
  choose Y f hf y hy using fun x ↦ Φ.jointly_surjective R hR x
  have hval {Y' : C} {f' : Y' ⟶ X} (h' : R f') (y' : Φ.fiber.obj Y') :
      (s (f (Φ.fiber.map f' y')) (hf _)).1 (y _) = (s f' h').1 y' :=
    key _ _ _ _ (hy _)
  let t : ((equivariantPresheaf Φ act Λ M ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙
      forget AddCommGrpCat.{w}).obj (op X) :=
    ⟨fun x ↦ (s (f x) (hf x)).1 (y x), fun σ x ↦ by
      have := hval (hf x) ((act σ).asHom.app _ (y x))
      rw [← NatTrans.naturality_apply, hy] at this
      dsimp only
      rw [this, (s (f x) (hf x)).2 σ (y x)]⟩
  refine ⟨t, fun Y' f' h' ↦ Subtype.ext (funext fun y' ↦ hval h' y'), fun t' ht' ↦ ?_⟩
  refine Subtype.ext (funext fun x ↦ ?_)
  have := congr_arg (fun g ↦ (Subtype.val g) (y x)) (ht' (f x) (hf x))
  simp only at this
  rw [← this]
  change t'.1 x = t'.1 (Φ.fiber.map (f x) (y x))
  rw [hy]

/-- The sheaf of `Λ`-modules of `G`-equivariant maps from the fibres of `Φ` to `M`. -/
@[simps]
def equivariantSheaf : Sheaf J (ModuleCat.{w} Λ) :=
  ⟨equivariantPresheaf Φ act Λ M, isSheaf_equivariantPresheaf Φ act Λ M⟩

end equivariant

/-- Postcomposition with a morphism of representations on equivariant maps. -/
def equivariantMapsMap {M N : Rep.{w} Λ G} (φ : M ⟶ N) (X : C) :
    equivariantMaps Φ act Λ M X →ₗ[Λ] equivariantMaps Φ act Λ N X where
  toFun f := ⟨fun x ↦ φ.hom (f.1 x), fun σ x ↦ by
    dsimp only
    rw [f.2 σ x]
    exact Rep.hom_comm_apply φ σ (f.1 x)⟩
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ ↦ map_smul _ _ _)

@[simp]
lemma equivariantMapsMap_apply_coe {M N : Rep.{w} Λ G} (φ : M ⟶ N) {X : C}
    (f : equivariantMaps Φ act Λ M X) (x : Φ.fiber.obj X) :
    (equivariantMapsMap Φ act Λ φ X f).1 x = φ.hom (f.1 x) :=
  rfl

/-- The functor sending a representation `M` to the sheaf of equivariant maps to `M`. -/
@[simps]
def equivariantSheafFunctor : Rep.{w} Λ G ⥤ Sheaf J (ModuleCat.{w} Λ) where
  obj M := equivariantSheaf Φ act Λ M
  map {M N} φ := ⟨{
    app X := ModuleCat.ofHom (equivariantMapsMap Φ act Λ φ X.unop)
    naturality _ _ _ := rfl }⟩

/-- A section `t` over `X` gives the equivariant map `x ↦ [X, x, t]`. -/
def toEquivariantMaps (F : Sheaf J (ModuleCat.{w} Λ)) (X : C) :
    F.obj.obj (op X) →ₗ[Λ] equivariantMaps Φ act Λ ((sheafFiberRep Φ act Λ).obj F) X where
  toFun t := ⟨fun x ↦ Φ.toPresheafFiber X x F.obj t, fun σ x ↦
    (fiberRepresentation_toPresheafFiber Φ act Λ F.obj σ X x t).symm⟩
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ ↦ map_smul _ _ _)

/-- The unit: a section `t` over `X` gives the equivariant map `x ↦ [X, x, t]`. -/
def toEquivariantSheaf (F : Sheaf J (ModuleCat.{w} Λ)) :
    F ⟶ (equivariantSheafFunctor Φ act Λ).obj ((sheafFiberRep Φ act Λ).obj F) :=
  ⟨{ app X := ModuleCat.ofHom (toEquivariantMaps Φ act Λ F X.unop)
     naturality X Y g := by
       ext t
       exact Subtype.ext (funext fun y ↦ Φ.toPresheafFiber_w_apply g.unop y F.obj t) }⟩

@[simp]
lemma toEquivariantSheaf_hom_app_apply_coe (F : Sheaf J (ModuleCat.{w} Λ)) (X : Cᵒᵖ)
    (t : F.obj.obj X) (x : Φ.fiber.obj X.unop) :
    ((toEquivariantSheaf Φ act Λ F).hom.app X t).1 x = Φ.toPresheafFiber X.unop x F.obj t :=
  rfl

/-- The unit is natural. -/
lemma toEquivariantSheaf_naturality {F F' : Sheaf J (ModuleCat.{w} Λ)} (g : F ⟶ F') :
    g ≫ toEquivariantSheaf Φ act Λ F' =
      toEquivariantSheaf Φ act Λ F ≫
        (equivariantSheafFunctor Φ act Λ).map ((sheafFiberRep Φ act Λ).map g) := by
  ext X t
  exact Subtype.ext (funext fun x ↦ (Φ.toPresheafFiber_naturality_apply g.hom X.unop x t).symm)

/-- Evaluation at `x` of equivariant maps. -/
def evalEquivariantMaps (M : Rep.{w} Λ G) (X : C) (x : Φ.fiber.obj X) :
    (equivariantPresheaf Φ act Λ M).obj (op X) ⟶ ModuleCat.of Λ M :=
  ModuleCat.ofHom
    { toFun f := f.1 x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

/-- The counit as a map of modules: `[X, x, f] ↦ f x`. -/
def fromEquivariantSheafHom (M : Rep.{w} Λ G) :
    Φ.presheafFiber.obj (equivariantPresheaf Φ act Λ M) ⟶ ModuleCat.of Λ M :=
  Φ.presheafFiberDesc (evalEquivariantMaps Φ act Λ M) (fun _ _ _ _ ↦ rfl)

/-- The counit sends the germ of `f` at `(X, x)` to `f x`. -/
@[reassoc (attr := simp)]
lemma toPresheafFiber_fromEquivariantSheafHom (M : Rep.{w} Λ G) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x (equivariantPresheaf Φ act Λ M) ≫ fromEquivariantSheafHom Φ act Λ M =
      evalEquivariantMaps Φ act Λ M X x :=
  Φ.toPresheafFiber_presheafFiberDesc _ _ X x

lemma toPresheafFiber_fromEquivariantSheafHom_apply (M : Rep.{w} Λ G) (X : C)
    (x : Φ.fiber.obj X) (f : (equivariantPresheaf Φ act Λ M).obj (op X)) :
    (fromEquivariantSheafHom Φ act Λ M).hom
      (Φ.toPresheafFiber X x (equivariantPresheaf Φ act Λ M) f) = f.1 x :=
  congr($(toPresheafFiber_fromEquivariantSheafHom Φ act Λ M X x).hom f)

/-- The counit is `G`-equivariant. -/
lemma fiberAct_fromEquivariantSheafHom (M : Rep.{w} Λ G) (σ : G) :
    fiberAct Φ act (equivariantPresheaf Φ act Λ M) σ ≫ fromEquivariantSheafHom Φ act Λ M =
      fromEquivariantSheafHom Φ act Λ M ≫ ModuleCat.ofHom (M.ρ σ) :=
  Φ.presheafFiber_hom_ext fun X x ↦ by
    rw [toPresheafFiber_fiberAct_assoc, toPresheafFiber_fromEquivariantSheafHom,
      toPresheafFiber_fromEquivariantSheafHom_assoc]
    ext f
    exact f.2 σ x

/-- The counit: `[X, x, f] ↦ f x`, a morphism of representations. -/
def fromEquivariantSheaf (M : Rep.{w} Λ G) :
    (sheafFiberRep Φ act Λ).obj ((equivariantSheafFunctor Φ act Λ).obj M) ⟶ M :=
  ConcreteCategory.ofHom (C := Rep.{w} Λ G) (X := Rep.of _) (Y := M)
    { toLinearMap := (fromEquivariantSheafHom Φ act Λ M).hom
      isIntertwining' := fun σ ↦
        congrArg ModuleCat.Hom.hom (fiberAct_fromEquivariantSheafHom Φ act Λ M σ) }

@[simp]
lemma fromEquivariantSheaf_hom_apply (M : Rep.{w} Λ G) (X : C) (x : Φ.fiber.obj X)
    (f : (equivariantPresheaf Φ act Λ M).obj (op X)) :
    (fromEquivariantSheaf Φ act Λ M).hom
      (Φ.toPresheafFiber X x (equivariantPresheaf Φ act Λ M) f) = f.1 x :=
  toPresheafFiber_fromEquivariantSheafHom_apply Φ act Λ M X x f

/-- The counit is natural. -/
lemma fromEquivariantSheaf_naturality {M N : Rep.{w} Λ G} (φ : M ⟶ N) :
    (sheafFiberRep Φ act Λ).map ((equivariantSheafFunctor Φ act Λ).map φ) ≫
        fromEquivariantSheaf Φ act Λ N =
      fromEquivariantSheaf Φ act Λ M ≫ φ := by
  have H : Φ.presheafFiber.map ((equivariantSheafFunctor Φ act Λ).map φ).hom ≫
      fromEquivariantSheafHom Φ act Λ N =
        fromEquivariantSheafHom Φ act Λ M ≫ ModuleCat.ofHom φ.hom.toLinearMap := by
    refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
    erw [Point.toPresheafFiber_naturality_assoc]
    erw [toPresheafFiber_fromEquivariantSheafHom, toPresheafFiber_fromEquivariantSheafHom_assoc]
    rfl
  apply Rep.hom_ext
  ext v
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom H) v

/-- The triangle identity: the fibre of the unit followed by the counit is the identity. -/
lemma sheafFiberRep_map_toEquivariantSheaf_comp_fromEquivariantSheaf
    (F : Sheaf J (ModuleCat.{w} Λ)) :
    (sheafFiberRep Φ act Λ).map (toEquivariantSheaf Φ act Λ F) ≫
        fromEquivariantSheaf Φ act Λ ((sheafFiberRep Φ act Λ).obj F) = 𝟙 _ := by
  have H : Φ.presheafFiber.map (toEquivariantSheaf Φ act Λ F).hom ≫
      fromEquivariantSheafHom Φ act Λ ((sheafFiberRep Φ act Λ).obj F) =
        𝟙 (Φ.presheafFiber.obj F.obj) := by
    refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
    erw [Point.toPresheafFiber_naturality_assoc]
    erw [toPresheafFiber_fromEquivariantSheafHom]
    ext t
    rfl
  apply Rep.hom_ext
  ext v
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom H) v

end Langlands.Sheaf.PointActionModules
