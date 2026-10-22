import Langlands.Cohomology.DerivedComparison
import Mathlib.CategoryTheory.Action.Basic

/-!
# Actions on derived functors through translation functors

Let a monoid `G` act on an abelian category `C` through exact translation
functors `T g` preserving injective objects, compatibly with a functor
`Γ : C ⥤ D`. An equivariant object `F`, with structure maps
`(T g).obj F ⟶ F` satisfying the cocycle conditions, then carries an action
of `G` on the cohomology of `Γ` applied to any injective resolution of `F`.
The action of `g` is induced by a chain map lifting the structure map of `g`
along the translated resolution; lifts are unique up to homotopy.
-/

noncomputable section

namespace Langlands.Cohomology.TranslationAction

open CategoryTheory CategoryTheory.Limits Langlands.Cohomology.DerivedComparison

universe v u v' u' w

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (Γ : C ⥤ D) [Γ.Additive]
variable {G : Type w} [Monoid G] (T : G → C ⥤ C) [∀ g, (T g).Additive]
  [∀ g, (T g).PreservesHomology] [∀ g, (T g).PreservesInjectiveObjects]

/-- Compatibility data of the translation functors with each other and with
`Γ`. -/
structure Data where
  /-- Translation does not change `Γ`. -/
  sections : ∀ g, T g ⋙ Γ ≅ Γ
  /-- Translating by `h` and then by `g` is translating by `g * h`. -/
  comp : ∀ g h, T h ⋙ T g ≅ T (g * h)
  /-- Translating by `1` is the identity. -/
  one : T 1 ≅ 𝟭 C
  sections_comp : ∀ g h X, (sections g).hom.app ((T h).obj X) ≫ (sections h).hom.app X =
    Γ.map ((comp g h).hom.app X) ≫ (sections (g * h)).hom.app X
  sections_one : ∀ X, (sections 1).hom.app X = Γ.map (one.hom.app X)

variable {Γ T} (𝒯 : Data Γ T)

/-- An object with compatible structure maps from its translates. -/
structure Equivariant where
  /-- The underlying object. -/
  obj : C
  /-- The structure map of `g`. -/
  act : ∀ g, (T g).obj obj ⟶ obj
  act_one : act 1 = 𝒯.one.hom.app obj
  act_mul : ∀ g h, act (g * h) = (𝒯.comp g h).inv.app obj ≫ (T g).map (act h) ≫ act g

variable {𝒯}

/-- A chain map from the translated resolution lifting the structure map of
`g`. -/
def lift (F : Equivariant 𝒯) (g : G) (I : InjectiveResolution F.obj) :
    ((T g).mapHomologicalComplex _).obj I.cocomplex ⟶ I.cocomplex :=
  InjectiveResolution.desc (F.act g) I (mapInjectiveResolution (T g) I)

omit [Abelian D] [Γ.Additive] in
theorem lift_comm (F : Equivariant 𝒯) (g : G) (I : InjectiveResolution F.obj) :
    (mapInjectiveResolution (T g) I).ι ≫ lift F g I =
      (CochainComplex.single₀ C).map (F.act g) ≫ I.ι :=
  InjectiveResolution.desc_commutes _ _ _

variable (Γ) in
/-- The chain map on `Γ` of the resolution induced by `g`. -/
def chainMap (F : Equivariant 𝒯) (g : G) (I : InjectiveResolution F.obj) :
    (Γ.mapHomologicalComplex _).obj I.cocomplex ⟶ (Γ.mapHomologicalComplex _).obj I.cocomplex :=
  (NatIso.mapHomologicalComplex (𝒯.sections g) _).inv.app I.cocomplex ≫
    (Γ.mapHomologicalComplex _).map (lift F g I)

omit [Abelian D] [Γ.Additive] [∀ g, (T g).Additive] [∀ g, (T g).PreservesHomology]
  [∀ g, (T g).PreservesInjectiveObjects] in
/-- A chain map between injective resolutions lifts a morphism as soon as it
does so in degree zero. -/
theorem comm_of_comm_zero {X Y : C} {f : X ⟶ Y} {J : InjectiveResolution X}
    {I : InjectiveResolution Y} {φ : J.cocomplex ⟶ I.cocomplex}
    (h : J.ι.f 0 ≫ φ.f 0 = f ≫ I.ι.f 0) :
    J.ι ≫ φ = (CochainComplex.single₀ C).map f ≫ I.ι := by
  apply HomologicalComplex.from_single_hom_ext
  simpa only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] using h

omit [Abelian D] [Γ.Additive] in
/-- The lifting property of `lift` in degree zero. -/
theorem lift_comm_zero (F : Equivariant 𝒯) (g : G) (I : InjectiveResolution F.obj) :
    (T g).map (I.ι.f 0) ≫ (lift F g I).f 0 = F.act g ≫ I.ι.f 0 := by
  have h := congrArg (fun φ => φ.f 0) (lift_comm F g I)
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at h
  rw [← mapInjectiveResolution_ι_f_zero]
  exact h

omit [Abelian C] [Abelian D] [Γ.Additive] [∀ g, (T g).Additive] [∀ g, (T g).PreservesHomology]
  [∀ g, (T g).PreservesInjectiveObjects] in
/-- The inverse form of `Data.sections_comp`. -/
theorem sections_comp_inv (g h : G) (X : C) :
    (𝒯.sections h).inv.app X ≫ (𝒯.sections g).inv.app ((T h).obj X) =
      (𝒯.sections (g * h)).inv.app X ≫ Γ.map ((𝒯.comp g h).inv.app X) := by
  have h1 : ((𝒯.sections h).inv.app X ≫ (𝒯.sections g).inv.app ((T h).obj X)) ≫
      (Γ.map ((𝒯.comp g h).hom.app X) ≫ (𝒯.sections (g * h)).hom.app X) = 𝟙 _ := by
    rw [← 𝒯.sections_comp]
    simp
  have h2 : ((𝒯.sections (g * h)).inv.app X ≫ Γ.map ((𝒯.comp g h).inv.app X)) ≫
      (Γ.map ((𝒯.comp g h).hom.app X) ≫ (𝒯.sections (g * h)).hom.app X) = 𝟙 _ := by
    simp [← Γ.map_comp_assoc]
  exact (cancel_mono _).1 (h1.trans h2.symm)

/-- The composite lift for `g * h`: translate the lift of `h` by `g`, then
apply the lift of `g`. -/
def compositeLift (F : Equivariant 𝒯) (g h : G) (I : InjectiveResolution F.obj) :
    ((T (g * h)).mapHomologicalComplex _).obj I.cocomplex ⟶ I.cocomplex :=
  (NatIso.mapHomologicalComplex (𝒯.comp g h) _).inv.app I.cocomplex ≫
    ((T g).mapHomologicalComplex _).map (lift F h I) ≫ lift F g I

omit [Abelian D] [Γ.Additive] in
theorem compositeLift_comm (F : Equivariant 𝒯) (g h : G) (I : InjectiveResolution F.obj) :
    (mapInjectiveResolution (T (g * h)) I).ι ≫ compositeLift F g h I =
      (CochainComplex.single₀ C).map (F.act (g * h)) ≫ I.ι := by
  apply comm_of_comm_zero
  rw [mapInjectiveResolution_ι_f_zero]
  simp only [compositeLift, HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
    Functor.mapHomologicalComplex_map_f]
  have n1 := (𝒯.comp g h).inv.naturality (I.ι.f 0)
  simp only [Functor.comp_map] at n1
  erw [← Category.assoc, n1, Category.assoc, ← Category.assoc ((T g).map ((T h).map _)),
    ← (T g).map_comp, lift_comm_zero, (T g).map_comp, Category.assoc, lift_comm_zero, F.act_mul]
  simp only [Category.assoc]
  rfl

variable (Γ) in
/-- Composing the chain maps of `h` and `g` is homotopic to the chain map of
`g * h`. -/
def mulHomotopy (F : Equivariant 𝒯) (g h : G) (I : InjectiveResolution F.obj) :
    Homotopy (chainMap Γ F h I ≫ chainMap Γ F g I) (chainMap Γ F (g * h) I) := by
  have H : Homotopy (compositeLift F g h I) (lift F (g * h) I) :=
    InjectiveResolution.descHomotopy (F.act (g * h)) _ _ (compositeLift_comm F g h I)
      (lift_comm F (g * h) I)
  have e : chainMap Γ F h I ≫ chainMap Γ F g I =
      (NatIso.mapHomologicalComplex (𝒯.sections (g * h)) _).inv.app I.cocomplex ≫
        (Γ.mapHomologicalComplex _).map (compositeLift F g h I) := by
    ext n
    simp only [chainMap, compositeLift, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_inv_app_f, Functor.mapHomologicalComplex_map_f, Γ.map_comp,
      Category.assoc]
    have n1 := (𝒯.sections g).inv.naturality ((lift F h I).f n)
    simp only [Functor.comp_map] at n1
    rw [← Category.assoc (Γ.map ((lift F h I).f n)), n1]
    dsimp only [Functor.mapHomologicalComplex_obj_X]
    simp only [Category.assoc]
    rw [← Category.assoc ((𝒯.sections h).inv.app _), sections_comp_inv]
    simp only [Category.assoc]
  exact (Homotopy.ofEq e).trans ((Γ.mapHomotopy H).compLeft _)

omit [Abelian D] [Γ.Additive] in
theorem oneLift_comm (F : Equivariant 𝒯) (I : InjectiveResolution F.obj) :
    I.ι ≫ ((NatIso.mapHomologicalComplex 𝒯.one _).inv.app I.cocomplex ≫ lift F 1 I) =
      (CochainComplex.single₀ C).map (𝟙 F.obj) ≫ I.ι := by
  apply comm_of_comm_zero
  simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f]
  have n1 := 𝒯.one.inv.naturality (I.ι.f 0)
  simp only [Functor.id_map] at n1
  erw [← Category.assoc, n1, Category.assoc, lift_comm_zero, F.act_one]
  exact (Iso.inv_hom_id_app_assoc 𝒯.one F.obj (I.ι.f 0)).trans (Category.id_comp _).symm

omit [Abelian C] [Abelian D] [Γ.Additive] [∀ g, (T g).Additive] [∀ g, (T g).PreservesHomology]
  [∀ g, (T g).PreservesInjectiveObjects] in
theorem sections_one_inv (X : C) : (𝒯.sections 1).inv.app X = Γ.map (𝒯.one.inv.app X) := by
  rw [← cancel_mono ((𝒯.sections 1).hom.app X), Iso.inv_hom_id_app, 𝒯.sections_one,
    ← Γ.map_comp, Iso.inv_hom_id_app, Γ.map_id]
  rfl

variable (Γ) in
/-- The chain map of `1` is homotopic to the identity. -/
def oneHomotopy (F : Equivariant 𝒯) (I : InjectiveResolution F.obj) :
    Homotopy (chainMap Γ F 1 I) (𝟙 _) := by
  have H : Homotopy ((NatIso.mapHomologicalComplex 𝒯.one _).inv.app I.cocomplex ≫ lift F 1 I)
      (𝟙 I.cocomplex) :=
    InjectiveResolution.descHomotopy (𝟙 F.obj) _ _ (oneLift_comm F I) (by simp)
  have e : chainMap Γ F 1 I = (Γ.mapHomologicalComplex _).map
      ((NatIso.mapHomologicalComplex 𝒯.one _).inv.app I.cocomplex ≫ lift F 1 I) := by
    ext n
    simp only [chainMap, HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
      Functor.mapHomologicalComplex_map_f, Γ.map_comp, sections_one_inv]
  exact (Homotopy.ofEq e).trans ((Γ.mapHomotopy H).trans
    (Homotopy.ofEq ((Γ.mapHomologicalComplex _).map_id _)))

variable (Γ) in
/-- The action of `G` on the degree `n` cohomology of `Γ` applied to an
injective resolution of an equivariant object. -/
def homologyAction (F : Equivariant 𝒯) (I : InjectiveResolution F.obj) (n : ℕ) :
    G →* End (((Γ.mapHomologicalComplex _).obj I.cocomplex).homology n) where
  toFun g := HomologicalComplex.homologyMap (chainMap Γ F g I) n
  map_one' := by
    rw [(oneHomotopy Γ F I).homologyMap_eq n, HomologicalComplex.homologyMap_id]
    rfl
  map_mul' g h := by
    rw [End.mul_def, ← HomologicalComplex.homologyMap_comp,
      (mulHomotopy Γ F g h I).homologyMap_eq n]

variable (Γ) in
/-- The degree `n` cohomology of `Γ` applied to an injective resolution of an
equivariant object, as an object with an action of `G`. -/
def cohomologyAction (F : Equivariant 𝒯) (I : InjectiveResolution F.obj) (n : ℕ) :
    Action D G where
  V := ((Γ.mapHomologicalComplex _).obj I.cocomplex).homology n
  ρ := homologyAction Γ F I n

end Langlands.Cohomology.TranslationAction
