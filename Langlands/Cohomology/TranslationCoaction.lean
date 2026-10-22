import Langlands.Cohomology.TranslationAction
import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# Actions on derived functors from structure maps into translates

This is the companion of `TranslationAction` for structure maps
`F ⟶ (T g).obj F` into the translates. Such maps out of an object are the
natural data for constant sheaves, whose maps out are governed by an
adjunction. The induced maps on cohomology compose in the opposite order, so
they form an action of the opposite monoid, and of the group itself through
inversion.
-/

noncomputable section

namespace Langlands.Cohomology.TranslationAction

open CategoryTheory CategoryTheory.Limits Langlands.Cohomology.DerivedComparison

universe v u v' u' w

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {Γ : C ⥤ D} [Γ.Additive]
variable {G : Type w} [Monoid G] {T : G → C ⥤ C} [∀ g, (T g).Additive]
  [∀ g, (T g).PreservesHomology] [∀ g, (T g).PreservesInjectiveObjects]
variable (𝒯 : Data Γ T)

/-- An object with compatible structure maps into its translates. -/
structure Coequivariant where
  /-- The underlying object. -/
  obj : C
  /-- The structure map of `g`. -/
  coact : ∀ g, obj ⟶ (T g).obj obj
  coact_one : coact 1 = 𝒯.one.inv.app obj
  coact_mul : ∀ g h, coact (g * h) = coact g ≫ (T g).map (coact h) ≫ (𝒯.comp g h).hom.app obj

variable {𝒯}

/-- A chain map into the translated resolution lifting the structure map of
`g`. -/
def colift (F : Coequivariant 𝒯) (g : G) (I : InjectiveResolution F.obj) :
    I.cocomplex ⟶ ((T g).mapHomologicalComplex _).obj I.cocomplex :=
  InjectiveResolution.desc (F.coact g) (mapInjectiveResolution (T g) I) I

omit [Abelian D] [Γ.Additive] in
theorem colift_comm (F : Coequivariant 𝒯) (g : G) (I : InjectiveResolution F.obj) :
    I.ι ≫ colift F g I =
      (CochainComplex.single₀ C).map (F.coact g) ≫ (mapInjectiveResolution (T g) I).ι :=
  InjectiveResolution.desc_commutes _ _ _

omit [Abelian D] [Γ.Additive] in
/-- The lifting property of `colift` in degree zero. -/
theorem colift_comm_zero (F : Coequivariant 𝒯) (g : G) (I : InjectiveResolution F.obj) :
    I.ι.f 0 ≫ (colift F g I).f 0 = F.coact g ≫ (T g).map (I.ι.f 0) := by
  have h := congrArg (fun φ => φ.f 0) (colift_comm F g I)
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at h
  rw [← mapInjectiveResolution_ι_f_zero]
  exact h

variable (Γ) in
/-- The chain map on `Γ` of the resolution induced by `g`. -/
def cochainMap (F : Coequivariant 𝒯) (g : G) (I : InjectiveResolution F.obj) :
    (Γ.mapHomologicalComplex _).obj I.cocomplex ⟶ (Γ.mapHomologicalComplex _).obj I.cocomplex :=
  (Γ.mapHomologicalComplex _).map (colift F g I) ≫
    (NatIso.mapHomologicalComplex (𝒯.sections g) _).hom.app I.cocomplex

/-- The composite lift for `g * h`: the lift of `g`, then the translate by `g`
of the lift of `h`, then the composition isomorphism. -/
def compositeColift (F : Coequivariant 𝒯) (g h : G) (I : InjectiveResolution F.obj) :
    I.cocomplex ⟶ ((T (g * h)).mapHomologicalComplex _).obj I.cocomplex :=
  colift F g I ≫ ((T g).mapHomologicalComplex _).map (colift F h I) ≫
    (NatIso.mapHomologicalComplex (𝒯.comp g h) _).hom.app I.cocomplex

omit [Abelian D] [Γ.Additive] in
theorem compositeColift_comm (F : Coequivariant 𝒯) (g h : G) (I : InjectiveResolution F.obj) :
    I.ι ≫ compositeColift F g h I =
      (CochainComplex.single₀ C).map (F.coact (g * h)) ≫
        (mapInjectiveResolution (T (g * h)) I).ι := by
  refine comm_of_comm_zero (I := mapInjectiveResolution (T (g * h)) I) ?_
  rw [mapInjectiveResolution_ι_f_zero]
  simp only [compositeColift, HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplex_map_f]
  have n1 := (𝒯.comp g h).hom.naturality (I.ι.f 0)
  simp only [Functor.comp_map] at n1
  erw [← Category.assoc, colift_comm_zero, Category.assoc, ← Category.assoc ((T g).map _),
    ← (T g).map_comp, colift_comm_zero, (T g).map_comp, Category.assoc, n1, F.coact_mul]
  simp only [Category.assoc]
  rfl

variable (Γ) in
/-- Composing the chain maps of `g` and `h` is homotopic to the chain map of
`g * h`. -/
def comulHomotopy (F : Coequivariant 𝒯) (g h : G) (I : InjectiveResolution F.obj) :
    Homotopy (cochainMap Γ F g I ≫ cochainMap Γ F h I) (cochainMap Γ F (g * h) I) := by
  have H : Homotopy (compositeColift F g h I) (colift F (g * h) I) :=
    InjectiveResolution.descHomotopy (F.coact (g * h)) _ _ (compositeColift_comm F g h I)
      (colift_comm F (g * h) I)
  have e : cochainMap Γ F g I ≫ cochainMap Γ F h I =
      (Γ.mapHomologicalComplex _).map (compositeColift F g h I) ≫
        (NatIso.mapHomologicalComplex (𝒯.sections (g * h)) _).hom.app I.cocomplex := by
    ext n
    simp only [cochainMap, compositeColift, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplex_map_f, Γ.map_comp,
      Category.assoc]
    have n1 := (𝒯.sections g).hom.naturality ((colift F h I).f n)
    simp only [Functor.comp_map] at n1
    rw [← Category.assoc ((𝒯.sections g).hom.app _)]
    erw [← n1]
    dsimp only [Functor.mapHomologicalComplex_obj_X]
    simp only [Category.assoc]
    rw [𝒯.sections_comp]
  exact (Homotopy.ofEq e).trans ((Γ.mapHomotopy H).compRight _)

omit [Abelian D] [Γ.Additive] in
theorem oneColift_comm (F : Coequivariant 𝒯) (I : InjectiveResolution F.obj) :
    I.ι ≫ (colift F 1 I ≫ (NatIso.mapHomologicalComplex 𝒯.one _).hom.app I.cocomplex) =
      (CochainComplex.single₀ C).map (𝟙 F.obj) ≫ I.ι := by
  apply comm_of_comm_zero
  simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f]
  have n1 := 𝒯.one.hom.naturality (I.ι.f 0)
  simp only [Functor.id_map] at n1
  erw [← Category.assoc, colift_comm_zero, Category.assoc, n1, F.coact_one]
  exact (Iso.inv_hom_id_app_assoc 𝒯.one F.obj (I.ι.f 0)).trans (Category.id_comp _).symm

variable (Γ) in
/-- The chain map of `1` is homotopic to the identity. -/
def coOneHomotopy (F : Coequivariant 𝒯) (I : InjectiveResolution F.obj) :
    Homotopy (cochainMap Γ F 1 I) (𝟙 _) := by
  have H : Homotopy (colift F 1 I ≫ (NatIso.mapHomologicalComplex 𝒯.one _).hom.app I.cocomplex)
      (𝟙 I.cocomplex) :=
    InjectiveResolution.descHomotopy (𝟙 F.obj) _ _ (oneColift_comm F I) (by simp)
  have e : cochainMap Γ F 1 I = (Γ.mapHomologicalComplex _).map
      (colift F 1 I ≫ (NatIso.mapHomologicalComplex 𝒯.one _).hom.app I.cocomplex) := by
    ext n
    simp only [cochainMap, HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
      Functor.mapHomologicalComplex_map_f, Γ.map_comp, 𝒯.sections_one]
  exact (Homotopy.ofEq e).trans ((Γ.mapHomotopy H).trans
    (Homotopy.ofEq ((Γ.mapHomologicalComplex _).map_id _)))

variable (Γ) in
/-- The maps induced on degree `n` cohomology form an action of the opposite
monoid. -/
def coHomologyAction (F : Coequivariant 𝒯) (I : InjectiveResolution F.obj) (n : ℕ) :
    Gᵐᵒᵖ →* End (((Γ.mapHomologicalComplex _).obj I.cocomplex).homology n) where
  toFun g := HomologicalComplex.homologyMap (cochainMap Γ F g.unop I) n
  map_one' := by
    rw [MulOpposite.unop_one, (coOneHomotopy Γ F I).homologyMap_eq n,
      HomologicalComplex.homologyMap_id]
    rfl
  map_mul' g h := by
    rw [End.mul_def, MulOpposite.unop_mul, ← HomologicalComplex.homologyMap_comp,
      (comulHomotopy Γ F h.unop g.unop I).homologyMap_eq n]

variable (Γ) in
/-- For a group, inversion turns the maps induced on degree `n` cohomology
into an object with an action of the group. -/
def coCohomologyAction {G : Type w} [Group G] {T : G → C ⥤ C} [∀ g, (T g).Additive]
    [∀ g, (T g).PreservesHomology] [∀ g, (T g).PreservesInjectiveObjects] {𝒯 : Data Γ T}
    (F : Coequivariant 𝒯) (I : InjectiveResolution F.obj) (n : ℕ) : Action D G where
  V := ((Γ.mapHomologicalComplex _).obj I.cocomplex).homology n
  ρ := (coHomologyAction Γ F I n).comp (MulEquiv.inv' G).toMonoidHom

end Langlands.Cohomology.TranslationAction
