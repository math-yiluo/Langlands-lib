import Langlands.Geometry.Analytic.GroundFieldChangingSpaceFunctor

/-! # Normalizing an analytic arrow over an isomorphic ground field -/

noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite
open Langlands.Analytic.CompleteUltrametricField

universe u v

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analytic.SpaceOverField

variable {K L : CompleteUltrametricField.{u}}
variable {X Y Z : SpaceOverField.{u, v}}

theorem fieldMap_comp (f : Z ⟶ Y) (g : Y ⟶ X) :
    fieldMap (f ≫ g) = fieldMap g ≫ fieldMap f :=
  rfl

theorem fieldMap_inv (f : Y ⟶ X) [IsIso f] :
    fieldMap (CategoryTheory.inv f) =
      @CategoryTheory.inv _ _ _ _ (fieldMap f)
        (inferInstanceAs (IsIso (fieldProjection.map f).unop)) := by
  let : IsIso (fieldMap f) := inferInstanceAs (IsIso (fieldProjection.map f).unop)
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← fieldMap_comp, IsIso.inv_hom_id]
  rfl

/-- The inclusion of the analytic fibre, by the identity coefficient map and
the scalar-extension unit. -/
abbrev fixedFieldAnalyticInclusion (K : CompleteUltrametricField.{u}) :
    K.CompatibleAnalyticCategory.{u, v} ⥤ SpaceOverField.{u, v} :=
  Pseudofunctor.CoGrothendieck.ι scalarExtensionPseudofunctor (op K)

instance (K : CompleteUltrametricField.{u}) : (fixedFieldAnalyticInclusion.{u, v} K).Faithful where
  map_injective h := by
    have h' := ((Pseudofunctor.CoGrothendieck.Hom.ext_iff _ _).mp h).2
    change _ ≫ (localizedExtendId K).inv.app _ =
      (_ ≫ (localizedExtendId K).inv.app _) ≫ eqToHom _ at h'
    simpa only [eqToHom_refl, Category.comp_id, cancel_mono] using h'

variable {A B : K.CompatibleAnalyticCategory.{u, v}}

/-- Read an identity-field arrow as a map in the analytic fibre. -/
def toFixedFieldMap (f : withField K A ⟶ withField K B) (hf : fieldMap f = 𝟙 K) :
    A ⟶ B :=
  f.fiber ≫ eqToHom (congrArg (fun e => (localizedExtend.{u, v} e).obj B) hf) ≫
    (localizedExtendId K).hom.app B

@[simp]
theorem fixedFieldAnalyticInclusion_map_toFixedFieldMap
    (f : withField K A ⟶ withField K B) (hf : fieldMap f = 𝟙 K) :
    (fixedFieldAnalyticInclusion K).map (toFixedFieldMap f hf) = f := by
  obtain ⟨base, a⟩ := f
  change base.unop = 𝟙 K at hf
  have hb : base = 𝟙 (op K) := congrArg Quiver.Hom.op hf
  subst base
  change A ⟶ (localizedExtend (𝟙 K)).obj B at a
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  change (a ≫ eqToHom rfl ≫ (localizedExtendId K).hom.app B) ≫
    (localizedExtendId K).inv.app B = a ≫ eqToHom rfl
  simp only [Category.assoc, Iso.hom_inv_id_app, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- An isomorphism with identity coefficient map lifts to an isomorphism in
the analytic fibre. -/
def toFixedFieldIso (e : withField K A ≅ withField K B) (he : fieldMap e.hom = 𝟙 K) :
    A ≅ B where
  hom := toFixedFieldMap e.hom he
  inv := toFixedFieldMap e.inv (by
    have h := congrArg fieldMap e.hom_inv_id
    rw [fieldMap_comp, he, Category.comp_id] at h
    exact h)
  hom_inv_id := by
    apply (fixedFieldAnalyticInclusion K).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      fixedFieldAnalyticInclusion_map_toFixedFieldMap,
      fixedFieldAnalyticInclusion_map_toFixedFieldMap]
    exact e.hom_inv_id
  inv_hom_id := by
    apply (fixedFieldAnalyticInclusion K).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      fixedFieldAnalyticInclusion_map_toFixedFieldMap,
      fixedFieldAnalyticInclusion_map_toFixedFieldMap]
    exact e.inv_hom_id

@[simp]
theorem fixedFieldAnalyticInclusion_map_toFixedFieldIso_hom (e : withField K A ≅ withField K B)
    (he : fieldMap e.hom = 𝟙 K) :
    (fixedFieldAnalyticInclusion K).map (toFixedFieldIso e he).hom = e.hom :=
  fixedFieldAnalyticInclusion_map_toFixedFieldMap e.hom he

theorem underlyingSpaceFunctor_map_fixedFieldAnalyticInclusion (f : A ⟶ B) :
    underlyingSpaceFunctor.map ((fixedFieldAnalyticInclusion K).map f) = K.underlyingSpace.map f := by
  change underlyingAnalyticMap (𝟙 K) (f ≫ (localizedExtendId K).inv.app B) = _
  rw [underlyingAnalyticMap, localizedExtendProjection_id, ← K.underlyingSpace.map_comp,
    Category.assoc, Iso.inv_hom_id_app]
  change K.underlyingSpace.map (f ≫ 𝟙 B) = K.underlyingSpace.map f
  rw [Category.comp_id]

/-- Scalar extension along an isometric field isomorphism gives an isomorphism
in the varying-field analytic category. -/
def scalarExtensionIso (X : SpaceOverField.{u, v}) (e : X.field ⟶ L) [IsIso e] :
    withField L ((localizedExtend e).obj X.space) ≅ X :=
  letI := scalarExtensionArrow_isStronglyCartesian X e
  letI := IsStronglyCartesian.isIso_of_base_isIso fieldProjection e.op (scalarExtensionArrow X e)
  asIso (scalarExtensionArrow X e)

@[simp]
theorem fieldMap_scalarExtensionIso_hom (X : SpaceOverField.{u, v}) (e : X.field ⟶ L) [IsIso e] :
    fieldMap (scalarExtensionIso X e).hom = e :=
  rfl

/-- To normalize an arrow over an isomorphic ground field, extend its source
by the inverse field embedding. The new structural arrow has identity
coefficient map and hence lies in the target analytic fibre. -/
theorem fieldMap_normalized (f : Y ⟶ X) [IsIso (fieldMap f)] :
    fieldMap ((scalarExtensionIso Y (CategoryTheory.inv (fieldMap f))).hom ≫ f) = 𝟙 X.field := by
  rw [fieldMap_comp, fieldMap_scalarExtensionIso_hom, IsIso.hom_inv_id]

end Langlands.Analytic.SpaceOverField
