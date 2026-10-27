import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenStatement
import Langlands.AlgebraicGeometry.Modules.UnitEndResidueStalkProof
import Langlands.AlgebraicGeometry.Modules.StructureUnitScalars
import Langlands.AlgebraicGeometry.Modules.TensorSections
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.ModuleLocalHomPullback

/-! # Whole generation opens of actually pulled-back line-bundle sections -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

open Langlands.AlgebraicGeometry.Picard

variable {X Y : Scheme.{u}}

/-- The section morphism of the actual pulled-back section is `pullbackSectionHom`. -/
lemma sectionHom_pullbackSection (f : Y ⟶ X) (M : X.Modules) (s : GlobalSections M) :
    sectionHom ((Scheme.Modules.pullback f).obj M) (pullbackSection f M s) =
      pullbackSectionHom f M s := by
  apply (sectionHomEquiv _).symm.injective
  change (sectionHomEquiv _).symm ((sectionHomEquiv _) (pullbackSection f M s)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Conjugating the pullback of an endomorphism of the structure module by the canonical
comparison `pullbackUnitIso` gives multiplication by the image of its global value at one. -/
lemma pullback_structureEnd_eq_mulHom (f : Y ⟶ X)
    (ψ : structureModule X ⟶ structureModule X) :
    (Langlands.Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map ψ ≫
        (Langlands.Scheme.Modules.pullbackUnitIso f).hom =
      structureMulHom (f.appTop (structureEndValue ψ ⊤)) := by
  rw [Iso.inv_comp_eq]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  erw [Langlands.Scheme.Modules.pullbackUnitAdjunction Y X f]
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  change f.app U (ψ.app U a) = (structureMulHom _).app (f ⁻¹ᵁ U) (f.app U a)
  rw [structureEnd_app_eq_mul_res, structureMulHom_app, map_mul]
  congr 1
  exact ConcreteCategory.congr_hom
    (f.naturality (homOfLE (le_top : U ≤ ⊤)).op) (structureEndValue ψ ⊤)

/-- Pulling back an endomorphism of the structure module preserves and reflects
isomorphisms on abelian-group stalks. -/
lemma pullback_structureEnd_stalk_isIso_iff (f : Y ⟶ X)
    (ψ : structureModule X ⟶ structureModule X) (y : Y) :
    IsIso ((Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y).map
        ((Scheme.Modules.pullback f).map ψ)) ↔
      IsIso ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} (f y)).map ψ) := by
  let e := Langlands.Scheme.Modules.pullbackUnitIso f
  let ψ' : structureModule Y ⟶ structureModule Y :=
    e.inv ≫ (Scheme.Modules.pullback f).map ψ ≫ e.hom
  have hψ : (Scheme.Modules.pullback f).map ψ = e.hom ≫ ψ' ≫ e.inv := by
    simp only [ψ', Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [hψ, Functor.map_comp, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]
  have h1 := unitEnd_stalkIso_iff_residue_ne_zero ψ' y
  have h2 := unitEnd_stalkIso_iff_residue_ne_zero ψ (f y)
  have hv : ψ'.app ⊤ (1 : Γ(Y, ⊤)) = f.appTop (ψ.app ⊤ (1 : Γ(X, ⊤))) := by
    have h : ψ' = structureMulHom (f.appTop (structureEndValue ψ ⊤)) :=
      pullback_structureEnd_eq_mulHom f ψ
    change structureEndValue ψ' ⊤ = f.appTop (structureEndValue ψ ⊤)
    rw [h, structureEndValue_mulHom]
  rw [hv, ← Scheme.Γevaluation_naturality_apply, map_ne_zero] at h1
  exact h1.trans h2.symm

/-- Composing with isomorphisms on both sides does not change invertibility of an image. -/
private lemma isIso_map_iso_comp_iff {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {a b c d : C} (α : a ≅ b) (g : b ⟶ c) (β : d ≅ c) :
    IsIso (F.map (α.hom ≫ g ≫ β.inv)) ↔ IsIso (F.map g) := by
  rw [F.map_comp, F.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]

/-- For a locally free rank-one module, pulling back a morphism out of the structure
module preserves and reflects stalk isomorphisms. -/
lemma pullback_stalk_isIso_iff (f : Y ⟶ X) {M : X.Modules} (hM : IsLocallyFreeRankOne M)
    (φ : structureModule X ⟶ M) (y : Y) :
    IsIso ((Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y).map
        ((Scheme.Modules.pullback f).map φ)) ↔
      IsIso ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} (f y)).map φ) := by
  obtain ⟨U, hU, ⟨e⟩⟩ := hM (f y)
  let V : Y.Opens := f ⁻¹ᵁ U
  let g : V.toScheme ⟶ U.toScheme := f ∣_ U
  let y' : V.toScheme := ⟨y, hU⟩
  let ψ : structureModule U.toScheme ⟶ structureModule U.toScheme :=
    (Scheme.Modules.restrictUnitIso U.ι).inv ≫ (Scheme.Modules.restrictFunctor U.ι).map φ ≫
      e.hom
  have hφ : (Scheme.Modules.restrictFunctor U.ι).map φ =
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫ ψ ≫ e.inv := by
    simp only [ψ, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have h1 := isIso_stalk_restrict_iff ((Scheme.Modules.pullback f).map φ) V y'
  have h2 := NatIso.isIso_map_iff
    (Functor.isoWhiskerRight (Langlands.Scheme.Modules.restrictPullbackNatIso f U)
      (Scheme.Modules.toPresheaf V ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y')) φ
  have h3 := isIso_stalk_restrict_iff φ U (g y')
  have h4 := pullback_structureEnd_stalk_isIso_iff g ψ y'
  have hpt : U.ι (g y') = f y := morphismRestrict_base_coe f U y'
  calc IsIso ((Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y).map
        ((Scheme.Modules.pullback f).map φ))
      ↔ IsIso (((Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor V.ι) ⋙
          (Scheme.Modules.toPresheaf V ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y')).map φ) :=
        h1.symm
    _ ↔ IsIso (((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback g) ⋙
          (Scheme.Modules.toPresheaf V ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y')).map φ) := h2
    _ ↔ IsIso ((Scheme.Modules.pullback g ⋙ Scheme.Modules.toPresheaf V ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} y').map ψ) := by
        change IsIso ((Scheme.Modules.pullback g ⋙ Scheme.Modules.toPresheaf V ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} y').map
            ((Scheme.Modules.restrictFunctor U.ι).map φ)) ↔ _
        rw [hφ]
        exact isIso_map_iso_comp_iff _ _ _ _
    _ ↔ IsIso ((Scheme.Modules.toPresheaf U.toScheme ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} (g y')).map ψ) := h4
    _ ↔ IsIso ((Scheme.Modules.toPresheaf U.toScheme ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} (g y')).map
            ((Scheme.Modules.restrictFunctor U.ι).map φ)) := by
        rw [hφ]
        exact (isIso_map_iso_comp_iff _ _ _ _).symm
    _ ↔ IsIso ((Scheme.Modules.toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} (U.ι (g y'))).map φ) := h3
    _ ↔ _ := by rw [hpt]

/-- The whole generation open of an actually pulled-back line-bundle section is the
inverse image of the whole original generation open. -/
theorem lineBundlePullbackSectionOpen : LineBundlePullbackSectionOpenStatement.{u} := by
  intro X Y f L s
  let L' : LineBundle Y := ⟨(Scheme.Modules.pullback f).obj L.obj, L.property.pullback f⟩
  have hL' := lineBundle_stalkFrame_set_eq L' (pullbackSection f L.obj s)
  have hL := lineBundle_stalkFrame_set_eq L s
  apply Opens.ext
  change (trivializationOpen L'.obj (pullbackSection f L.obj s) : Set Y) =
    f ⁻¹' (trivializationOpen L.obj s : Set X)
  rw [← hL', ← hL]
  ext y
  change IsStalkFrame ((Scheme.Modules.pullback f).obj L.obj) (pullbackSection f L.obj s) y ↔
    IsStalkFrame L.obj s (f y)
  unfold IsStalkFrame
  rw [sectionHom_pullbackSection, pullbackSectionHom, Functor.map_comp, Functor.map_comp,
    isIso_comp_left_iff]
  exact pullback_stalk_isIso_iff f L.property (sectionHom L.obj s) y

end Langlands.SchemeModule
