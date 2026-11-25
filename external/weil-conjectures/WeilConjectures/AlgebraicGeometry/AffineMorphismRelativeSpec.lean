/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffineStructureAlgebraFullyFaithful
import WeilConjectures.AlgebraicGeometry.RelativeSpectrumAffineRealization
import WeilConjectures.AlgebraicGeometry.RelativeSpecMorphismChart

/-! # Affine morphisms and quasi-coherent algebras (relative spectrum)

Source: Stacks Project, Morphisms, Lemmas 01S8 and 01SA; Constructions, Definition 01LW and
Lemma 01LX (blueprint: lem-weil-pbc-affine-morphism-relative-spec).

A quasi-coherent `𝒪_S`-algebra is a landed `S.CommAlgebraSheaf` (`Under S.sheaf`,
def-weil-pbc-comm-algebra-sheaf) whose `toModule` is quasi-coherent. For `f : X ⟶ S` the algebra
`f_* 𝒪_X` is `Under.mk ⟨f.c⟩` (the local notation `𝒪⁎ f`). Schemes affine over `S` are the full
subcategory of `Over S` on `IsAffineHom`. The restriction `𝒜|_V` to an open `V` is Mathlib's
naive sheaf pullback along the open embedding `V.ι`, whose sections over `W` are `𝒜(V.ι ''ᵁ W)`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

set_option hygiene false in
/-- `f_* 𝒪_X` as a sheaf of commutative `𝒪_S`-algebras, through `f^♯ = f.c`. -/
local notation "𝒪⁎" f:max => Under.mk (⟨(f).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (f).base).obj (Scheme.sheaf _))

private theorem qc {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] :
    (Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f)).IsQuasicoherent := by
  let := IsSeparated.of_isAffineHom f
  have := SheafOfModules.isQuasicoherent_unit.{u, u, u} (R := X.ringCatSheaf)
  exact Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f
    (SheafOfModules.unit X.ringCatSheaf)
private noncomputable def affineStructureAlgebraFunctor (S : Scheme.{u}) :
    (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ⥤
      ObjectProperty.FullSubcategory
        (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) := by
  refine {
    obj := fun Y ↦ ⟨𝒪⁎ Y.unop.obj.hom, @qc _ _ Y.unop.obj.hom Y.unop.property⟩
    map := fun {Y Y'} h ↦ ⟨Under.homMk ⟨{
      app := fun V ↦ h.unop.hom.left.appLE (Y.unop.obj.hom ⁻¹ᵁ V.unop)
        (Y'.unop.obj.hom ⁻¹ᵁ V.unop)
        (by rw [← Over.w h.unop.hom, Scheme.Hom.comp_preimage])
      naturality := ?_ }⟩ ?_⟩
    map_id := ?_
    map_comp := ?_ }
  · intro U V i
    change Y.unop.obj.left.presheaf.map
        ((Opens.map Y.unop.obj.hom.base).map i.unop).op ≫ _ = _ ≫
      Y'.unop.obj.left.presheaf.map ((Opens.map Y'.unop.obj.hom.base).map i.unop).op
    simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change Y.unop.obj.hom.app V.unop ≫ h.unop.hom.left.appLE _ _ _ =
      Y'.unop.obj.hom.app V.unop
    rw [← Scheme.Hom.comp_appLE]
    exact (Scheme.Hom.congr_app (Over.w h.unop.hom).symm V.unop).symm
  · intro Y
    apply InducedCategory.hom_ext
    apply StructuredArrow.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change Scheme.Hom.appLE (𝟙 Y.unop.obj.left) _ _ _ = 𝟙 _
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
      homOfLE_refl, op_id, Category.id_comp]
    exact CategoryTheory.Functor.map_id _ _
  · intro Y Y' Y'' h k
    apply InducedCategory.hom_ext
    apply StructuredArrow.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change (k.unop.hom.left ≫ h.unop.hom.left).appLE _ _ _ =
      h.unop.hom.left.appLE _ _ _ ≫ k.unop.hom.left.appLE _ _ _
    rw [Scheme.Hom.appLE_comp_appLE]

private noncomputable def structureAlgebraRestrictionIso {X S : Scheme.{u}}
    (f : X ⟶ S) (V : S.Opens) :
    ((Under.post (V.ι.isOpenEmbedding.sheafPullback CommRingCat.{u})).obj
      (𝒪⁎ f) : V.toScheme.CommAlgebraSheaf) ≅ 𝒪⁎ (f ∣_ V) := by
  refine Under.isoMk (ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun W ↦ X.presheaf.mapIso (eqToIso
      (image_morphismRestrict_preimage f V W.unop)).op) ?_)) ?_
  · intro W W' i
    change X.presheaf.map _ ≫ X.presheaf.map _ = X.presheaf.map _ ≫ X.presheaf.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    change f.app (V.ι ''ᵁ W.unop) ≫ _ = (f ∣_ V).app W.unop
    exact (morphismRestrict_app f V W.unop).symm

-- The equivalence witnesses and sectionwise naturality require substantial dependent elaboration.
/-- (1) For an affine `f : X ⟶ S`, `f_* 𝒪_X` is a quasi-coherent `𝒪_S`-algebra.
(3) An anti-equivalence `E` from schemes affine over `S` to quasi-coherent `𝒪_S`-algebras whose
functor is `f ↦ f_* 𝒪_X` on objects (`hobj`) and `h ↦ f'_* h^♯` on morphisms (sections:
`h.appLE`), with quasi-inverse `𝒜 ↦ Spec_S 𝒜 = E.inverse.obj 𝒜`; (2) for `π = Spec_S 𝒜 ⟶ S`
and `α : 𝒜 ≅ π_* 𝒪` (the counit of `E`), the morphism `π⁻¹ U ⟶ Spec 𝒜(U)` corresponding to
`α_U` (`toSpecΓ ≫ Spec.map α_U`) is an isomorphism for every affine open `U`; for `φ : 𝒜 ⟶ ℬ`
the restriction over an affine `U` of `Spec_S ℬ ⟶ Spec_S 𝒜` is `Spec φ_U` under these charts.
(4) For an open `V`: `ρ : (f_* 𝒪_X)|_V ≅ (f ∣_ V)_* 𝒪` is the canonical identification (sections:
`(f⁻¹ V).ι.appLE`); `Spec_S 𝒜 ×_S V = π⁻¹ V`, and `π ∣_ V` is affine with isomorphic charts for
`𝒜|_V` and `α|_V ≫ ρ` over every affine open `W` of `V`, i.e. `π⁻¹ V = Spec_V (𝒜|_V)`.
Source: Stacks Project, Morphisms, Lemmas 01S8 and 01SA; Constructions, Definition 01LW and
Lemma 01LX (blueprint: lem-weil-pbc-affine-morphism-relative-spec).

Proof: (1) by Stacks 01LC (pushforward of a quasi-coherent module along a quasi-compact
quasi-separated morphism). For (2), on each affine open `U` take `Spec 𝒜(U)`; these are
compatible over inclusions of affine opens and glue by relative gluing (Stacks 01LH) to
`π : Spec_S 𝒜 ⟶ S`, affine with `π⁻¹ U ≅ Spec 𝒜(U)`; `α` is an isomorphism on the affine basis,
hence an isomorphism. For (3), full faithfulness is checked locally on affine opens using
morphisms into affine schemes and Spec on affine pieces, essential surjectivity is (1) with
Stacks 01S8 (`X ≅ Spec_S f_* 𝒪_X`). (4) follows from `isPullback_morphismRestrict` and the
local nature of the construction. -/
theorem affine_morphism_relative_spec (S : Scheme.{u}) :
    (∀ {X : Scheme.{u}} (f : X ⟶ S), IsAffineHom f →
      (Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f)).IsQuasicoherent) ∧
    ∃ (E : (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ≌
        ObjectProperty.FullSubcategory
          (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent))
      (hobj : ∀ Y, (E.functor.obj (op Y)).obj = 𝒪⁎ Y.obj.hom)
      (ρ : ∀ (Y : ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))
          (V : S.Opens),
        ((Under.post (V.ι.isOpenEmbedding.sheafPullback CommRingCat.{u})).obj
          (𝒪⁎ Y.obj.hom) : V.toScheme.CommAlgebraSheaf) ≅ 𝒪⁎ (Y.obj.hom ∣_ V)),
      (∀ (Y Y') (h : Y ⟶ Y') (V : S.Opens),
        (E.functor.map h.op).hom.right.hom.app (op V) =
          eqToHom (by rw [hobj Y']; rfl) ≫
            h.hom.left.appLE (Y'.obj.hom ⁻¹ᵁ V) (Y.obj.hom ⁻¹ᵁ V)
              (by rw [← Over.w h.hom, Scheme.Hom.comp_preimage]) ≫
            eqToHom (by rw [hobj Y]; rfl)) ∧
      (∀ (A) (U : S.Opens), IsAffineOpen U →
        IsIso (((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ U).toSpecΓ ≫
          Spec.map (((E.counitIso.app A).inv.hom ≫
            eqToHom (hobj (E.inverse.obj A).unop)).right.hom.app (op U)))) ∧
      (∀ (A B) (φ : A ⟶ B) (U : S.Opens), IsAffineOpen U →
        (E.inverse.map φ).unop.hom.left.resLE ((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ U)
            ((E.inverse.obj B).unop.obj.hom ⁻¹ᵁ U)
            (by rw [← Scheme.Hom.comp_preimage, Over.w (E.inverse.map φ).unop.hom]) ≫
          ((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ U).toSpecΓ ≫
            Spec.map (((E.counitIso.app A).inv.hom ≫
              eqToHom (hobj (E.inverse.obj A).unop)).right.hom.app (op U)) =
        ((E.inverse.obj B).unop.obj.hom ⁻¹ᵁ U).toSpecΓ ≫
          Spec.map (((E.counitIso.app B).inv.hom ≫
            eqToHom (hobj (E.inverse.obj B).unop)).right.hom.app (op U)) ≫
          Spec.map (φ.hom.right.hom.app (op U))) ∧
      (∀ (Y : ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))
          (V : S.Opens) (W : V.toScheme.Opens),
        (ρ Y V).hom.right.hom.app (op W) =
          (Y.obj.hom ⁻¹ᵁ V).ι.appLE (Y.obj.hom ⁻¹ᵁ (V.ι ''ᵁ W)) ((Y.obj.hom ∣_ V) ⁻¹ᵁ W)
            (by rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι,
              Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq])) ∧
      (∀ (A) (V : S.Opens),
        IsPullback (((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ V).ι)
          ((E.inverse.obj A).unop.obj.hom ∣_ V) (E.inverse.obj A).unop.obj.hom V.ι ∧
        IsAffineHom ((E.inverse.obj A).unop.obj.hom ∣_ V) ∧
        ∀ W : V.toScheme.Opens, IsAffineOpen W →
          IsIso ((((E.inverse.obj A).unop.obj.hom ∣_ V) ⁻¹ᵁ W).toSpecΓ ≫
            Spec.map (((E.counitIso.app A).inv.hom ≫
              eqToHom (hobj (E.inverse.obj A).unop)).right.hom.app (op (V.ι ''ᵁ W)) ≫
              (ρ (E.inverse.obj A).unop V).hom.right.hom.app (op W)))) := by
  classical
  refine ⟨fun f hf ↦ @qc _ _ f hf, ?_⟩
  let F := affineStructureAlgebraFunctor S
  have hobj : ∀ Y, (F.obj (op Y)).obj = 𝒪⁎ Y.obj.hom := fun _ ↦ rfl
  have hmap : ∀ (Y Y') (h : Y ⟶ Y') (V : S.Opens),
      (F.map h.op).hom.right.hom.app (op V) =
        eqToHom (by rw [hobj Y']; rfl) ≫
          h.hom.left.appLE (Y'.obj.hom ⁻¹ᵁ V) (Y.obj.hom ⁻¹ᵁ V)
            (by rw [← Over.w h.hom, Scheme.Hom.comp_preimage]) ≫
          eqToHom (by rw [hobj Y]; rfl) := by
    intros
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hFF : F.Full ∧ F.Faithful :=
    affine_structure_algebra_full_faithful S F hobj hmap
  have : F.Full := hFF.1
  have : F.Faithful := hFF.2
  have : F.EssSurj := by
    refine ⟨fun A ↦ ?_⟩
    obtain ⟨X, f, hf, ⟨α⟩⟩ := exists_affine_structure_algebra S A.obj A.property
    let Y : ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom) :=
      ⟨Over.mk f, hf⟩
    refine ⟨op Y, ⟨ObjectProperty.isoMk _ ?_⟩⟩
    exact (eqToIso (hobj Y)) ≪≫ α.symm
  let : F.IsEquivalence := {}
  let E := F.asEquivalence
  refine ⟨E, hobj, fun Y V ↦ structureAlgebraRestrictionIso Y.obj.hom V,
    hmap, ?_, ?_, ?_, ?_⟩
  · intro A U hU
    have : IsAffineHom (E.inverse.obj A).unop.obj.hom := (E.inverse.obj A).unop.property
    have : IsIso ((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ U).toSpecΓ :=
      (hU.preimage _).isoSpec.isIso_hom
    infer_instance
  · exact relative_spec_morphism_chart S E hobj hmap
  · intro Y V W
    simp only [structureAlgebraRestrictionIso, Scheme.Opens.ι_appLE]
    rfl
  · intro A V
    have : IsAffineHom (E.inverse.obj A).unop.obj.hom := (E.inverse.obj A).unop.property
    have : IsAffineHom ((E.inverse.obj A).unop.obj.hom ∣_ V) :=
      IsZariskiLocalAtTarget.restrict ‹IsAffineHom _› V
    refine ⟨(isPullback_morphismRestrict _ V).flip, inferInstance, ?_⟩
    intro W hW
    have : IsIso (((E.inverse.obj A).unop.obj.hom ∣_ V) ⁻¹ᵁ W).toSpecΓ :=
      (hW.preimage _).isoSpec.isIso_hom
    infer_instance

end AlgebraicGeometry
