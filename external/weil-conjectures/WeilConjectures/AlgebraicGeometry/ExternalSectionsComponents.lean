/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison

/-! # Components of the external section morphism

Source: Stacks Project, Tag 0BED, degree-zero cup product.
(blueprint: lem-sc-external-sections-components).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Structure maps on sections commute with pullback.
Source: Stacks Project, Tags 0096 and 0BED. -/
theorem scalarMap_pullback
    (f : X ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (U : X.Opens) (r : k) :
    (a.app U).hom (scalarMap f U r) = scalarMap (a ≫ f) (a ⁻¹ᵁ U) r := by
  have hn := congrArg (fun q : Γ(X, ⊤) ⟶ Γ(Y, a ⁻¹ᵁ U) ↦
    q.hom (((ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom r))
    (a.naturality (homOfLE (le_top (a := U))).op)
  simp only [scalarMap, RingHom.comp_apply, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  convert hn using 1; rfl

/-- The pullback adjunction unit on sections, with the scalar actions restricted to k.
Source: Stacks Project, Tags 0096 and 0BED. -/
def scalarUnitSection
    (f : X ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (F : X.Modules) (U : X.Opens) :
    scalarObj f F (op U) →ₗ[k]
      scalarObj (a ≫ f) ((tensorPullback a).obj F) (op (a ⁻¹ᵁ U)) where
  toFun s := ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F).app U s
  map_add' s t := map_add _ s t
  map_smul' r s := by
    let η := ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F).val.app (op U)
    change η.hom ((scalarMap f U r) • (show F.val.obj (op U) from s)) = _
    have h := η.hom.map_smul (scalarMap f U r) s
    refine h.trans ?_
    change (a.app U).hom (scalarMap f U r) •
        (show Γ((tensorPullback a).obj F, a ⁻¹ᵁ U) from η.hom s) =
      (scalarMap (a ≫ f) (a ⁻¹ᵁ U) r) • (show Γ((tensorPullback a).obj F, a ⁻¹ᵁ U) from η.hom s)
    exact congrArg (fun q : Γ(Y, a ⁻¹ᵁ U) ↦
      q • (show Γ((tensorPullback a).obj F, a ⁻¹ᵁ U) from η.hom s))
      (scalarMap_pullback f a U r)

/-- Pull a global section back and restrict it to an arbitrary open in the source.
Source: Stacks Project, Tags 0096 and 0BED. -/
def scalarPullbackGlobalSection
    (f : X ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (F : X.Modules) (W : Y.Opens) :
    scalarObj f F (op ⊤) →ₗ[k] scalarObj (a ≫ f) ((tensorPullback a).obj F) (op W) :=
  (scalarRestriction (a ≫ f) ((tensorPullback a).obj F)
    (homOfLE (by simp : W ≤ a ⁻¹ᵁ ⊤)).op).hom.comp (scalarUnitSection f a F ⊤)

/-- The bilinear external section map over an open of the second factor.
Source: Stacks Project, Tag 0BED. -/
def externalSectionsBilinear
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : Y.Opens) :
    scalarObj f F (op ⊤) →ₗ[k] scalarObj g G (op V) →ₗ[k]
      scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
        (op (pullback.snd f g ⁻¹ᵁ V)) := by
  let L := scalarPullbackGlobalSection f (pullback.fst f g) F (pullback.snd f g ⁻¹ᵁ V)
  let R := scalarUnitSection g (pullback.snd f g) G V
  exact LinearMap.mk₂ k (fun s t ↦ tmulSection (L s) (R t))
    (by intros; rw [map_add, add_tmulSection])
    (by
      intro r s t
      rw [LinearMap.map_smul]
      exact smul_tmulSection _ _ _)
    (by intros; rw [map_add, tmulSection_add])
    (by
      intro r s t
      rw [LinearMap.map_smul]
      change tmulSection (L s)
        ((scalarMap (pullback.snd f g ≫ g) (pullback.snd f g ⁻¹ᵁ V) r) • _) = _
      rw [show scalarMap (pullback.snd f g ≫ g) (pullback.snd f g ⁻¹ᵁ V) r =
        scalarMap (pullback.fst f g ≫ f) (pullback.snd f g ⁻¹ᵁ V) r from
        congrArg (fun a ↦ scalarMap a (pullback.snd f g ⁻¹ᵁ V) r)
          pullback.condition.symm]
      exact tmulSection_smul _ _ _)

/-- The induced k-linear map on tensor products of sections.
Source: Stacks Project, Tag 0BED. -/
def externalSectionsComponent
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : Y.Opens) :
    ModuleCat.of k (scalarObj f F (op ⊤) ⊗[k] scalarObj g G (op V)) ⟶
      scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
        (op (pullback.snd f g ⁻¹ᵁ V)) :=
  ModuleCat.ofHom (X := scalarObj f F (op ⊤) ⊗[k] scalarObj g G (op V))
    (Y := scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
      (op (pullback.snd f g ⁻¹ᵁ V))) (show
    (scalarObj f F (op ⊤) ⊗[k] scalarObj g G (op V)) →ₗ[k]
      scalarObj (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
        (op (pullback.snd f g ⁻¹ᵁ V)) from
    TensorProduct.lift (externalSectionsBilinear f g F G V))

/-- External section components commute with restriction in the second factor.
Source: Stacks Project, Tag 0BED, degree-zero cup product.
(blueprint: lem-sc-external-sections-components).
Proof: On a pure tensor the left factor is the restriction of one fixed pulled-back
section, so functoriality of restriction gives its compatibility. The right factor
is the pullback adjunction unit, whose naturality gives compatibility with restriction.
The restriction formula for tensor sections then identifies the two products.
Tensor induction extends this equality to all tensors.
-/
theorem externalSectionsComponent_naturality
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) {U V : Y.Opensᵒᵖ} (i : U ⟶ V) :
    (scalarPresheaf g G ⋙ MonoidalCategory.tensorLeft (scalarObj f F (op ⊤))).map i ≫
        externalSectionsComponent f g F G V.unop =
      externalSectionsComponent f g F G U.unop ≫
        scalarRestriction (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
          ((Opens.map (pullback.snd f g).base).map i.unop).op := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s t
  change (TensorProduct.lift (externalSectionsBilinear f g F G V.unop))
      (s ⊗ₜ[k] ((scalarRestriction g G i).hom t)) =
    (scalarRestriction (pullback.fst f g ≫ f) (externalCupCoefficients f g F G)
      ((Opens.map (pullback.snd f g).base).map i.unop).op).hom
      ((TensorProduct.lift (externalSectionsBilinear f g F G U.unop)) (s ⊗ₜ[k] t))
  simp only [TensorProduct.lift.tmul]
  dsimp only [externalSectionsBilinear, LinearMap.mk₂_apply,
    scalarPullbackGlobalSection, scalarUnitSection, LinearMap.comp_apply]
  change tmulSection
      (((tensorPullback (pullback.fst f g)).obj F).presheaf.map
        (homOfLE (by simp : pullback.snd f g ⁻¹ᵁ V.unop ≤ pullback.fst f g ⁻¹ᵁ ⊤)).op
        (((Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).unit.app F).app
          ⊤ s))
      (((Classical.choose (exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app G).app
        V.unop (G.presheaf.map i t)) =
    (externalCupCoefficients f g F G).presheaf.map
      ((Opens.map (pullback.snd f g).base).map i.unop).op
      (tmulSection _ _)
  refine Eq.trans ?_ (tmulSection_map
    (M := (tensorPullback (pullback.fst f g)).obj F)
    (N := (tensorPullback (pullback.snd f g)).obj G)
    (leOfHom ((Opens.map (pullback.snd f g).base).map i.unop)) _ _).symm
  congr 1
  · exact (presheaf_map_map_apply (M := (tensorPullback (pullback.fst f g)).obj F)
      (homOfLE (by simp : pullback.snd f g ⁻¹ᵁ U.unop ≤ pullback.fst f g ⁻¹ᵁ ⊤))
      (homOfLE (leOfHom ((Opens.map (pullback.snd f g).base).map i.unop))) _).symm
  · exact Hom.app_presheaf_map
      ((Classical.choose (exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app G)
      i.unop t

end
end AlgebraicGeometry.Scheme.Modules
