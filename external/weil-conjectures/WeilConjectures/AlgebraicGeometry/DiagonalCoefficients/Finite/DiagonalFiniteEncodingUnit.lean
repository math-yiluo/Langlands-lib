/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement

/-! # The regular-module normalization of the sectionwise encoding

Source: finite coefficient reductions in diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-finite-encoding-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- The inverse of the common encoding, with no choice of an equivalence. -/
abbrev finiteEncoding (X : Scheme.{u}) :=
  (CondensedRing.finiteDiscreteCoefficientEquivalence B eR G hG X).inverse

/-- The sectionwise comparison of the inverse encoding's underlying sheaves. -/
def finiteEncodingUnderlying (X : Scheme.{u}) :
    finiteEncoding B eR G hG X ⋙ sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) ≅ Mod.forget _ :=
  by
    let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
      ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
    unfold finiteEncoding CondensedRing.finiteDiscreteCoefficientEquivalence
    exact Functor.isoWhiskerLeft
      (Mod.comap (finiteDiscreteSchemeRingIso B X eR).hom)
      (CategoryTheory.ConstantInternalModuleSheafEncoding.sheafEncodingForgetIso
        (Scheme.ProEt.topology X) (ULift.{u + 1} B) G hG)

/-- Encoding the regular internal module gives the constant coefficient unit,
with its actual unital coefficient comparison.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), finite reductions.
(blueprint: lem-diagonal-finite-encoding-unit).

Proof in words. Restrict the regular module along the pulled-back ring isomorphism;
its inverse identifies this with the regular module of the sheafified constant ring.
At the terminal pro-etale object the module-sheafification unit gives a map from
the regular internal A-module to the sections of this regular sheaf module. Apply
G and precompose the given regular-module comparison. The constant-sheaf adjunction
extends this section map to q from the constant A-module to the encoded regular
module. Naturality of the forgetful comparison and the hypothesis on G identify
its underlying section with the constant-section unit. The forgetful counit
formula and the adjunction triangle therefore give U(q) followed by the underlying
comparison equal to constantCommuteCompose. Thus U(q), and hence q, is invertible.
Compose the inverse of q with the image of the regular-module ring comparison.
Naturality and cancellation give exactly the displayed inverse coefficient map.
This argument includes the zero ring and the empty scheme. -/
theorem finiteEncoding_unitComparison
    (hregular : ∃ j : G.obj (Mod.regular (AddCommGrpCat.of (ULift.{u + 1} B))) ≅
        ModuleCat.of (ULift.{u + 1} B) (ULift.{u + 1} B),
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}).map j.hom =
        (eqToIso hG).hom.app (Mod.regular (AddCommGrpCat.of (ULift.{u + 1} B))))
    (X : Scheme.{u})
    [(Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})] :
    ∃ i : (finiteEncoding B eR G hG X).obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)) ≅
        (constantSheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj
            (ModuleCat.of (ULift.{u + 1} B) (ULift.{u + 1} B)),
      (finiteEncodingUnderlying B eR G hG X).inv.app
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)) ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).map i.hom ≫
        ((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).app
            (ModuleCat.of (ULift.{u + 1} B) (ULift.{u + 1} B))).hom =
      (finiteDiscreteSchemeRingIso B X eR).inv := by
  let J := Scheme.ProEt.topology X
  let A := ULift.{u + 1} B
  let A₀ := CategoryTheory.ConstantInternalModuleSheafEncoding.A (C := X.ProEtᵒᵖ) A
  let : (J.W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal (J := J) (A := Ab.{u + 1})
  let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} A) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  let H := CategoryTheory.ConstantInternalModuleSheafEncoding.sheafEncoding J A G hG
  let Q := CategoryTheory.ConstantInternalModuleSheafEncoding.moduleLocalizationRight J A₀
  let P := CategoryTheory.ConstantInternalModuleSheafEncoding.presheafToFunctor
    (C := X.ProEtᵒᵖ) A
  let S := Mod.regular ((presheafToSheaf J Ab.{u + 1}).obj A₀)
  let M := H.obj S
  let U := sheafCompose J (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})
  let C₀ := constantSheaf J (ModuleCat.{u + 1} A)
  let C₁ := constantSheaf J Ab.{u + 1}
  let T := Scheme.ProEt.mk (𝟙 X)
  let V := Opposite.op T
  let hT : IsTerminal T := IsTerminal.ofUniqueHom
    (fun V ↦ MorphismProperty.Over.homMk V.hom) fun V f ↦
      MorphismProperty.Over.Hom.ext <| by
        change f.left = V.hom
        rw [← MorphismProperty.Over.w f]
        exact (Category.comp_id _).symm
  let u₀ : U.obj M ≅ C₁.obj (AddCommGrpCat.of A) :=
    (CategoryTheory.ConstantInternalModuleSheafEncoding.sheafEncodingForgetIso J A G hG).app S
  let g₀ : (P.obj (Mod.regular A₀)).obj V ≅ Mod.regular (AddCommGrpCat.of A) :=
    Mod.isoMk (Iso.refl _) (by simp)
  let e₀ : ((presheafToSheaf J Ab.{u + 1}).mapMod A₀).obj (Mod.regular A₀) ≅ S :=
    Mod.isoMk (Iso.refl _) (by simp)
  let f : Mod.regular (AddCommGrpCat.of A) ⟶ (P.obj (Q.obj S)).obj V :=
    g₀.inv ≫ (P.map
      ((CategoryTheory.ConstantInternalModuleSheafEncoding.moduleLocalizationAdjunction
        J A₀).unit.app (Mod.regular A₀) ≫ Q.map e₀.hom)).app V
  obtain ⟨j, hj⟩ := hregular
  let t : ModuleCat.of A A ⟶ M.obj.obj V := j.inv ≫ G.map f
  let q : C₀.obj (ModuleCat.of A A) ⟶ M :=
    C₀.map t ≫ (constantSheafAdj J (ModuleCat.{u + 1} A) hT).counit.app M
  let c := (constantCommuteCompose J
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).app (ModuleCat.of A A)
  have ht : (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map t ≫ u₀.hom.hom.app V =
      (constantSheafAdj J Ab.{u + 1} hT).unit.app (AddCommGrpCat.of A) := by
    let N := (P.obj (Q.obj S)).obj V
    let ε := eqToIso hG
    have hn : (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map (G.map f) ≫
        ε.hom.app N = ε.hom.app (Mod.regular (AddCommGrpCat.of A)) ≫ f.hom :=
      ε.hom.naturality f
    have hj' : (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map j.inv ≫
        ε.hom.app (Mod.regular (AddCommGrpCat.of A)) = 𝟙 _ := by
      rw [← hj, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    have huV : u₀.hom.hom.app V = ε.hom.app N := by
      dsimp only [u₀,
        CategoryTheory.ConstantInternalModuleSheafEncoding.sheafEncodingForgetIso]
      let E₀ := eqToIso (congrArg (fun P₀ ↦ Q ⋙ P₀)
        (CategoryTheory.ConstantInternalModuleSheafEncoding.modulePresheafEncoding_forget
          (C := X.ProEt) A G hG))
      change ((sheafToPresheaf J Ab.{u + 1}).map
        ((Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf J Ab.{u + 1})).preimage
          (X := U.obj M) (Y := C₁.obj (AddCommGrpCat.of A)) (E₀.hom.app S))).app V = _
      rw [Functor.FullyFaithful.map_preimage]
      dsimp only [E₀, ε, eqToIso]
      simp only [eqToHom_app]
    have hf : f.hom = (constantSheafAdj J Ab.{u + 1} hT).unit.app
        (AddCommGrpCat.of A) := by
      change (𝟙 _ ≫
        (((CategoryTheory.ConstantInternalModuleSheafEncoding.moduleLocalizationAdjunction
          J A₀).unit.app (Mod.regular A₀)).hom.app V ≫ 𝟙 _)) = _
      rw [Category.id_comp, Category.comp_id]
      rw [CategoryTheory.Adjunction.mapModAdjunction_unit_app_hom]
      simp only [constantSheafAdj, Adjunction.comp_unit_app,
        constantPresheafAdj_unit_app, Functor.comp_obj]
      simp only [Category.id_comp]
      rfl
    calc
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map t ≫ u₀.hom.hom.app V =
          (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map j.inv ≫
            ((forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map (G.map f) ≫
              ε.hom.app N) := by rw [huV]; simp only [t, Functor.map_comp, Category.assoc]
      _ = (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map j.inv ≫
          (ε.hom.app (Mod.regular (AddCommGrpCat.of A)) ≫ f.hom) := by rw [hn]
      _ = f.hom := by rw [← Category.assoc, hj', Category.id_comp]
      _ = _ := hf
  have hq : U.map q ≫ u₀.hom = c.hom := by
    dsimp only [q]
    erw [U.map_comp]
    erw [← constantSheafAdj_counit_w J (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) M hT]
    simp only [Category.assoc]
    erw [← Category.assoc, (constantCommuteCompose J
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).hom.naturality t]
    simp only [Functor.comp_map, Category.assoc]
    erw [← (constantSheafAdj J Ab.{u + 1} hT).counit.naturality u₀.hom]
    erw [← C₁.map_comp_assoc, ht]
    erw [(constantSheafAdj J Ab.{u + 1} hT).left_triangle_components
      (AddCommGrpCat.of A)]
    exact Category.comp_id _
  have hq' : c.hom ≫ u₀.inv = U.map q := (u₀.comp_inv_eq).mpr hq.symm
  have : IsIso (U.map q) := by
    rw [← hq']
    infer_instance
  have : IsIso q := isIso_of_reflects_iso q U
  have hqinv : U.map (asIso q).inv ≫ c.hom = u₀.hom := by
    exact ((U.mapIso (asIso q)).inv_comp_eq).mpr hq.symm
  let d := finiteDiscreteSchemeRingIso B X eR
  have : IsMonHom d.inv :=
    inferInstanceAs (IsMonHom (finiteDiscreteSchemeRingIso B X eR).inv)
  let a : (Mod.comap d.hom).obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)) ≅ S := by
    refine Mod.isoMk d.symm ?_
    change (d.hom ▷ _ ≫ μ[_]) ≫ d.inv = _ ◁ d.inv ≫ μ[_]
    rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, Category.assoc,
      ← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp]
  let k := H.mapIso a ≪≫ (asIso q).symm
  unfold finiteEncoding CondensedRing.finiteDiscreteCoefficientEquivalence
  refine ⟨k, ?_⟩
  change (CategoryTheory.ConstantInternalModuleSheafEncoding.sheafEncodingForgetIso
    J A G hG).inv.app _ ≫ U.map k.hom ≫ c.hom = d.inv
  dsimp only [k, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [U.map_comp, Category.assoc, hqinv]
  erw [(CategoryTheory.ConstantInternalModuleSheafEncoding.sheafEncodingForgetIso
    J A G hG).hom.naturality a.hom]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
