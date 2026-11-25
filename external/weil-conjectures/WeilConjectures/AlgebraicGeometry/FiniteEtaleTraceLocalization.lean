/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceLocalSums
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSectionDescent
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceLocalizationSectionFormula

/-!
# Local sum characterization of finite étale traces

Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-localization)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem localSum_section_formula {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Etale f) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (τ : (lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj F) ⟶ F)
    (hτ : FiniteEtaleTraceLocalSums f hf F τ) :
    let B := MorphismProperty.Over.pullback @Etale ⊤ f ⋙ MorphismProperty.Over.map ⊤ hf
    ∀ (W : X.Etale) (s : F.obj.obj (op (B.obj W)))
      (T : X.Etale) (h : T ⟶ W) (J : Type u) [Fintype J]
      (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ pullback T.hom f)
      (t : ∀ j, T.left ⟶ V j) (_ : IsColimit (Cofan.mk (pullback T.hom f) i))
      (hinv₁ : ∀ j, t j ≫ i j ≫ pullback.fst T.hom f = 𝟙 T.left)
      (_ : ∀ j, i j ≫ pullback.fst T.hom f ≫ t j = 𝟙 (V j))
      (_ : ∀ j, IsOpenImmersion (i j)) (_ : ∀ j, IsClosedImmersion (i j)),
      F.obj.map h.op
        ((((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f hf).app F).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) ≫
            τ.hom.app (op W)) s) =
        ∑ j, F.obj.map (MorphismProperty.Over.homMk
          (A := T) (B := B.obj T) (t j ≫ i j)
          (by
            change (t j ≫ i j) ≫ pullback.snd T.hom f ≫ f = T.hom
            rw [← pullback.condition]
            simpa [← Category.assoc] using
              congrArg (fun k ↦ k ≫ T.hom) (hinv₁ j))).op
                (F.obj.map (B.map h).op s) := by
  classical
  dsimp only
  intro W s T h J hJ V i t hc hinv₁ hinv₂ hopen hclosed
  let β := (lowerStar AddCommGrpCat.{u + 1} f).map
    ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f hf).app F).inv ≫ τ
  have hn := congrArg (fun k ↦ k s) (β.hom.naturality h.op).symm
  change F.obj.map h.op
    ((((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f hf).app F).inv.hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) ≫
        τ.hom.app (op W)) s) = _ at hn
  rw [hn]
  have hs := hτ T J V i t hc hinv₁ hinv₂ hopen hclosed
  change _ = _ at hs
  change ((((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f hf).app F).inv.hom.app
    (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj T)) ≫
      τ.hom.app (op T)) _) = _
  rw [hs]
  have heval {M N : AddCommGrpCat.{u + 1}} (v : J → (M ⟶ N)) (x : M) :
      (∑ j, v j) x = ∑ j, v j x := by
    change ((∑ j, v j).hom) x = _
    have hv := map_sum (AddCommGrpCat.homAddEquiv (M := M) (N := N)) v Finset.univ
    change (∑ j, v j).hom = ∑ j, (v j).hom at hv
    rw [hv]
    exact AddMonoidHom.finsetSum_apply _ _ _
  exact heval _ _

set_option maxRecDepth 2048 in
/-- Local sum characterizations identify two trace morphisms under étale localization.
No compatibility between the choices of the two morphisms is assumed.
Source: Stacks Project, Section 03SH, after Definition 03SE, localization property;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-localization)

Proof. Work at `W` over `X'`. A splitting cover of `W` for the finite étale pullback
of `f` exists by Stacks 04HN and covering base change. The canonical pasting
isomorphism identifies its pullback with the pullback used for `f` on the same
objects regarded as objects of `X.Etale`. Its two projection identities identify
the sections of each splitting: compose a section with the pasting isomorphism,
and its projections are the identity and the same map to `Y`. Conversely use the
inverse isomorphism to transport a splitting in the other direction.

The natural restriction isomorphism `g⁻¹ F ≅ F|_X'` commutes with the restriction
along every such section. The two local sum hypotheses therefore make the two sides
of the desired identity the same finite sum on each member of the splitting cover.
Naturality of the sheaf morphisms and of the restriction isomorphism shows that these
are the restrictions of the displayed maps at `W`, including their input restricted
to the pulled-back object. For each input section, separatedness of `F|_X'` implies
equality of their images at `W`. Extensionality of additive group homomorphisms gives
the asserted equality. Empty splitting covers and empty objects are covered by the
empty-cover sheaf condition. The proof only uses the two projection identities for
`κ`, so it applies to every isomorphism specified in the statement. -/
theorem finiteEtaleTrace_localization_of_localSums
    {X Y X' : Scheme.{u}} (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
    (g : X' ⟶ X) (hg : Etale g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let A := AddCommGrpCat.{u + 1}
    let B := fun {S Z : Scheme.{u}} (q : Z ⟶ S) (hq : Etale q) (W : S.Etale) ↦
      (MorphismProperty.Over.map ⊤ hq).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ q).obj W)
    letI := hfin
    letI := hf
    let f' := pullback.snd f g
    let hf' : Etale f' := inferInstance
    let F' := (upperStar A g).obj F
    ∀ (τ : (lowerStar A f).obj ((upperStar A f).obj F) ⟶ F)
      (τ' : (lowerStar A f').obj ((upperStar A f').obj F') ⟶ F'),
      FiniteEtaleTraceLocalSums f hf F τ → FiniteEtaleTraceLocalSums f' hf' F' τ' →
      ∀ (W : X'.Etale)
        (κ : (MorphismProperty.Over.map ⊤ hg).obj (B f' hf' W) ≅
          B f hf ((MorphismProperty.Over.map ⊤ hg).obj W)),
        κ.hom.left ≫ pullback.fst (W.hom ≫ g) f = pullback.fst W.hom f' →
        κ.hom.left ≫ pullback.snd (W.hom ≫ g) f =
          pullback.snd W.hom f' ≫ pullback.fst f g →
        (((upperStarIsoLocalizationRestriction A f' hf').app F').inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f').obj W))) ≫
          τ'.hom.app (op W) ≫
          ((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app (op W) =
        ((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app
            (op (B f' hf' W)) ≫ F.obj.map κ.inv.op ≫
          (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
              ((MorphismProperty.Over.map ⊤ hg).obj W)))) ≫
            τ.hom.app (op ((MorphismProperty.Over.map ⊤ hg).obj W)) := by
  dsimp only
  intro τ τ' hτ hτ' W κ hκ₁ hκ₂
  let A := AddCommGrpCat.{u + 1}
  let := hfin
  let := hf
  let f' := pullback.snd f g
  let hf' : Etale f' := inferInstance
  let F' := (upperStar A g).obj F
  let B' := MorphismProperty.Over.pullback @Etale ⊤ f' ⋙
    MorphismProperty.Over.map ⊤ hf'
  let ρ := (upperStarIsoLocalizationRestriction A g hg).app F
  let L := ((upperStarIsoLocalizationRestriction A f' hf').app F').inv.hom.app
    (op ((MorphismProperty.Over.pullback @Etale ⊤ f').obj W)) ≫ τ'.hom.app (op W)
  let R := ρ.hom.hom.app (op (B'.obj W)) ≫ F.obj.map κ.inv.op ≫
    ((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
        ((MorphismProperty.Over.map ⊤ hg).obj W))) ≫
    τ.hom.app (op ((MorphismProperty.Over.map ⊤ hg).obj W))
  change L ≫ ρ.hom.hom.app (op W) = R
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨z, hz, huniq⟩ :=
    finiteEtaleTrace_section_descent f' (inferInstance) hf' F' W s
  have hL := localSum_section_formula f' hf' F' τ' hτ' W s
  have hR := finiteEtaleTrace_localization_section_formula f hf g hg F τ hτ
    W κ hκ₁ hκ₂ s
  have he : L s = (R ≫ ρ.inv.hom.app (op W)) s :=
    (huniq _ hL).trans (huniq _ hR).symm
  have hcancel : ρ.inv.hom.app (op W) ≫ ρ.hom.hom.app (op W) =
      𝟙 (F.obj.obj (op ((MorphismProperty.Over.map ⊤ hg).obj W))) := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom]
    simp only [Iso.inv_hom_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
    rfl
  have hs := congrArg (fun x ↦ ρ.hom.hom.app (op W) x) he
  change (L ≫ ρ.hom.hom.app (op W)) s =
    ((R ≫ ρ.inv.hom.app (op W)) ≫ ρ.hom.hom.app (op W)) s at hs
  have hRcancel : (R ≫ ρ.inv.hom.app (op W)) ≫ ρ.hom.hom.app (op W) = R := by
    calc
      _ = R ≫ (ρ.inv.hom.app (op W) ≫ ρ.hom.hom.app (op W)) := Category.assoc _ _ _
      _ = R ≫ 𝟙 _ := congrArg (fun k ↦ R ≫ k) hcancel
      _ = R := Category.comp_id R
  exact hs.trans (congrArg (fun k ↦ k s) hRcancel)

end AlgebraicGeometry.Etale
