/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.AlgebraicGeometry.SiteLocallyConstantFiniteType
import WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import WeilConjectures.CategoryTheory.SiteModuleSheafConstantRingEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Local bounded finite-module models of a good lower truncation

Source: Stacks Project, Cohomology on Sites, Tags 094G and 094H
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{u} C]

set_option quotPrecheck false in
set_option hygiene false in
local notation "𝓡(" J ", " B ")" => (sheafCompose J
  (forget₂ CommRingCat.{u} RingCat.{u})).obj
    ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B))
set_option quotPrecheck false in
set_option hygiene false in
local notation "cB(" J ", " B ")" => strictPerfectConstantPresheaf (C := C) B ⋙
  PresheafOfModules.sheafification.{u} (R := 𝓡(J, B)) (Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat.{u} RingCat.{u}))

private noncomputable instance moduleSheafify
    (J : GrothendieckTopology C) (B : Type u) [CommRing B] :
    HasSheafify J (ModuleCat.{u} B) := inferInstance

private noncomputable instance moduleSheafAbelian
    (J : GrothendieckTopology C) (B : Type u) [CommRing B] :
    Abelian (Sheaf J (ModuleCat.{u} B)) := inferInstance

private noncomputable instance ringModuleSheafAbelian
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u}) :
    Abelian (SheafOfModules.{u} R) := inferInstance

private instance restrictionAdditive
    (J : GrothendieckTopology C) (B : Type u) [CommRing B] (U : C) :
    (J.overPullback (ModuleCat.{u} B) U).Additive where
  map_add := by intros; rfl

private instance constantAdditive
    (J : GrothendieckTopology C) (B : Type u) [CommRing B] :
    (constantSheaf J (ModuleCat.{u} B)).Additive :=
  Functor.additive_of_preserves_binary_products _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def constantRestrictionIso
    (J : GrothendieckTopology C) (B : Type u) [CommRing B] (U : C) :
    constantSheaf (J.over U) (ModuleCat.{u} B) ≅
      constantSheaf J (ModuleCat.{u} B) ⋙ J.overPullback (ModuleCat.{u} B) U :=
  NatIso.ofComponents (constantSheafOverIso J (ModuleCat.{u} B) U) (by
    intro M N f
    apply ((constantSheafAdj (J.over U) (ModuleCat.{u} B)
      Over.mkIdTerminal).homEquiv M _).injective
    rw [constantSheafAdj_homEquiv_apply, constantSheafAdj_homEquiv_apply]
    symm
    change _ ≫ (constantSheafOverHom J (ModuleCat.{u} B) U M).hom.app _ ≫
        ((constantSheaf J (ModuleCat.{u} B)).map f).hom.app _ =
      _ ≫ ((constantSheaf (J.over U) (ModuleCat.{u} B)).map f).hom.app _ ≫
        (constantSheafOverHom J (ModuleCat.{u} B) U N).hom.app _
    have hM := congrArg (fun α ↦ α.app (Opposite.op (Over.mk (𝟙 U))))
      (toSheafify_constantSheafOverHom_hom J (ModuleCat.{u} B) U M)
    have hN := congrArg (fun α ↦ α.app (Opposite.op (Over.mk (𝟙 U))))
      (toSheafify_constantSheafOverHom_hom J (ModuleCat.{u} B) U N)
    have hf := congrArg (fun α ↦ α.app (Opposite.op (Over.mk (𝟙 U))))
      (toSheafify_naturality (J := J.over U) ((Functor.const (Over U)ᵒᵖ).map f))
    have hf' := congrArg (fun α ↦ α.app (Opposite.op U))
      (toSheafify_naturality (J := J) ((Functor.const Cᵒᵖ).map f))
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hM hN hf hf'
    change f ≫ _ = _ ≫ ((constantSheaf (J.over U) (ModuleCat.{u} B)).map f).hom.app _ at hf
    change f ≫ _ = _ ≫ ((constantSheaf J (ModuleCat.{u} B)).map f).hom.app _ at hf'
    erw [← Category.assoc, hM, ← hf', ← Category.assoc, ← hf, Category.assoc, hN]
    rfl)

private noncomputable def constantOverMapNatIso
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    {U V : C} (f : U ⟶ V) :
    constantSheaf (J.over U) (ModuleCat.{u} B) ≅
      constantSheaf (J.over V) (ModuleCat.{u} B) ⋙
        J.overMapPullback (ModuleCat.{u} B) f :=
  constantRestrictionIso J B U ≪≫
    Functor.isoWhiskerRight (constantRestrictionIso J B V).symm
      (J.overMapPullback (ModuleCat.{u} B) f)

private noncomputable def sliceBack
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    {V : C} (W : Over V) :
    Sheaf ((J.over V).over W) (ModuleCat.{u} B) ⥤
      Sheaf (J.over W.left) (ModuleCat.{u} B) :=
  W.iteratedSliceEquiv.inverse.sheafPushforwardContinuous (ModuleCat.{u} B)
    (J.over W.left) ((J.over V).over W)

private instance sliceBackEquivalence
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    {V : C} (W : Over V) : (sliceBack J B W).IsEquivalence :=
  inferInstanceAs (W.iteratedSliceEquiv.inverse.sheafPushforwardContinuous (ModuleCat.{u} B)
    (J.over W.left) ((J.over V).over W)).IsEquivalence

private instance sliceBackAdditive
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    {V : C} (W : Over V) : (sliceBack J B W).Additive where
  map_add := by intros; rfl

private noncomputable def sliceBackConstantIso
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    {V : C} (W : Over V) :
    constantSheaf ((J.over V).over W) (ModuleCat.{u} B) ⋙ sliceBack J B W ≅
      constantSheaf (J.over W.left) (ModuleCat.{u} B) :=
  (equivCommuteConstant' (J.over W.left) (ModuleCat.{u} B)
    ((J.over V).over W) W.iteratedSliceEquiv.inverse Over.mkIdTerminal
    (Over.mkIdTerminal.isTerminalObj W.iteratedSliceEquiv.inverse (Over.mk (𝟙 W.left)))).symm

private noncomputable def sliceBackRestrictionIso
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    {V : C} (W : Over V) :
    J.overPullback (ModuleCat.{u} B) V ⋙
        (J.over V).overPullback (ModuleCat.{u} B) W ⋙ sliceBack J B W ≅
      J.overPullback (ModuleCat.{u} B) W.left :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by cat_disch)

private noncomputable def complexHomologyIso
    {A D : Type*} [Category A] [Abelian A] [Category D] [Abelian D]
    (F : A ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (q : ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).homology q ≅ F.obj (K.homology q) :=
  (K.sc q).mapHomologyIso F

set_option backward.isDefEq.respectTransparency false in
private theorem module_bounded_model_sieve
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{u + 1} (Sheaf J.toGrothendieck (ModuleCat.{u} B))]
    [∀ U : C, HasDerivedCategory.{u + 1}
      (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))]
    (N : CochainComplex (Sheaf J.toGrothendieck (ModuleCat.{u} B)) ℤ)
    (a b : ℤ) (hab : a ≤ b)
    (hvan : ∀ q : ℤ, q < a ∨ b < q → IsZero (N.homology q))
    (hloc : ∀ (q : ℤ) (W : C), ∃ S : Sieve W, S ∈ J.toGrothendieck W ∧
      ∀ (U : C) (f : U ⟶ W), S f →
        ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
          ((J.toGrothendieck.overPullback (ModuleCat.{u} B) U).obj (N.homology q) ≅
            (constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)).obj M))
    (V : C) :
    ∃ S : Sieve V, S ∈ J.toGrothendieck V ∧
      ∀ (U : C) (f : U ⟶ V), S f →
        ∃ E : CochainComplex (ModuleCat.{u} B) ℤ,
          (∀ q : ℤ, q < a ∨ b < q → IsZero (E.X q)) ∧
          (∀ q : ℤ, Module.Finite B (E.X q)) ∧ Nonempty
            (DerivedCategory.Q.obj
                (((J.toGrothendieck.overPullback (ModuleCat.{u} B) U).mapHomologicalComplex
                  (.up ℤ)).obj N) ≅
              DerivedCategory.Q.obj
                (((constantSheaf (J.toGrothendieck.over U)
                  (ModuleCat.{u} B)).mapHomologicalComplex (.up ℤ)).obj E)) := by
  classical
  let L := J.comap (Over.forget V)
  have model := @exists_site_bounded_constant_model.{u, u + 1} (Over V) inferInstance L
    inferInstance inferInstance inferInstance inferInstance
    (Over.mk (𝟙 V)) Over.mkIdTerminal B inferInstance inferInstance
  rw [← over_toGrothendieck_eq_toGrothendieck_comap_forget J V] at model
  let (W : Over V) := HasDerivedCategory.standard
    (Sheaf ((J.toGrothendieck.over V).over W) (ModuleCat.{u} B))
  let R := J.toGrothendieck.overPullback (ModuleCat.{u} B) V
  have : R.Additive := inferInstance
  let N₀ := (R.mapHomologicalComplex (.up ℤ)).obj N
  let K := DerivedCategory.Q.obj N₀
  let eH (q : ℤ) :
      (DerivedCategory.homologyFunctor _ q).obj K ≅ R.obj (N.homology q) :=
    (DerivedCategory.homologyFunctorFactors _ q).app N₀ ≪≫ complexHomologyIso R N q
  have hvan₀ (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) :=
    IsZero.of_iso (R.map_isZero (hvan q hq)) (eH q)
  have hloc₀ (q : ℤ) (W : Over V) :
      ∃ (I : Type u) (U : I → Over V) (f : ∀ i, U i ⟶ W),
        Presieve.ofArrows U f ∈ L W ∧
        ∀ i, ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
          (((J.toGrothendieck.over V).overPullback (ModuleCat.{u} B) (U i)).obj
            ((DerivedCategory.homologyFunctor _ q).obj K) ≅
            (constantSheaf ((J.toGrothendieck.over V).over (U i))
              (ModuleCat.{u} B)).obj M) := by
    obtain ⟨S, hS, h⟩ := hloc q W.left
    obtain ⟨T, hT, hTS⟩ := J.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
    obtain ⟨I, U, f, rfl⟩ := T.exists_eq_ofArrows
    let U' (i : I) : Over V := Over.mk (f i ≫ W.hom)
    let f' (i : I) : U' i ⟶ W := Over.homMk (f i)
    refine ⟨I, U', f', ?_, fun i ↦ ?_⟩
    · rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
      change Presieve.ofArrows U f ∈ J W.left
      exact hT
    · obtain ⟨M, hf, ⟨e⟩⟩ := h (U i) (f i) (hTS _ _ (Presieve.ofArrows.mk i))
      let F := (J.toGrothendieck.over V).overPullback (ModuleCat.{u} B) (U' i)
      let G := sliceBack J.toGrothendieck B (U' i)
      refine ⟨M, hf, ⟨G.preimageIso ?_⟩⟩
      exact G.mapIso (F.mapIso (eH q)) ≪≫
        (sliceBackRestrictionIso J.toGrothendieck B (U' i)).app (N.homology q) ≪≫
        e ≪≫ ((sliceBackConstantIso J.toGrothendieck B (U' i)).app M).symm
  obtain ⟨I, U, f, hcover, hmodels⟩ := model K a b hab hvan₀ hloc₀
  have hs (i : I) : ∃ E : CochainComplex (ModuleCat.{u} B) ℤ,
      (∀ q : ℤ, q < a ∨ b < q → IsZero (E.X q)) ∧
      (∀ q : ℤ, Module.Finite B (E.X q)) ∧ Nonempty
        (DerivedCategory.Q.obj
            (((J.toGrothendieck.overPullback (ModuleCat.{u} B) (U i).left).mapHomologicalComplex
               (.up ℤ)).obj N) ≅
          DerivedCategory.Q.obj
            (((constantSheaf (J.toGrothendieck.over (U i).left)
              (ModuleCat.{u} B)).mapHomologicalComplex (.up ℤ)).obj E)) := by
    obtain ⟨E, hf, hz, ⟨e⟩⟩ := hmodels i
    let F := (J.toGrothendieck.over V).overPullback (ModuleCat.{u} B) (U i)
    let G := sliceBack J.toGrothendieck B (U i)
    have : F.Additive := inferInstance
    have : G.Additive := Functor.additive_of_preserves_binary_products _
    refine ⟨E, hz, hf, ⟨?_⟩⟩
    let e₁ := DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (sliceBackRestrictionIso J.toGrothendieck B (U i))
        (.up ℤ)).app N)
    let e₂ := G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj N₀)
    let e₃ := G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app N₀)
    let e₄ := G.mapDerivedCategory.mapIso e
    let e₅ := G.mapDerivedCategoryFactors.app
      (((constantSheaf ((J.toGrothendieck.over V).over (U i))
        (ModuleCat.{u} B)).mapHomologicalComplex (.up ℤ)).obj E)
    let e₆ := DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (sliceBackConstantIso J.toGrothendieck B (U i))
        (.up ℤ)).app E)
    exact e₁.symm ≪≫ e₂.symm ≪≫ e₃.symm ≪≫ e₄ ≪≫ e₅ ≪≫ e₆
  let Ui (i : I) := (U i).left
  let fi (i : I) : Ui i ⟶ V := (f i).left
  have hc : Presieve.ofArrows Ui fi ∈ J V := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hcover
    exact hcover
  refine ⟨Sieve.ofArrows Ui fi, J.generate_mem_toGrothendieck hc, ?_⟩
  intro W g hg
  obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff Ui fi g).mp hg
  obtain ⟨E, hz, hf, ⟨e⟩⟩ := hs i
  let H := J.toGrothendieck.overMapPullback (ModuleCat.{u} B) h
  have : H.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteColimits H :=
    ⟨fun _ _ _ ↦ PreservesColimitsOfSize.preservesColimitsOfShape
      (self := Adjunction.leftAdjoint_preservesColimits
        (Functor.sheafAdjunctionCocontinuous (Over.map h) (ModuleCat.{u} B)
          (J.toGrothendieck.over W) (J.toGrothendieck.over (Ui i))))⟩
  refine ⟨E, hz, hf, ⟨?_⟩⟩
  let eR : J.toGrothendieck.overPullback (ModuleCat.{u} B) (Ui i) ⋙ H ≅
      J.toGrothendieck.overPullback (ModuleCat.{u} B) W :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by cat_disch)
  exact (DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso eR (.up ℤ)).app N)).symm ≪≫
    (H.mapDerivedCategoryFactors.app _).symm ≪≫
    H.mapDerivedCategory.mapIso e ≪≫ H.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (constantOverMapNatIso J.toGrothendieck B h)
        (.up ℤ)).app E).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
/-- A good lower truncation of a bounded-above complex with locally constant finite
cohomology has local bounded finite-module models, in the ring-sheaf module encoding.
The model is a genuine module complex, including its differentials.

Source: Stacks Project, Cohomology on Sites, Tag 094G, applied on slices, and Tag 094H.
(auxiliary; not a blueprint node).

Proof: Choose an upper cohomological bound b. Exact slice restriction commutes with
cohomology and good truncation, so the truncation has cohomology in [a,b]. Its retained
cohomology has the stated local constant descriptions; all other cohomology is zero.
On the slice over V, apply the local bounded constant model theorem (Tag 094G), with
the terminal object id_V. If a > b, use the zero complex instead. To pass between the
two encodings use `site_moduleSheaf_constantRing_equivalence`, whose extension of
scalars retains the additive sheaf and is naturally compatible with constants. The
equivalence commutes with slice restriction
and with the constant-module realization, since their units are the same constant-ring
sheafification unit. Hence it transports both the hypotheses and the derived model
isomorphism. Constant restriction is natural in module maps, so the complex on a slice
is the restriction of the global constant realization, including differentials. Take
the sieve generated by the resulting covering family. Further restriction preserves
the model, its finite terms and its bounds, by relocalization and the same natural
constant-restriction comparison. This supplies a model for every arrow of the sieve.
Empty slices have the zero model. No point of the site is used. -/
theorem exists_site_bounded_truncation_models
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    (P : CochainComplex (SheafOfModules.{u} (𝓡(J.toGrothendieck, B))) ℤ)
    (hbounded : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (P.homology j))
    (hlc : ∀ j : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B (P.homology j))
    (a : ℤ) (V : C) :
    ∃ S : Sieve V, S ∈ J.toGrothendieck V ∧
      ∀ (U : C) (f : U ⟶ V), S f →
        letI := HasDerivedCategory.standard (SheafOfModules.{u} ((𝓡(J.toGrothendieck, B)).over U))
        ∃ (E : CochainComplex (ModuleCat.{u} B) ℤ) (b : ℤ),
          (∀ j : ℤ, j < a ∨ b < j → IsZero (E.X j)) ∧
          (∀ j : ℤ, Module.Finite B (E.X j)) ∧
          Nonempty
            (DerivedCategory.Q.obj
                (((overFunctor.{u} (𝓡(J.toGrothendieck, B)) U).mapHomologicalComplex
                  (.up ℤ)).obj (P.truncGE a)) ≅
              DerivedCategory.Q.obj
                ((((cB(J.toGrothendieck, B)) ⋙
                  overFunctor.{u} (𝓡(J.toGrothendieck, B)) U).mapHomologicalComplex
                    (.up ℤ)).obj E)) := by
  classical
  let R := 𝓡(J.toGrothendieck, B)
  let α := Functor.whiskerRight
    (toSheafify J.toGrothendieck ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat.{u} RingCat.{u})
  obtain ⟨G, hG, ⟨ec⟩, hslice⟩ :=
    site_moduleSheaf_restriction_equivalence J.toGrothendieck B R α
  have : G.IsEquivalence := hG
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  let T := P.truncGE a
  let N := (G.mapHomologicalComplex (.up ℤ)).obj T
  let eH (q : ℤ) : N.homology q ≅ G.obj (T.homology q) :=
    complexHomologyIso G T q
  have hzero (q : ℤ) (hq : q < a) : IsZero (N.homology q) :=
    IsZero.of_iso (G.map_isZero (T.isZero_of_isGE a q hq)) (eH q)
  obtain ⟨b, hb⟩ := hbounded
  have hvan (q : ℤ) (hq : q < a ∨ max a b < q) : IsZero (N.homology q) := by
    by_cases hqa : q < a
    · exact hzero q hqa
    · have : QuasiIsoAt (P.πTruncGE a) q :=
        P.quasiIsoAt_πTruncGE a q (by omega)
      exact IsZero.of_iso (G.map_isZero (hb q (by omega)))
        (eH q ≪≫ G.mapIso (isoOfQuasiIsoAt (P.πTruncGE a) q).symm)
  have hloc (q : ℤ) (W : C) : ∃ S : Sieve W, S ∈ J.toGrothendieck W ∧
      ∀ (U : C) (f : U ⟶ W), S f →
        ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
          ((J.toGrothendieck.overPullback (ModuleCat.{u} B) U).obj (N.homology q) ≅
            (constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)).obj M) := by
    by_cases hqa : q < a
    · refine ⟨⊤, J.toGrothendieck.top_mem W, fun U _ _ ↦
        ⟨ModuleCat.of B (Fin 0 → B), inferInstance, ⟨?_⟩⟩⟩
      exact ((J.toGrothendieck.overPullback (ModuleCat.{u} B) U).map_isZero
        (hzero q hqa)).iso
          ((constantSheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)).map_isZero
            (ModuleCat.isZero_of_subsingleton _))
    · have : QuasiIsoAt (P.πTruncGE a) q :=
        P.quasiIsoAt_πTruncGE a q (by omega)
      obtain ⟨S, hS, h⟩ := hlc q W
      refine ⟨S, hS, fun U f hf ↦ ?_⟩
      obtain ⟨M, hM, ⟨e⟩⟩ := h U f hf
      obtain ⟨GU, hGU, ⟨eU⟩⟩ := hslice U
      have : GU.IsEquivalence := hGU
      let F := J.toGrothendieck.overPullback (ModuleCat.{u} B) U
      refine ⟨M, hM, ⟨?_⟩⟩
      let e₁ := F.mapIso (eH q)
      let e₂ := F.mapIso (G.mapIso (isoOfQuasiIsoAt (P.πTruncGE a) q).symm)
      let e₃ := (eU.app (P.homology q)).symm
      let e₄ := GU.mapIso e
      let e₅ := eU.app ((cB(J.toGrothendieck, B)).obj M)
      let e₆ := F.mapIso (ec.app M)
      let e₇ := ((constantRestrictionIso J.toGrothendieck B U).app M).symm
      exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆ ≪≫ e₇
  let := HasDerivedCategory.standard (Sheaf J.toGrothendieck (ModuleCat.{u} B))
  let (U : C) := HasDerivedCategory.standard
    (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B))
  obtain ⟨S, hS, h⟩ := module_bounded_model_sieve J B N a (max a b) (le_max_left _ _)
    hvan hloc V
  refine ⟨S, hS, fun U f hf ↦ ?_⟩
  let := HasDerivedCategory.standard (SheafOfModules.{u} (R.over U))
  obtain ⟨E, hz, hfinite, ⟨e⟩⟩ := h U f hf
  obtain ⟨GU, hGU, ⟨eU⟩⟩ := hslice U
  have : GU.IsEquivalence := hGU
  have : GU.Additive := Functor.additive_of_preserves_binary_products _
  refine ⟨E, max a b, hz, hfinite, ⟨GU.mapDerivedCategory.preimageIso ?_⟩⟩
  let F := J.toGrothendieck.overPullback (ModuleCat.{u} B) U
  let e₁ := GU.mapDerivedCategoryFactors.app
    (((overFunctor.{u} R U).mapHomologicalComplex (.up ℤ)).obj T)
  let e₂ := DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex eU (.up ℤ)).app T)
  let e₃ := DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex (constantRestrictionIso J.toGrothendieck B U)
      (.up ℤ)).app E)
  let e₄ := DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex (Functor.isoWhiskerRight ec F) (.up ℤ)).app E)
  let e₅ := DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft (cB(J.toGrothendieck, B)) eU)
      (.up ℤ)).app E)
  let e₆ := GU.mapDerivedCategoryFactors.app
    ((((cB(J.toGrothendieck, B)) ⋙ overFunctor.{u} R U).mapHomologicalComplex
      (.up ℤ)).obj E)
  exact e₁ ≪≫ e₂ ≪≫ e ≪≫ e₃ ≪≫ e₄.symm ≪≫ e₅.symm ≪≫ e₆.symm

end SheafOfModules
