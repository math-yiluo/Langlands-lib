/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection

/-! The canonical coefficient-sized closed localization unit.

Source: Stacks Project, proetale.tex, Tags 09AH and 09AF.
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

def coefficientFixedSiteAdjunction {C D : Type w} [SmallCategory C] [SmallCategory D]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsContinuous J K] (A : Type w) [CommRing A] :
    Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{w} A) J K ⊣
      G.sheafPushforwardContinuous (ModuleCat.{w} A) J K :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G (ModuleCat.{w} A) J K

noncomputable def coefficientFixedCanonicalAdj
    (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) :
    Scheme.coefficientProEtaleFixedModulePullback.{u, v} i A ⊣
      (Scheme.coefficientProEtaleModelBaseChange.{u, v} i).sheafPushforwardContinuous
        (ModuleCat.{max v (u + 1)} A)
        (Scheme.coefficientProEtaleModelTopology.{u, v} X)
        (Scheme.coefficientProEtaleModelTopology.{u, v} Z) :=
  coefficientFixedSiteAdjunction
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} i)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} Z) A

/- The geometric argument is independent of the coefficient universe. We work on the
original site, where covering families have their usual scheme-theoretic description,
and transport only the concluding epimorphism to the coefficient-sized site. -/

open Scheme

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance modelDownEquiv (X : Scheme.{u}) :
    (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).IsEquivalence :=
  (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_inverse

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance modelDownDense (X : Scheme.{u}) :
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).inverse.IsDenseSubsite
      (coefficientProEtaleModelTopology.{u, v} X) (ProEt.topology X) := by
  change (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).IsDenseSubsite
    ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).inducedTopology
      (ProEt.topology X)) (ProEt.topology X)
  infer_instance

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance rawSheafify (A : Type (max v (u + 1))) [CommRing A]
    (X : Scheme.{u}) : HasSheafify (ProEt.topology X) (ModuleCat.{max v (u + 1)} A) := by
  have : HasSheafify (coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A) :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let e := AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)
  exact e.hasSheafify (ProEt.topology X)
    (coefficientProEtaleModelTopology.{u, v} X) (ModuleCat.{max v (u + 1)} A)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance rawKan (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) (F : X.ProEtᵒᵖ ⥤ ModuleCat.{max v (u + 1)} A) :
    (proEtaleBaseChange i).op.HasPointwiseLeftKanExtension F := by
  intro Y
  have : HasColimitsOfShape (CostructuredArrow (proEtaleBaseChange i).op Y)
      (ModuleCat.{max v (u + 1)} A) :=
    hasColimitsOfShape_of_essentiallySmall.{max v (u + 1)} _ _
  infer_instance

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private abbrev rawPush (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) :=
  (proEtaleBaseChange i).sheafPushforwardContinuous (ModuleCat.{max v (u + 1)} A)
    (ProEt.topology X) (ProEt.topology Z)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private abbrev rawPull (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (proEtaleBaseChange i) (ModuleCat.{max v (u + 1)} A)
    (ProEt.topology X) (ProEt.topology Z)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def rawAdj (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) : rawPull A i ⊣ rawPush A i :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleBaseChange i) (ModuleCat.{max v (u + 1)} A)
    (ProEt.topology X) (ProEt.topology Z)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance rawPushAdditive (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) : (rawPush A i).Additive where

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance rawW (A : Type (max v (u + 1))) [CommRing A] (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{max v (u + 1)} A) := by
  let G : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt := AsSmall.down
  have : (coefficientProEtaleModelTopology.{u, v} X).WEqualsLocallyBijective
      (ModuleCat.{max v (u + 1)} A) := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.transport
    (ProEt.topology X) (coefficientProEtaleModelTopology.{u, v} X)
    G (Functor.IsDenseSubsite.coverPreserving _ _ _)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance rawPullAdditive (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) : (rawPull A i).Additive :=
  (rawAdj A i).left_adjoint_additive

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def rawPushComp (A : Type (max v (u + 1))) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rawPush A f ⋙ rawPush A g ≅ rawPush A (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm)
    (ModuleCat.{max v (u + 1)} A) (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def rawPushCongr (A : Type (max v (u + 1))) [CommRing A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) : rawPush A f ≅ rawPush A g :=
  Functor.sheafPushforwardContinuousIso
    (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) h)
    (ModuleCat.{max v (u + 1)} A) (ProEt.topology Y) (ProEt.topology X)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def rawPushId (A : Type (max v (u + 1))) [CommRing A] (X : Scheme.{u}) :
    rawPush A (𝟙 X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X)
    (ModuleCat.{max v (u + 1)} A) (ProEt.topology X)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance rawPushIso (A : Type (max v (u + 1))) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : (rawPush A f).IsEquivalence := by
  let e := asIso f
  let E := CategoryTheory.Equivalence.mk (rawPush A e.hom) (rawPush A e.inv)
    ((rawPushId A X).symm ≪≫ rawPushCongr A e.hom_inv_id.symm ≪≫
      (rawPushComp A e.hom e.inv).symm)
    (rawPushComp A e.inv e.hom ≪≫ rawPushCongr A e.inv_hom_id ≪≫ rawPushId A Y)
  exact E.isEquivalence_functor

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private lemma closedSitePrecompFullyFaithful
    (R : Type (max v (u + 1))) [CommRing R] (A : Type u) [CommRing A] (I : Ideal A) :
    Nonempty (((Functor.whiskeringLeft _ _ (ModuleCat.{max v (u + 1)} R)).obj
      (AffineProEt.closedSiteBaseChange A I).op).FullyFaithful) := by
  obtain ⟨adj, h⟩ := AffineProEt.exists_closedSiteAdjunction A I
  have : IsIso adj.unit := h
  let adjp := adj.op.whiskerLeft (ModuleCat.{max v (u + 1)} R)
  have : ∀ F, IsIso (adjp.counit.app F) := fun F => by
    have : ∀ X, IsIso ((adjp.counit.app F).app X) := fun X => by
      change IsIso (F.map (adj.unit.app X.unop).op)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have : IsIso adjp.counit := NatIso.isIso_of_isIso_app _
  exact ⟨adjp.fullyFaithfulROfIsIsoCounit⟩

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private lemma isIso_closedCounit_of_quotient
    (R : Type (max v (u + 1))) [CommRing R] (A : Type u) [CommRing A] (I : Ideal A) :
    IsIso (rawAdj R
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).counit := by
  obtain ⟨hpre⟩ := closedSitePrecompFullyFaithful R A I
  let F := rawPush R
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  let RX := (AffineProEt.toProEt (Spec (.of A))).sheafPushforwardContinuous
    (ModuleCat.{max v (u + 1)} R) (AffineProEt.topology (Spec (.of A)))
      (ProEt.topology (Spec (.of A))) ⋙
    sheafToPresheaf (AffineProEt.topology (Spec (.of A))) (ModuleCat.{max v (u + 1)} R)
  let RZ := (AffineProEt.toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous
    (ModuleCat.{max v (u + 1)} R) (AffineProEt.topology (Spec (.of (A ⧸ I))))
      (ProEt.topology (Spec (.of (A ⧸ I)))) ⋙
    sheafToPresheaf (AffineProEt.topology (Spec (.of (A ⧸ I)))) (ModuleCat.{max v (u + 1)} R)
  have hRZ : RZ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  have hcomp : (F ⋙ RX).FullyFaithful := hRZ.comp hpre
  have hF : F.FullyFaithful := hcomp.ofCompFaithful
  have : F.Full := hF.full
  have : F.Faithful := hF.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private lemma isIso_closedCounit_of_isAffine
    (R : Type (max v (u + 1))) [CommRing R] {Z X : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso (rawAdj R i).counit := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := i ≫ X.isoSpec.hom)).mp inferInstance
  have hq := isIso_closedCounit_of_quotient R (Γ(X, ⊤)) I
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : (rawPush R q).Full :=
    (rawAdj R q).fullyFaithfulROfIsIsoCounit.full
  have : (rawPush R q).Faithful :=
    (rawAdj R q).fullyFaithfulROfIsIsoCounit.faithful
  have h : (rawPush R (e.hom) ⋙ (rawPush R q)).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  have h' := h.ofIso (rawPushComp R e.hom q ≪≫
    rawPushCongr R he.symm)
  have h'' : (rawPush R (i) ⋙
      (rawPush R X.isoSpec.hom)).FullyFaithful :=
    h'.ofIso (rawPushComp R i X.isoSpec.hom).symm
  have hF := h''.ofCompFaithful
  have := hF.full
  have := hF.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The forgetful functor of modules preserves the colimits computing the left Kan extension
along the opposite of base change: they are filtered, base change being representably flat. -/
private instance rawPreservesFiltered
    (R : Type (max v (u + 1))) [CommRing R] {U Z : Scheme.{u}} (g : Z ⟶ U) (Y) :
    PreservesColimitsOfShape
    (CostructuredArrow (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op Y)
    (forget (ModuleCat.{max v (u + 1)} R)) := by
  have : IsFiltered (CostructuredArrow (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op Y) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ Y.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget (ModuleCat.{max v (u + 1)} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, max v (u + 1), u, max v (u + 1)} _
  infer_instance

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- **Local vanishing.** If the image of a section `s` of `F` over `V` under the unit
`F ⟶ g_* g^* F` vanishes, then there is a pro-étale cover of `V ×_U Z` each of whose members
factors through the base change `V' ×_U Z` of a morphism `f : V' ⟶ V` of the pro-étale site
with `s|_{V'} = 0`. -/
private lemma rawLocalVanish
    (R : Type (max v (u + 1))) [CommRing R] {U Z : Scheme.{u}} (g : Z ⟶ U)
    (F : Sheaf (ProEt.topology U) (ModuleCat.{max v (u + 1)} R)) {V : U.ProEt}
    (s : ToType (F.obj.obj (op V)))
    (hs : ((rawAdj R g).unit.app F).hom.app (op V) s =
      0) :
    ∃ P ∈ Scheme.ProEt.precoverage Z ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V),
      ∀ ⦃T⦄ (φ : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V), P φ →
        ∃ (V' : U.ProEt) (f : V' ⟶ V)
          (ψ : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V'),
          ψ ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f = φ ∧
            F.obj.map f.op s = 0 := by
  set G := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
  have hunit : ((rawAdj R g).unit.app F).hom.app
      (op V) = (G.op.leftKanExtensionUnit F.obj).app (op V) ≫
        (toSheafify (ProEt.topology Z) (G.op.leftKanExtension F.obj)).app (op (G.obj V)) := rfl
  rw [hunit, ConcreteCategory.comp_apply] at hs
  have hS := Presheaf.equalizerSieve_mem (Scheme.ProEt.topology Z)
    (toSheafify (Scheme.ProEt.topology Z) (G.op.leftKanExtension F.obj)) (X := op (G.obj V))
      ((G.op.leftKanExtensionUnit F.obj).app (op V) s) 0
      (hs.trans (map_zero _).symm)
  obtain ⟨P, hP, hle⟩ := Scheme.ProEt.mem_topology_iff.1 hS
  refine ⟨P, hP, fun T φ hφ ↦ ?_⟩
  have h₁ := hle _ _ hφ
  obtain ⟨V', f, ψ, hψ, h⟩ := Functor.exists_map_eq_of_leftKanExtensionUnit_eq G F.obj φ s 0
    (by simpa using h₁)
  exact ⟨V', f, ψ, hψ, by simpa using h⟩

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- **Restrictions along a quasi-compact jointly surjective family detect sections.** Let
`g k : Z k ⟶ U` be finitely many quasi-compact morphisms jointly covering `U`. A section `s` of
a pro-étale sheaf of modules `F` on `U` whose images under the units `F ⟶ (g k)_* (g k)^* F` all
vanish is zero: `s` vanishes on weakly étale neighbourhoods of the points of every
`V ×_U Z k` (`AlgebraicGeometry.ProEtale.rawLocalVanish`), and these
neighbourhoods form a pro-étale cover of `V`
(`AlgebraicGeometry.QuasiCompactCover.of_comp_factor`). -/
private theorem rawDetectSections
    (R : Type (max v (u + 1))) [CommRing R] {U : Scheme.{u}}
    {κ : Type*} [Finite κ] {Z : κ → Scheme.{u}}
    (g : ∀ k, Z k ⟶ U) [∀ k, QuasiCompact (g k)] (hg : ∀ x, ∃ k, x ∈ Set.range (g k))
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max v (u + 1)} R)) {V : U.ProEt}
    (s : ToType (F.obj.obj (op V)))
    (hs : ∀ k, ((rawAdj R (g k)).unit.app F).hom.app
      (op V) s = 0) :
    s = 0 := by
  choose P hP hPs using fun k ↦ rawLocalVanish R (g k) F s (hs k)
  choose ι T φ hTφ using fun k ↦ (P k).exists_eq_ofArrows
  choose V' f ψ hψ hf using fun (p : Σ k, ι k) ↦
    hPs p.1 (φ p.1 p.2) (by rw [hTφ p.1]; exact .mk p.2)
  let D : PreZeroHypercover V.left := ⟨Σ k, ι k, fun p ↦ (V' p).left, fun p ↦ (f p).left⟩
  let E (k : κ) : PreZeroHypercover
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (g k)).obj V).left :=
    ⟨ι k, fun m ↦ (T k m).left, fun m ↦ (φ k m).left⟩
  have hE (k : κ) : (E k).presieve₀ ∈ Scheme.proetalePrecoverage _ := by
    have := hP k
    rw [hTφ k, Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at this
    exact this
  have : ∀ k, QuasiCompactCover (E k) := fun k ↦
    Scheme.presieve₀_mem_qcPrecoverage_iff.1 (hE k).1
  have hD : QuasiCompactCover D := by
    refine QuasiCompactCover.of_comp_factor (fun k ↦ pullback.fst V.hom (g k)) (fun x ↦ ?_) E D
      (fun k m ↦ ⟨k, m⟩) (fun k m ↦ (ψ ⟨k, m⟩).left ≫ pullback.fst _ _) fun k m ↦ ?_
    · obtain ⟨k, z, hz⟩ := hg (V.hom x)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hz.symm
      exact ⟨k, w, hw⟩
    · have := congrArg (fun a ↦ a.left ≫ pullback.fst V.hom (g k)) (hψ ⟨k, m⟩)
      simpa using this
  have hDmem : D.presieve₀ ∈ Scheme.proetalePrecoverage V.left := by
    refine ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hD, ?_⟩
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).2 ⟨fun x ↦ ?_, fun p ↦ ?_⟩
    · obtain ⟨k, z, hz⟩ := hg (V.hom x)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hz.symm
      obtain ⟨m, τ, rfl⟩ :=
        ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 (hE k).2).1 w
      refine ⟨⟨k, m⟩, (ψ ⟨k, m⟩).left ≫ pullback.fst _ _ |>.base τ, ?_⟩
      have key : (ψ ⟨k, m⟩).left ≫ pullback.fst _ _ ≫ (f ⟨k, m⟩).left =
          (φ k m).left ≫ pullback.fst V.hom (g k) := by
        rw [← hψ ⟨k, m⟩]
        simp
      rw [← hw]
      change ((ψ ⟨k, m⟩).left ≫ pullback.fst _ _ ≫ (f ⟨k, m⟩).left).base τ =
        ((φ k m).left ≫ pullback.fst V.hom (g k)).base τ
      exact congrArg (fun a ↦ a.base τ) key
    · exact MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) (f p).left
        V.hom V.prop (by rw [MorphismProperty.Over.w (f p)]; exact (V' p).prop)
  have hmem : Presieve.ofArrows V' f ∈ Scheme.ProEt.precoverage U V := by
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hDmem
  have hS : Sieve.generate (Presieve.ofArrows V' f) ∈ Scheme.ProEt.topology U V :=
    Scheme.ProEt.mem_topology_iff.2 ⟨_, hmem, Sieve.le_generate _⟩
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (forget (ModuleCat.{max v (u + 1)} R))
      F.property) _ hS
  rw [← Presieve.isSheafFor_iff_generate] at hsh
  refine hsh.isSeparatedFor.ext fun _ _ ⟨p⟩ ↦ ?_
  change F.obj.map (f p).op s = F.obj.map (f p).op 0
  rw [hf p, map_zero]

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- **Pullbacks along a quasi-compact jointly surjective family are jointly faithful.** A
morphism of pro-étale sheaves of modules on `U` whose pullbacks along finitely many
quasi-compact morphisms `g k : Z k ⟶ U` jointly covering `U` vanish is zero. -/
private theorem rawDetectMaps
    (R : Type (max v (u + 1))) [CommRing R] {U : Scheme.{u}}
    {κ : Type*} [Finite κ] {Z : κ → Scheme.{u}}
    (g : ∀ k, Z k ⟶ U) [∀ k, QuasiCompact (g k)] (hg : ∀ x, ∃ k, x ∈ Set.range (g k))
    {F G : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max v (u + 1)} R)} (φ : F ⟶ G)
    (h : ∀ k, (rawPull R (g k)).map φ = 0) : φ = 0 := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ModuleCat.hom_ext
    (LinearMap.ext fun x ↦ ?_)))
  refine rawDetectSections R g hg G (φ.hom.app V x) fun k ↦ ?_
  have h0 : φ ≫ (rawAdj R (g k)).unit.app G = 0 := by
    have := (rawAdj R (g k)).unit.naturality φ
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map, h k,
      Functor.map_zero, comp_zero] at this
    exact this
  have := congrArg (fun ψ ↦ (ψ.hom.app V).hom x) h0
  simpa using this

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem rawOpenZero (A : Type (max v (u + 1))) [CommRing A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{max v (u + 1)} A)) :
    IsZero ((rawPull A j).obj ((rawPush A i).obj M)) := by
  let l := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  let r := (l.sheafPushforwardContinuous (ModuleCat.{max v (u + 1)} A)
    (ProEt.topology U) (ProEt.topology X))
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial).sheafPushforwardContinuous
      (E := ModuleCat.{max v (u + 1)} A) (ProEt.topology U) (ProEt.topology X)
  have hz : IsZero (r.obj ((rawPush A i).obj M)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply Sheaf.hom_ext
    ext V x
    let T := (proEtaleBaseChange i).obj (l.obj V.unop)
    have : IsEmpty T.left := by
      refine ⟨fun z ↦ ?_⟩
      have hz : (pullback.fst (V.unop.hom ≫ j) i ≫ V.unop.hom ≫ j).base z ∈
          Set.range i.base ∩ Set.range j.base := by
        refine ⟨?_, ⟨_, rfl⟩⟩
        rw [pullback.condition]
        exact ⟨_, rfl⟩
      rw [hU, Set.inter_compl_self] at hz
      exact hz
    exact ConcreteCategory.congr_hom
      ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M T).hom_ext (𝟙 _) 0) x
  exact hz.of_iso (((rawAdj A j).leftAdjointUniq a).app _)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem rawUnitEpi (A : Type (max v (u + 1))) [CommRing A]
    {X Z U : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{max v (u + 1)} A)) :
    Epi ((rawAdj A i).unit.app F) := by
  have hc := isIso_closedCounit_of_isAffine A i
  have : IsIso (rawAdj A i).counit := hc
  have hunit : IsIso ((rawPull A i).map ((rawAdj A i).unit.app F)) := by
    have h := (rawAdj A i).left_triangle_components F
    rw [← IsIso.inv_eq_of_inv_hom_id h]
    infer_instance
  apply Preadditive.epi_of_cancel_zero
  intro G φ hφ
  let Y : Bool → Scheme.{u} := fun b ↦ bif b then Z else U
  let g : ∀ b, Y b ⟶ X := fun b ↦ match b with | true => i | false => j
  have : ∀ b, QuasiCompact (g b) := by
    rintro (_ | _) <;> dsimp [g] <;> infer_instance
  refine rawDetectMaps A g (fun x ↦ ?_) φ ?_
  · by_cases hx : x ∈ Set.range i.base
    · exact ⟨true, hx⟩
    · exact ⟨false, hU ▸ hx⟩
  · rintro (_ | _)
    · exact (rawOpenZero A i j hU _).eq_of_src _ _
    · change (rawPull A i).map φ = 0
      apply (cancel_epi ((rawPull A i).map ((rawAdj A i).unit.app F))).mp
      rw [← Functor.map_comp, hφ, Functor.map_zero, comp_zero]

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The canonical inverse/direct-image unit of a closed immersion is epic.
Source: Stacks Project, Tag 09AH, lemma-ses-associated-to-open, and Tag 09BK,
lemma-closed-immersion-affines
(auxiliary; not a blueprint node).

Proof: work first on the original sites with modules in the independent coefficient
universe. On affine pro-etale bases the closed-site adjunction has invertible unit,
so presheaf precomposition and then sheaf direct image are fully faithful. An affine
closed immersion is isomorphic to a quotient immersion; hence its sheaf counit is
invertible. The closed pullback of the unit is therefore invertible by a triangle
identity. Its target restricts to zero on the complementary open, since sections
there are evaluated on empty fibre products. The closed and open restrictions
jointly detect zero morphisms: local injectivity of sheafification and filtered
module colimits turn vanishing inverse images into local vanishing, and the finite
quasi-compact jointly surjective family combines these neighborhoods into a cover.
Thus any morphism killed by precomposition with the unit is zero, proving it epic.
Transport the adjunction through the two AsSmall sheaf equivalences. Uniqueness
of left adjoints, with its unit identity, identifies its epic unit with the displayed
canonical unit up to an invertible factor. No size bound on A, nonempty scheme,
reducedness, or splitting of the closed immersion is used. -/
theorem coefficientFixed_closed_unit_epi
    (A : Type (max v (u + 1))) [CommRing A]
    {X Z U : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)) :
    Epi (C := Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
      ((coefficientFixedCanonicalAdj.{u, v} A i).unit.app F)  := by
  let EX := (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).sheafCongr
    (ProEt.topology X) (coefficientProEtaleModelTopology.{u, v} X)
    (ModuleCat.{max v (u + 1)} A)
  let EZ := (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Z.ProEt)).sheafCongr
    (ProEt.topology Z) (coefficientProEtaleModelTopology.{u, v} Z)
    (ModuleCat.{max v (u + 1)} A)
  let a₀ := EX.symm.toAdjunction.comp ((rawAdj A i).comp EZ.toAdjunction)
  let eR : EZ.inverse ⋙ rawPush A i ⋙ EX.functor ≅
      (coefficientProEtaleModelBaseChange.{u, v} i).sheafPushforwardContinuous
        (ModuleCat.{max v (u + 1)} A)
        (coefficientProEtaleModelTopology.{u, v} X)
        (coefficientProEtaleModelTopology.{u, v} Z) := Iso.refl _
  let a := a₀.ofNatIsoRight eR
  have : Epi (a₀.unit.app F) := by
    have := rawUnitEpi A i j hU (EX.inverse.obj F)
    have hpreserve : EX.functor.PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction EX.toAdjunction
    have hEZ : IsIso (EZ.toAdjunction.unit.app ((rawPull A i).obj
        (EX.inverse.obj F))) := by
      change IsIso (EZ.unitIso.hom.app _)
      infer_instance
    have hEX : IsIso (EX.symm.toAdjunction.unit.app F) := by
      change IsIso (EX.symm.unitIso.hom.app F)
      infer_instance
    have hinner : Epi ((rawAdj A i).unit.app (EX.inverse.obj F) ≫
        (rawPush A i).map (EZ.toAdjunction.unit.app
          ((rawPull A i).obj (EX.inverse.obj F)))) := by infer_instance
    have hmap : Epi (EX.functor.map ((rawAdj A i).unit.app (EX.inverse.obj F) ≫
        (rawPush A i).map (EZ.toAdjunction.unit.app
          ((rawPull A i).obj (EX.inverse.obj F))))) := by
      exact hpreserve.preserves _
    simp only [a₀, Adjunction.comp_unit_app]
    exact (epi_comp_iff_of_epi _ _).2 hmap
  have : Epi (a.unit.app F) := by
    change Epi (a₀.unit.app F ≫ eR.hom.app _)
    infer_instance
  rw [← Adjunction.unit_leftAdjointUniq_hom_app a
    (coefficientFixedCanonicalAdj.{u, v} A i) F]
  infer_instance

end AlgebraicGeometry.ProEtale
