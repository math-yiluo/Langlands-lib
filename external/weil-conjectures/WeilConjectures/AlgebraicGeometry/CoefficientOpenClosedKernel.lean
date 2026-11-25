/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientFixedClosedUnitEpi
public import WeilConjectures.AlgebraicGeometry.CoefficientOpenExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # The open term as a kernel on coefficient-sized sites

Source: Stacks Project, Tag 09AH, lemma-ses-associated-to-open.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance modelDownEquiv (X : Scheme.{u}) :
    (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).IsEquivalence :=
  (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_inverse

attribute [local instance] modelDownEquiv

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance modelDownDense (X : Scheme.{u}) :
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).inverse.IsDenseSubsite
      (coefficientProEtaleModelTopology.{u, v} X) (ProEt.topology X) := by
  change (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).IsDenseSubsite
    ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).inducedTopology
      (ProEt.topology X)) (ProEt.topology X)
  infer_instance

attribute [local instance] modelDownDense

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance rawSheafify (A : Type (max v (u + 1))) [CommRing A]
    (X : Scheme.{u}) : HasSheafify (ProEt.topology X) (ModuleCat.{max v (u + 1)} A) := by
  have : HasSheafify (coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A) :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let e := AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)
  exact e.hasSheafify (ProEt.topology X)
    (coefficientProEtaleModelTopology.{u, v} X) (ModuleCat.{max v (u + 1)} A)

attribute [local instance] rawSheafify

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance rawKan (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) (F : X.ProEtᵒᵖ ⥤ ModuleCat.{max v (u + 1)} A) :
    (proEtaleBaseChange i).op.HasPointwiseLeftKanExtension F := by
  intro Y
  have : HasColimitsOfShape (CostructuredArrow (proEtaleBaseChange i).op Y)
      (ModuleCat.{max v (u + 1)} A) :=
    hasColimitsOfShape_of_essentiallySmall.{max v (u + 1)} _ _
  infer_instance

attribute [local instance] rawKan

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private abbrev rawPush (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) :=
  (proEtaleBaseChange i).sheafPushforwardContinuous (ModuleCat.{max v (u + 1)} A)
    (ProEt.topology X) (ProEt.topology Z)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private abbrev rawPull (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (proEtaleBaseChange i) (ModuleCat.{max v (u + 1)} A)
    (ProEt.topology X) (ProEt.topology Z)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private def rawAdj (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) : rawPull A i ⊣ rawPush A i :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleBaseChange i) (ModuleCat.{max v (u + 1)} A)
    (ProEt.topology X) (ProEt.topology Z)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance rawPushAdditive (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) : (rawPush A i).Additive where

attribute [local instance] rawPushAdditive

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance rawW (A : Type (max v (u + 1))) [CommRing A] (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{max v (u + 1)} A) := by
  let G : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt := AsSmall.down
  have : (coefficientProEtaleModelTopology.{u, v} X).WEqualsLocallyBijective
      (ModuleCat.{max v (u + 1)} A) := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.transport
    (ProEt.topology X) (coefficientProEtaleModelTopology.{u, v} X)
    G (Functor.IsDenseSubsite.coverPreserving _ _ _)

attribute [local instance] rawW

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance rawPullAdditive (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) : (rawPull A i).Additive :=
  (rawAdj A i).left_adjoint_additive

attribute [local instance] rawPullAdditive

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private def rawPushComp (A : Type (max v (u + 1))) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rawPush A f ⋙ rawPush A g ≅ rawPush A (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm)
    (ModuleCat.{max v (u + 1)} A) (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private def rawPushCongr (A : Type (max v (u + 1))) [CommRing A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) : rawPush A f ≅ rawPush A g :=
  Functor.sheafPushforwardContinuousIso
    (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) h)
    (ModuleCat.{max v (u + 1)} A) (ProEt.topology Y) (ProEt.topology X)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private def rawPushId (A : Type (max v (u + 1))) [CommRing A] (X : Scheme.{u}) :
    rawPush A (𝟙 X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X)
    (ModuleCat.{max v (u + 1)} A) (ProEt.topology X)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance rawPushIso (A : Type (max v (u + 1))) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : (rawPush A f).IsEquivalence := by
  let e := asIso f
  let E := CategoryTheory.Equivalence.mk (rawPush A e.hom) (rawPush A e.inv)
    ((rawPushId A X).symm ≪≫ rawPushCongr A e.hom_inv_id.symm ≪≫
      (rawPushComp A e.hom e.inv).symm)
    (rawPushComp A e.inv e.hom ≪≫ rawPushCongr A e.inv_hom_id ≪≫ rawPushId A Y)
  exact E.isEquivalence_functor

attribute [local instance] rawPushIso

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
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

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
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

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
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

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
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

attribute [local instance] rawPreservesFiltered

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
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

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
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

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
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

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
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

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance rawPullZero (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) : (rawPull A i).PreservesZeroMorphisms := by
  have := rawPullAdditive.{u, v} A i
  infer_instance

attribute [local instance] rawPullZero

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance rawAbelian (A : Type (max v (u + 1))) [CommRing A] (X : Scheme.{u}) :
    Abelian (Sheaf (ProEt.topology X) (ModuleCat.{max v (u + 1)} A)) := by
  haveI := rawSheafify.{u, v} A X
  infer_instance

attribute [local instance] rawAbelian

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance rawPullFiniteLimits (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) : PreservesFiniteLimits (rawPull A i) := by
  have : RepresentablyFlat (proEtaleBaseChange i) := flat_of_preservesFiniteLimits _
  have : AB5OfSize.{u, u + 1} (ModuleCat.{max v (u + 1)} A) :=
    AB5OfSize_shrink.{u, u + 1, max v (u + 1), max v (u + 1)} _
  have : PreservesFiniteLimits
      ((proEtaleBaseChange i).op.lan :
        (X.ProEtᵒᵖ ⥤ ModuleCat.{max v (u + 1)} A) ⥤
          (Z.ProEtᵒᵖ ⥤ ModuleCat.{max v (u + 1)} A)) := by
    exact preservesFiniteLimits_op_lan_of_flat _
  unfold rawPull Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

attribute [local instance] rawPullFiniteLimits

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance rawPullFiniteColimits (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) : PreservesFiniteColimits (rawPull A i) := by
  have : (rawPull A i).IsLeftAdjoint := (rawAdj A i).isLeftAdjoint
  infer_instance

attribute [local instance] rawPullFiniteColimits

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private instance rawExtKan (A : Type (max v (u + 1))) [CommRing A]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : U.ProEtᵒᵖ ⥤ ModuleCat.{max v (u + 1)} A) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.HasPointwiseLeftKanExtension
      F := by
  intro Y
  have : HasColimitsOfShape
      (CostructuredArrow (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op Y)
      (ModuleCat.{max v (u + 1)} A) :=
    hasColimitsOfShape_of_essentiallySmall.{max v (u + 1)} _ _
  infer_instance

attribute [local instance] rawExtKan

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private abbrev rawExt (A : Type (max v (u + 1))) [CommRing A]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  haveI := rawSheafify.{u, v} A X
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j))
    (ModuleCat.{max v (u + 1)} A) (ProEt.topology U) (ProEt.topology X)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private abbrev rawRes (A : Type (max v (u + 1))) [CommRing A]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).sheafPushforwardContinuous
    (ModuleCat.{max v (u + 1)} A) (ProEt.topology U) (ProEt.topology X)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private def rawExtAdj (A : Type (max v (u + 1))) [CommRing A]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : rawExt A j ⊣ rawRes A j :=
  haveI := rawSheafify.{u, v} A X
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j))
    (ModuleCat.{max v (u + 1)} A) (ProEt.topology U) (ProEt.topology X)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private def rawResAdj (A : Type (max v (u + 1))) [CommRing A]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : rawRes A j ⊣ rawPush A j :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial).sheafPushforwardContinuous
      (E := ModuleCat.{max v (u + 1)} A) (ProEt.topology U) (ProEt.topology X)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private def rawOpenAdj (A : Type (max v (u + 1))) [CommRing A]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : rawExt A j ⊣ rawPull A j :=
  (rawExtAdj A j).ofNatIsoRight ((rawAdj A j).leftAdjointUniq (rawResAdj A j)).symm

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private lemma rawOpenUnit (A : Type (max v (u + 1))) [CommRing A]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : IsIso (rawOpenAdj A j).unit := by
  have hc : IsIso (rawResAdj A j).counit :=
    Adjunction.isIso_sheafPushforwardContinuous_counit (ModuleCat.{max v (u + 1)} A)
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial)
      (ProEt.topology U) (ProEt.topology X)
  let t : Adjunction.Triple (rawExt A j) (rawRes A j) (rawPush A j) :=
    ⟨rawExtAdj A j, rawResAdj A j⟩
  have : IsIso (rawExtAdj A j).unit := t.isIso_unit_iff_isIso_counit.mpr hc
  change IsIso ((rawExtAdj A j).unit ≫
    Functor.whiskerLeft (rawExt A j) ((rawAdj A j).leftAdjointUniq (rawResAdj A j)).inv)
  infer_instance

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private lemma rawDetectZero (A : Type (max v (u + 1))) [CommRing A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{max v (u + 1)} A))
    (hi : IsZero ((rawPull A i).obj F)) (hj : IsZero ((rawPull A j).obj F)) :
    IsZero F := by
  let Y : Bool → Scheme.{u} := fun b ↦ bif b then Z else U
  let g : ∀ b, Y b ⟶ X := fun b ↦ match b with | true => i | false => j
  have : ∀ b, QuasiCompact (g b) := by
    rintro (_ | _) <;> dsimp [g] <;> infer_instance
  refine (IsZero.iff_id_eq_zero F).2 (rawDetectMaps A g (fun x ↦ ?_) (𝟙 F) ?_)
  · by_cases hx : x ∈ Set.range i.base
    · exact ⟨true, hx⟩
    · exact ⟨false, hU ▸ hx⟩
  · rintro (_ | _)
    · exact hj.eq_of_src _ _
    · exact hi.eq_of_src _ _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
/-- Exactness of a short complex can be detected by two exact functors which jointly
    detect zero objects. This packages the kernel, cokernel and homology argument without
    unfolding the concrete sheaf pullbacks during elaboration. -/
private lemma shortExact_of_joint_detection
    {C : Type*} {D E : Type w} [Category C] [Category.{w'} D] [Category.{w'} E]
    [Abelian C] [Abelian D] [Abelian E]
    (P : C ⥤ D) (Q : C ⥤ E) [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (h : ∀ M : C, IsZero (P.obj M) → IsZero (Q.obj M) → IsZero M)
    (S : ShortComplex C) (hp : (S.map P).ShortExact) (hq : (S.map Q).ShortExact) :
    S.ShortExact := by
  have hker {B : Type w} [Category.{w'} B] [Abelian B]
      (T : C ⥤ B) [T.Additive] [PreservesFiniteLimits T]
      (ht : (S.map T).ShortExact) : IsZero (T.obj (kernel S.f)) := by
    have : Mono (T.map S.f) := ht.mono_f
    exact (isZero_kernel_of_mono (T.map S.f)).of_iso (PreservesKernel.iso T S.f)
  have hcoker {B : Type w} [Category.{w'} B] [Abelian B]
      (T : C ⥤ B) [T.Additive] [PreservesFiniteColimits T]
      (ht : (S.map T).ShortExact) : IsZero (T.obj (cokernel S.g)) := by
    have : Epi (T.map S.g) := ht.epi_g
    exact (isZero_cokernel_of_epi (T.map S.g)).of_iso (PreservesCokernel.iso T S.g)
  have hhom {B : Type w} [Category.{w'} B] [Abelian B]
      (T : C ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
      (ht : (S.map T).ShortExact) : IsZero (T.obj S.homology) :=
    ((S.map T).exact_iff_isZero_homology.1 ht.exact).of_iso (S.mapHomologyIso T).symm
  have : Mono S.f := Preadditive.mono_of_isZero_kernel _
    (h _ (hker P hp) (hker Q hq))
  have : Epi S.g := Preadditive.epi_of_isZero_cokernel _
    (h _ (hcoker P hp) (hcoker Q hq))
  exact ⟨S.exact_iff_isZero_homology.2 (h _ (hhom P hp) (hhom Q hq))⟩

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
private lemma rawShortExact (A : Type (max v (u + 1))) [CommRing A]
    {X Z U : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{max v (u + 1)} A)) :
    ∃ hz : (rawOpenAdj A j).counit.app F ≫ (rawAdj A i).unit.app F = 0,
      (ShortComplex.mk ((rawOpenAdj A j).counit.app F)
        ((rawAdj A i).unit.app F) hz).ShortExact := by
  let (Y : Scheme.{u}) := rawAbelian.{u, v} A Y
  let {Y : Scheme.{u}} (g : Y ⟶ X) := rawPullZero.{u, v} A g
  let a := rawOpenAdj A j
  let b := rawAdj A i
  have hz (M : Sheaf (ProEt.topology Z) (ModuleCat.{max v (u + 1)} A)) :
      IsZero ((rawPull A j).obj ((rawPush A i).obj M)) := rawOpenZero A i j hU M
  have hzi (M : Sheaf (ProEt.topology U) (ModuleCat.{max v (u + 1)} A)) :
      IsZero ((rawPull A i).obj ((rawExt A j).obj M)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (b.homEquiv _ _).injective
    apply (a.homEquiv _ _).injective
    exact (hz _).eq_of_tgt _ _
  have hzero : a.counit.app F ≫ b.unit.app F = 0 := by
    apply (a.homEquiv _ _).injective
    exact (hz _).eq_of_tgt _ _
  let S := ShortComplex.mk (a.counit.app F) (b.unit.app F) hzero
  have hi : (S.map (rawPull A i)).ShortExact := by
    have : IsIso b.counit := isIso_closedCounit_of_isAffine A i
    have hgi : IsIso ((rawPull A i).map (b.unit.app F)) := by
      have h := b.left_triangle_components F
      rw [← IsIso.inv_eq_of_inv_hom_id h]
      infer_instance
    have : IsIso (S.map (rawPull A i)).g := hgi
    have hf : (S.map (rawPull A i)).f = 0 := (hzi _).eq_of_src _ _
    exact
      { exact := (ShortComplex.exact_iff_mono _ hf).2 inferInstance
        mono_f := ⟨fun _ _ _ ↦ (hzi _).eq_of_tgt _ _⟩
        epi_g := by
          change Epi ((rawPull A i).map (b.unit.app F))
          infer_instance }
  have hj : (S.map (rawPull A j)).ShortExact := by
    have : IsIso a.unit := rawOpenUnit A j
    have hfj : IsIso ((rawPull A j).map (a.counit.app F)) := by
      have h := a.right_triangle_components (Y := F)
      rw [← IsIso.inv_eq_of_hom_inv_id h]
      infer_instance
    have : IsIso (S.map (rawPull A j)).f := hfj
    have hg : (S.map (rawPull A j)).g = 0 := (hz _).eq_of_tgt _ _
    exact
      { exact := (ShortComplex.exact_iff_epi _ hg).2 inferInstance
        mono_f := by
          change Mono ((rawPull A j).map (a.counit.app F))
          infer_instance
        epi_g := ⟨fun _ _ _ ↦ (hz _).eq_of_src _ _⟩ }
  refine ⟨hzero, ?_⟩
  exact shortExact_of_joint_detection (rawPull A i) (rawPull A j)
    (rawDetectZero A i j hU) S hi hj

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology in
/-- The open extension of the open restriction is the kernel of the closed unit.
This assertion concerns arbitrary coefficient-sized module sheaves and does not involve
etale comparison or an etale antecedent.

Source: Stacks Project, Tag 09AH, lemma-ses-associated-to-open
(auxiliary; not a blueprint node).

Proof: identify inverse image along the open immersion with restriction along composition
of site objects. The site-level composition/base-change adjunction induces an adjunction
on sheaves; uniqueness of left adjoints identifies this restriction with the specified
Kan-extension pullback. Thus extension by zero is left adjoint to that pullback.
Its counit has zero composite with the closed unit. Check that this counit is monic and
has image the kernel locally, as in Tag 09AH. On an affine weakly contractible test
object Spec B, the inverse image of Z is cut out by an ideal I. Quasi-compactness of j
provides finitely many functions of I whose distinguished opens cover its complement.
The distinguished opens and the localization of B at elements invertible modulo I
form a pro-etale cover. On a distinguished open the two maps are an isomorphism followed
by a map to zero. On the localization every point specializes into the closed fibre;
extension by zero vanishes there, and the closed unit is an isomorphism. The sequence
is therefore left exact on this covering. The sheaf condition descends monicity and
factorizations of maps killed by the closed unit, giving the kernel universal property.
These local maps preserve the A-action. Transport the covering and all restriction maps
through AsSmall.down and AsSmall.up, which are inverse site equivalences. This does not
shrink coefficients or sections and works for the displayed independent universes.
Uniqueness of kernels gives the isomorphism. If U is empty the open term and the kernel
are zero; if Z is empty the counit identifies the open term with F itself. -/
theorem coefficientOpenClosedKernelIso
    (A : Type (max v (u + 1))) [CommRing A]
    {X Z U : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    [HasKernel (C := Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)) ((coefficientFixedCanonicalAdj.{u, v} A i).unit.app F)] :
    Nonempty
      ((coefficientOpenProEtaleExtension.{u, v} A j).obj
          ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} j A).obj F) ≅
        kernel (C := Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
          (ModuleCat.{max v (u + 1)} A))
          ((coefficientFixedCanonicalAdj.{u, v} A i).unit.app F)) := by
  let (Y : Scheme.{u}) := rawAbelian.{u, v} A Y
  let EX := (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).sheafCongr
    (ProEt.topology X) (coefficientProEtaleModelTopology.{u, v} X)
    (ModuleCat.{max v (u + 1)} A)
  let EZ := (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Z.ProEt)).sheafCongr
    (ProEt.topology Z) (coefficientProEtaleModelTopology.{u, v} Z)
    (ModuleCat.{max v (u + 1)} A)
  let EU := (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := U.ProEt)).sheafCongr
    (ProEt.topology U) (coefficientProEtaleModelTopology.{u, v} U)
    (ModuleCat.{max v (u + 1)} A)
  let Pi := Scheme.coefficientProEtaleFixedModulePullback.{u, v} i A
  let Pj := Scheme.coefficientProEtaleFixedModulePullback.{u, v} j A
  let Ri := (coefficientProEtaleModelBaseChange.{u, v} i).sheafPushforwardContinuous
    (ModuleCat.{max v (u + 1)} A)
    (coefficientProEtaleModelTopology.{u, v} X)
    (coefficientProEtaleModelTopology.{u, v} Z)
  let b₀ := EX.symm.toAdjunction.comp ((rawAdj A i).comp EZ.toAdjunction)
  let bR : EZ.inverse ⋙ rawPush A i ⋙ EX.functor ≅
      (coefficientProEtaleModelBaseChange.{u, v} i).sheafPushforwardContinuous
        (ModuleCat.{max v (u + 1)} A)
        (coefficientProEtaleModelTopology.{u, v} X)
        (coefficientProEtaleModelTopology.{u, v} Z) := Iso.refl _
  let b := b₀.ofNatIsoRight bR
  let bi := coefficientFixedCanonicalAdj.{u, v} A i
  let ei := b.leftAdjointUniq bi
  let c₀ := EX.symm.toAdjunction.comp ((rawAdj A j).comp EU.toAdjunction)
  let cR : EU.inverse ⋙ rawPush A j ⋙ EX.functor ≅
      (coefficientProEtaleModelBaseChange.{u, v} j).sheafPushforwardContinuous
        (ModuleCat.{max v (u + 1)} A)
        (coefficientProEtaleModelTopology.{u, v} X)
        (coefficientProEtaleModelTopology.{u, v} U) := Iso.refl _
  let c := c₀.ofNatIsoRight cR
  let cj := coefficientFixedCanonicalAdj.{u, v} A j
  let ej := c.leftAdjointUniq cj
  let d₀ := EU.symm.toAdjunction.comp ((rawExtAdj A j).comp EX.toAdjunction)
  let dR : EX.inverse ⋙ rawRes A j ⋙ EU.functor ≅
      (coefficientOpenProEtaleMap.{u, v} j).sheafPushforwardContinuous
        (ModuleCat.{max v (u + 1)} A)
        (coefficientProEtaleModelTopology.{u, v} U)
        (coefficientProEtaleModelTopology.{u, v} X) := Iso.refl _
  let d := d₀.ofNatIsoRight dR
  let dj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (coefficientOpenProEtaleMap.{u, v} j) (ModuleCat.{max v (u + 1)} A)
    (coefficientProEtaleModelTopology.{u, v} U)
    (coefficientProEtaleModelTopology.{u, v} X)
  let ed := d.leftAdjointUniq dj
  let F₀ := EX.inverse.obj F
  obtain ⟨hz, hs⟩ := rawShortExact A i j hU F₀
  let ek : (rawExt A j).obj ((rawPull A j).obj F₀) ≅
      kernel ((rawAdj A i).unit.app F₀) :=
    hs.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  let : EX.functor.Additive := { map_add := by intros; rfl }
  let eF : EX.functor.obj F₀ ≅ F := EX.counitIso.app F
  let eT : EX.functor.obj ((rawPush A i).obj ((rawPull A i).obj F₀)) ≅
      Ri.obj (Pi.obj F) :=
    EX.functor.mapIso ((rawPush A i).mapIso
      (EZ.unitIso.app ((rawPull A i).obj F₀))) ≪≫ Ri.mapIso (ei.app F)
  have hu : eF.inv ≫ EX.functor.map ((rawAdj A i).unit.app F₀) ≫ eT.hom =
      bi.unit.app F := by
    rw [← Adjunction.unit_leftAdjointUniq_hom_app b bi F]
    change eF.inv ≫ EX.functor.map ((rawAdj A i).unit.app F₀) ≫ eT.hom =
      (b₀.unit.app F ≫ bR.hom.app _) ≫ Ri.map (ei.hom.app F)
    simp only [b₀, Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
    rfl
  let eK : kernel (EX.functor.map ((rawAdj A i).unit.app F₀)) ≅
      kernel (bi.unit.app F) :=
    kernel.mapIso _ _ eF eT (by rw [← hu]; simp only [Iso.hom_inv_id_assoc])
  let eJ : EU.inverse.obj (Pj.obj F) ≅ (rawPull A j).obj F₀ :=
    (EU.inverse.mapIso (ej.app F)).symm ≪≫
      (EU.unitIso.app ((rawPull A j).obj F₀)).symm
  exact ⟨(ed.app (Pj.obj F)).symm ≪≫
    EX.functor.mapIso ((rawExt A j).mapIso eJ) ≪≫
    EX.functor.mapIso ek ≪≫ PreservesKernel.iso EX.functor _ ≪≫ eK⟩

end AlgebraicGeometry.ProEtale
