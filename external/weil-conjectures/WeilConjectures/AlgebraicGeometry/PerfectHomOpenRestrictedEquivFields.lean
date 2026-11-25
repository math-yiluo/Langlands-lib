/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PerfectHomPushPullCocone
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.RelativeMVInverseOpenIso

/-! # Restricted representing Hom equivalences

Source: Stacks Project, Tags 079W and 08FE.
(blueprint: new-perfect-hom-open-restricted-equiv-fields).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section
/-- The Hom equivalence and testing-object naturality fields needed before the
transition and cocone maps are assembled. Source: Stacks Project, Tags 079W and
08FE; perfect.tex, Tag 09RE. (blueprint: new-perfect-hom-open-restricted-equiv-fields). -/
structure PerfectHomOpenRestrictedEquivFields
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F) where
  stageEquiv : ∀ (j : Set.Ici i) (M : schemeDerivedCategory B.toScheme),
    (M ⟶ (F ⋙ schemeMVDerivedRestriction Y B).obj j) ≃
      ((derivedPullback (pullback.fst (B.ι ≫ s)
        (Spec.map (R.map (homOfLE j.property))))).obj M ⟶
       (derivedPullback (pullback.fst (B.ι ≫ s)
        (Spec.map (R.map (homOfLE j.property))))).obj
          ((schemeMVDerivedRestriction Y B).obj Q))
  limitEquiv : ∀ (M : schemeDerivedCategory B.toScheme),
    (M ⟶ (schemeMVDerivedRestriction Y B).obj d.pt) ≃
      ((derivedPullback (pullback.fst (B.ι ≫ s) (Spec.map (c.ι.app i)))).obj M ⟶
       (derivedPullback (pullback.fst (B.ι ≫ s) (Spec.map (c.ι.app i)))).obj
         ((schemeMVDerivedRestriction Y B).obj Q))
  stageNatural : ∀ (j : Set.Ici i) (M N : schemeDerivedCategory B.toScheme)
    (g : M ⟶ N) (f : N ⟶ (F ⋙ schemeMVDerivedRestriction Y B).obj j),
    stageEquiv j M (g ≫ f) =
      (derivedPullback (pullback.fst (B.ι ≫ s) (Spec.map (R.map (homOfLE j.property))))).map g ≫
        stageEquiv j N f
  limitNatural : ∀ (M N : schemeDerivedCategory B.toScheme)
    (g : M ⟶ N) (f : N ⟶ (schemeMVDerivedRestriction Y B).obj d.pt),
    limitEquiv M (g ≫ f) =
      (derivedPullback (pullback.fst (B.ι ≫ s) (Spec.map (c.ι.app i)))).map g ≫ limitEquiv N f

/-- Yoneda identifies an object representing the pullback Hom functor with push-pull. -/
private def representingIso {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {G : D ⥤ C} (a : L ⊣ G) (P Q : C)
    (e : ∀ M : C, (M ⟶ P) ≃ (L.obj M ⟶ L.obj Q))
    (hn : ∀ (M N : C) (g : M ⟶ N) (f : N ⟶ P),
      e M (g ≫ f) = L.map g ≫ e N f) : P ≅ G.obj (L.obj Q) := by
  let ee (M : C) := (e M).trans (a.homEquiv M (L.obj Q))
  exact Yoneda.fullyFaithful.preimageIso
    (NatIso.ofComponents (fun M ↦ (ee M.unop).toIso) (by
      intro M N g
      ext f
      exact (congrArg (a.homEquiv N.unop (L.obj Q))
        (hn N.unop M.unop g.unop f)).trans
          (a.homEquiv_naturality_left g.unop (e M.unop f))))

/-- Open restriction of push-pull, transported to the chosen base-change pullback. -/
private def openPushPullIso {S T Y : Scheme.{u}} (s : Y ⟶ S) (t : T ⟶ S)
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (Q : schemeDerivedCategory Y) :
    (schemeMVDerivedRestriction Y B).obj
        ((schemeDerivedDirectImage (pullback.fst s t)).obj
          ((derivedPullback (pullback.fst s t)).obj Q)) ≅
      (schemeDerivedDirectImage (pullback.fst (B.ι ≫ s) t)).obj
        ((derivedPullback (pullback.fst (B.ι ≫ s) t)).obj
          ((schemeMVDerivedRestriction Y B).obj Q)) := by
  let π := pullback.fst s t
  let hp := (isPullback_morphismRestrict π B).paste_vert (IsPullback.of_hasPullback s t)
  let e := hp.isoPullback.symm
  exact (schemeMVOpenRestrictionComparison π B).app ((derivedPullback π).obj Q) ≪≫
    (schemeDerivedDirectImage (π ∣_ B)).mapIso
      (by simpa only [Scheme.Hom.resLE_eq_morphismRestrict, Functor.comp_obj,
        schemeMVDerivedRestriction] using
        (mvPullbackOpenRestrictionIso π B).app Q) ≪≫
    relativeMVIsoOpenTransport e (π ∣_ B) (pullback.fst (B.ι ≫ s) t)
      (by simp [e]) ((schemeMVDerivedRestriction Y B).obj Q)

/-- Restrict a representing object and transpose the transported Hom equivalence. -/
private theorem restrictedHomEquiv {S T Y : Scheme.{u}} (s : Y ⟶ S) (t : T ⟶ S)
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (P Q : schemeDerivedCategory Y)
    (e : ∀ M : schemeDerivedCategory Y, (M ⟶ P) ≃
      ((derivedPullback (pullback.fst s t)).obj M ⟶
        (derivedPullback (pullback.fst s t)).obj Q))
    (hn : ∀ (M N : schemeDerivedCategory Y) (g : M ⟶ N) (f : N ⟶ P),
      e M (g ≫ f) = (derivedPullback (pullback.fst s t)).map g ≫ e N f) :
    ∃ eb : ∀ M : schemeDerivedCategory B.toScheme,
      (M ⟶ (schemeMVDerivedRestriction Y B).obj P) ≃
        ((derivedPullback (pullback.fst (B.ι ≫ s) t)).obj M ⟶
          (derivedPullback (pullback.fst (B.ι ≫ s) t)).obj
            ((schemeMVDerivedRestriction Y B).obj Q)),
      ∀ (M N : schemeDerivedCategory B.toScheme) (g : M ⟶ N)
        (f : N ⟶ (schemeMVDerivedRestriction Y B).obj P),
        eb M (g ≫ f) = (derivedPullback (pullback.fst (B.ι ≫ s) t)).map g ≫ eb N f := by
  let a := relativeMVAdj (pullback.fst s t)
  let ab := relativeMVAdj (pullback.fst (B.ι ≫ s) t)
  let k := (schemeMVDerivedRestriction Y B).mapIso (representingIso a P Q e hn) ≪≫
    openPushPullIso s t B Q
  refine ⟨fun M ↦ k.homToEquiv.trans (ab.homEquiv M _).symm, ?_⟩
  intro M N g f
  change (ab.homEquiv M _).symm ((g ≫ f) ≫ k.hom) =
    (derivedPullback (pullback.fst (B.ι ≫ s) t)).map g ≫
      (ab.homEquiv N _).symm (f ≫ k.hom)
  rw [Category.assoc]
  exact ab.homEquiv_naturality_left_symm g (f ≫ k.hom)

/-- Existence of the restricted Hom equivalence fields.

Proof: Compose each supplied Hom equivalence with the global pullback adjunction.
Its naturality gives an isomorphism of Yoneda functors, hence an isomorphism from
its representing object to the derived push-pull object. Restrict this isomorphism
to B. The direct-image open comparison and the pullback open comparison identify
its target with push-pull for the restricted projection. Paste the open pullback
square with the original base-change square and use its projection-preserving
isomorphism to transport to the chosen pullback of B.ι followed by s. Postcompose
Hom with this object isomorphism, then apply the restricted projection adjunction
in reverse. Associativity and left naturality of that adjunction prove naturality
in the testing object. Apply this construction to every stage and to the apex and
assemble the four fields. No perfectness or quasi-coherence argument is required;
the same comparisons apply to empty opens and zero objects.
Source: Stacks Project, Tags 079W and 08FE.
(blueprint: new-perfect-hom-open-restricted-equiv-fields). -/
theorem perfect_hom_open_restricted_equiv_fields_exists
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) :
    Nonempty (PerfectHomOpenRestrictedEquivFields R c s B Q F d) := by
  classical
  have hs (j : Set.Ici i) := restrictedHomEquiv s
    (Spec.map (R.map (homOfLE j.property))) B (F.obj j) Q
      (h.stageEquiv j) (h.stageNatural j)
  obtain ⟨el, hnl⟩ := restrictedHomEquiv s (Spec.map (c.ι.app i)) B d.pt Q
    h.limitEquiv h.limitNatural
  exact ⟨{
    stageEquiv := fun j ↦ (hs j).choose
    limitEquiv := el
    stageNatural := fun j ↦ (hs j).choose_spec
    limitNatural := hnl }⟩
end
end AlgebraicGeometry
