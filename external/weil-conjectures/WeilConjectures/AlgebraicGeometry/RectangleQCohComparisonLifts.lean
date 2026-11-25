/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Restriction of canonical rectangle comparisons -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- The fixed rectangle interface names U and V although this comparison does not use them.
/-- Canonical ordinary rectangle comparisons on the quasi-coherent subcategories.
Source: Stacks Project, Tags 0D5S (pullback composition), 0ATM (pasting), and
08HY (adjunctions defining the mate).
(blueprint: lem-sc-rectangle-qcoh-comparison-lifts)

Proof: The two projection equations identify k with pullbackLeftPullbackSndIso.hom,
by the uniqueness clause for the outer pullback. Pullback along k is an equivalence:
its inverse is pullback along the inverse scheme isomorphism, with unit and counit
obtained from the pinned composition and identity comparisons. Consequently the
unit of the pinned adjunction for k is invertible. Conjugate c(k,q) followed by the
transport along hk₂ under the pinned adjunctions for q, k, and the iterated second
projection; this is d. Whisker d with pullback along k and cancel the invertible
unit to obtain an ambient isomorphism from that pullback followed by the iterated
direct image to the outer direct image. Its inverse component is exactly the
first displayed formula. Both end functors preserve quasi-coherent objects, so
full faithfulness of the QCoh inclusion lifts this isomorphism uniquely to p.
Likewise lift c(h,g).symm to b. Faithfulness gives the second component formula.
No base-change map is assumed invertible here. Empty schemes and identity maps
satisfy the same universal-property and adjunction calculations. -/
theorem rectangle_qcoh_comparison_lifts
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (g : S ⟶ Y) (h : T ⟶ S)
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let L := qcPullback k
    let P := @qcDirectImage _ _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _
      (pullback.snd f (h ≫ g))
    let Q := @qcDirectImage _ _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)) _ _
      (pullback.snd (pullback.snd f g) h)
    let B := qcPullback (h ≫ g)
    let H := qcPullback g ⋙ qcPullback h
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let a := fun {A B : Scheme} (r : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction r
        (hAdd := (Classical.choose exists_derivedPullbackComposition) r)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) r)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) r))
    let d := conjugateIsoEquiv (a (pullback.snd (pullback.snd f g) h))
      ((a (pullback.snd f (h ≫ g))).comp (a k))
      (c k (pullback.snd f (h ≫ g)) ≪≫
        eqToIso (congrArg (fun r ↦ derivedPullback.{u, w} r) hk₂))
    ∃ (p : L ⋙ Q ≅ P) (b : B ≅ H),
      (∀ D : schemeDerivedQCohCategory (pullback f (h ≫ g)),
        (schemeDerivedQCohProperty T).ι.map (p.inv.app D) =
          (schemeDerivedDirectImage (pullback.snd f (h ≫ g))).map
            ((a k).unit.app D.obj) ≫ d.inv.app ((derivedPullback k).obj D.obj)) ∧
      (∀ D : schemeDerivedQCohCategory Y,
        (schemeDerivedQCohProperty T).ι.map (b.hom.app D) = (c h g).inv.app D.obj) := by
  classical
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
  let a := fun {A B : Scheme.{u}} (r : A ⟶ B) ↦
    Classical.choose (exists_schemeDerivedAdjunction r
      (hAdd := (Classical.choose exists_derivedPullbackComposition) r)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) r)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) r))
  let d := conjugateIsoEquiv (a (pullback.snd (pullback.snd f g) h))
    ((a (pullback.snd f (h ≫ g))).comp (a k))
    (c k (pullback.snd f (h ≫ g)) ≪≫
      eqToIso (congrArg (fun r ↦ derivedPullback.{u, w} r) hk₂))
  have hk : k = (pullbackLeftPullbackSndIso f g h).hom := by
    apply pullback.hom_ext
    · exact hk₁.trans (pullbackLeftPullbackSndIso_hom_fst f g h).symm
    · exact hk₂.trans (pullbackLeftPullbackSndIso_hom_snd f g h).symm
  have : IsIso k := by rw [hk]; infer_instance
  let i : ∀ Z : Scheme.{u}, derivedPullback (𝟙 Z) ≅ 𝟭 _ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).2
  let e := asIso k
  let ev : schemeDerivedCategory (pullback f (h ≫ g)) ≌
      schemeDerivedCategory (pullback (pullback.snd f g) h) :=
    CategoryTheory.Equivalence.mk (derivedPullback k) (derivedPullback e.inv)
    (c e.inv k ≪≫ eqToIso (congrArg (fun r ↦ derivedPullback r) e.inv_hom_id) ≪≫
      i _).symm
    (c k e.inv ≪≫ eqToIso (congrArg (fun r ↦ derivedPullback r) e.hom_inv_id) ≪≫ i _)
  have : (derivedPullback k).IsEquivalence := ev.isEquivalence_functor
  have : IsIso (a k).unit := (a k).unit_isIso_of_L_fully_faithful
  let P₀ := schemeDerivedDirectImage (pullback.snd f (h ≫ g))
  let Q₀ := schemeDerivedDirectImage (pullback.snd (pullback.snd f g) h)
  let t : P₀ ≅ derivedPullback k ⋙ Q₀ :=
    (Functor.leftUnitor P₀).symm ≪≫
      Functor.isoWhiskerRight (asIso (a k).unit) P₀ ≪≫
      Functor.associator (derivedPullback k) (schemeDerivedDirectImage k) P₀ ≪≫
      Functor.isoWhiskerLeft (derivedPullback k) d.symm
  let P := @qcDirectImage _ _ _ _
    (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _
    (pullback.snd f (h ≫ g))
  let Q := @qcDirectImage _ _ _ _
    (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)) _ _
    (pullback.snd (pullback.snd f g) h)
  let p : qcPullback k ⋙ Q ≅ P :=
    NatIso.ofComponents
      (fun D ↦ (schemeDerivedQCohProperty T).isoMk (t.app D.obj).symm)
      (fun {D E} φ ↦ by
        ext
        exact t.inv.naturality φ.hom)
  let b : qcPullback (h ≫ g) ≅ qcPullback g ⋙ qcPullback h :=
    NatIso.ofComponents
      (fun D ↦ (schemeDerivedQCohProperty T).isoMk ((c h g).app D.obj).symm)
      (fun {D E} φ ↦ by
        ext
        exact (c h g).inv.naturality φ.hom)
  refine ⟨p, b, ?_, ?_⟩
  · intro D
    change t.hom.app D.obj = _
    simp only [t, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Iso.symm_hom, asIso_hom, Functor.leftUnitor_inv_app,
      Functor.associator_hom_app, Category.id_comp]
    rfl
  · intro D
    rfl

end AlgebraicGeometry
