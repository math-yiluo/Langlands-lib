/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Ordinary pasting comparisons for the iterated pullback

Source: Stacks Project, Tag 0ATR, Lemma 48.5.2.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

-- Keep the derived construction folded while restricting its comparisons.

/-- The canonical upper pullback comparison and equivalence for an iterated fiber product.
No quasi-compactness or ordinary base-change invertibility is needed here.
Source: Stacks Project, Tag 0D5S; the pullback universal property.
(blueprint: lem-sc-rectangle-ordinary-geometric-pullback)

Proof: Restrict the pinned derived pullback composition and identity comparisons
through the fully faithful quasi-coherent inclusion. The two projection equations
identify k with pullbackLeftPullbackSndIso.hom by pullback.hom_ext. Pullback along
its inverse is an inverse functor to qcPullback k: composition comparisons,
equality transports for the two inverse identities, and the identity comparison
give its unit and counit isomorphisms. Equivalence.mk supplies the equivalence.
Compose the ambient comparison for k and the outer first projection, the equality
transport for hk₁, and the inverse comparison for the two inner first projections.
Lift this natural isomorphism uniquely through the fully faithful inclusion to s.
The map-preimage identity computes its ambient component, and equality transport
commutes with evaluation. This is the stated three-factor formula. Empty schemes
and zero complexes need no special assumptions; identity maps use the same unit
comparisons. The chosen composition family is pinned by its universal property. -/
theorem rectangle_ordinary_geometric_pullback
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    (f : X ⟶ Y) (g : S ⟶ Y) (h : T ⟶ S)
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let U := qcPullback (pullback.fst f (h ≫ g))
    let L := qcPullback k
    let V := qcPullback (pullback.fst f g) ⋙
      qcPullback (pullback.fst (pullback.snd f g) h)
    ∃ (s : U ⋙ L ≅ V),
      L.IsEquivalence ∧
      (∀ E : schemeDerivedQCohCategory X,
        (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
            (s.hom.app E) =
          (let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
            (Classical.choose_spec exists_derivedPullbackComposition)))
           (comp k (pullback.fst f (h ≫ g))).hom.app E.obj ≫
             eqToHom (congrArg (fun v ↦ (derivedPullback v).obj E.obj) hk₁) ≫
             (comp (pullback.fst (pullback.snd f g) h)
               (pullback.fst f g)).inv.app E.obj)) := by
  classical
  intro U L V
  let c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      derivedPullback.{u, w} b ⋙ derivedPullback.{u, w} a ≅ derivedPullback.{u, w} (a ≫ b) :=
    @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
  let i : ∀ A : Scheme.{u}, derivedPullback.{u, w} (𝟙 A) ≅ 𝟭 _ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).2
  let cc : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      qcPullback.{u, w} b ⋙ qcPullback.{u, w} a ≅ qcPullback.{u, w} (a ≫ b) := fun {A B C} a b ↦
    ((schemeDerivedQCohProperty.{u, w} A).fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (schemeDerivedQCohProperty.{u, w} C).ι (c a b))
  let ii : ∀ A : Scheme.{u}, qcPullback.{u, w} (𝟙 A) ≅ 𝟭 (schemeDerivedQCohCategory.{u, w} A) :=
    fun A ↦ ((schemeDerivedQCohProperty.{u, w} A).fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (schemeDerivedQCohProperty.{u, w} A).ι (i A))
  let e := pullbackLeftPullbackSndIso f g h
  have he : k = e.hom := by
    apply pullback.hom_ext
    · exact hk₁.trans (pullbackLeftPullbackSndIso_hom_fst f g h).symm
    · exact hk₂.trans (pullbackLeftPullbackSndIso_hom_snd f g h).symm
  have hL : L.IsEquivalence := by
    change (qcPullback.{u, w} k).IsEquivalence
    rw [he]
    let ev := CategoryTheory.Equivalence.mk (qcPullback.{u, w} e.hom) (qcPullback.{u, w} e.inv)
      (cc e.inv e.hom ≪≫ eqToIso (congrArg (fun a ↦ qcPullback.{u, w} a) e.inv_hom_id) ≪≫
        ii _).symm
      (cc e.hom e.inv ≪≫ eqToIso (congrArg (fun a ↦ qcPullback.{u, w} a) e.hom_inv_id) ≪≫ ii _)
    exact ev.isEquivalence_functor
  let ambient := c k (pullback.fst f (h ≫ g)) ≪≫
    eqToIso (congrArg (fun a ↦ derivedPullback.{u, w} a) hk₁) ≪≫
      (c (pullback.fst (pullback.snd f g) h) (pullback.fst f g)).symm
  let ff := (schemeDerivedQCohProperty.{u, w}
    (pullback (pullback.snd f g) h)).fullyFaithfulι.whiskeringRight
      (schemeDerivedQCohCategory.{u, w} X)
  let s : U ⋙ L ≅ V := ff.preimageIso
    (Functor.isoWhiskerLeft (schemeDerivedQCohProperty.{u, w} X).ι ambient)
  refine ⟨s, hL, ?_⟩
  intro E
  have hs := congrArg (fun t ↦ t.app E)
    (ff.map_preimage (X := U ⋙ L) (Y := V)
      (Functor.isoWhiskerLeft (schemeDerivedQCohProperty.{u, w} X).ι ambient).hom)
  change (schemeDerivedQCohProperty.{u, w} (pullback (pullback.snd f g) h)).ι.map
    (s.hom.app E) = ambient.hom.app E.obj at hs
  simpa only [ambient, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    eqToIso.hom, eqToHom_app, c] using hs

end AlgebraicGeometry
