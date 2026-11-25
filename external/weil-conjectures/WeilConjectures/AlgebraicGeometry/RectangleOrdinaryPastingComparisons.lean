/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
import WeilConjectures.AlgebraicGeometry.RectangleOrdinaryGeometricComparisons
import WeilConjectures.CategoryTheory.EquivalenceRightAdjointCounitTransport

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

/-- Ordinary horizontal pasting and the adjunction comparisons for the iterated pullback.
Source: Stacks Project, Tag 0ATR, Lemma 48.5.2; Tags 08HY, 0ATM and 0D5S.
(blueprint: lem-sc-rectangle-ordinary-pasting-comparisons)

Proof: The two projection equations identify k with the canonical iterated-pullback
isomorphism, by the pullback universal property. Restrict the canonical pullback
composition comparisons to the full quasi-coherent subcategories. Their composite
with the first projection equation gives s with the displayed component; the base
composition comparison gives b. Pullback along k is an equivalence. Derived
pullback/direct-image adjunctions identify its inverse with direct image along k;
derived direct-image composition and the second projection equation therefore give
p. Transport the adjunction for P along p and this equivalence. Uniqueness of right
adjoints gives t, characterized by the displayed counit equation. Transpose the
ordinary rectangle and the horizontally pasted ordinary square under the pinned
pullback/direct-image adjunctions. The counit formula for base change and the
associativity law for canonical derived pullback composition identify their
transposes. Injectivity of the Hom equivalence gives ordinary pasting. Inverting
the ordinary base-change comparisons gives the displayed identity for alpha and
delta: all three inverses exist by the hypotheses, and naturality moves p and b
through the composites. This argument is entirely at the ordinary-square level:
it uses no right adjoint to the direct image of f and no second mate. The same
identities apply to empty schemes and zero complexes. -/
theorem rectangle_ordinary_pasting_comparisons
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (g : S ⟶ Y) (h : T ⟶ S)
    (c : schemeDerivedQCohCategory T ⥤ schemeDerivedQCohCategory (pullback f (h ≫ g)))
    (d : schemeDerivedQCohCategory T ⥤
      schemeDerivedQCohCategory (pullback (pullback.snd f g) h))
    (adjc : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι ⋙
        schemeDerivedDirectImage (pullback.snd f (h ≫ g)))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _ _ _
        (pullback.snd f (h ≫ g)) _ _).fst E.obj E.property) ⊣ c)
    (adjd : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι ⋙
        schemeDerivedDirectImage (pullback.snd (pullback.snd f g) h))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)) _ _ _ _
        (pullback.snd (pullback.snd f g) h) _ _).fst E.obj E.property) ⊣ d)
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
        (pullback.fst f (h ≫ g)) pullback.condition E.obj))
    (hβS : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj))
    (hβI : ∀ E : schemeDerivedQCohCategory (pullback f g),
      IsIso (schemeDerivedBaseChangeMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h) h
        (pullback.fst (pullback.snd f g) h) pullback.condition E.obj))
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let U := qcPullback (pullback.fst f (h ≫ g))
    let L := qcPullback k
    let V := qcPullback (pullback.fst f g) ⋙
      qcPullback (pullback.fst (pullback.snd f g) h)
    let P := @qcDirectImage _ _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _
      (pullback.snd f (h ≫ g))
    let Q := @qcDirectImage _ _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)) _ _
      (pullback.snd (pullback.snd f g) h)
    let B := qcPullback (h ≫ g)
    let H := qcPullback g ⋙ qcPullback h
    let α := qcInverseBaseChange f (h ≫ g) hβ
    let δ := qcInverseBaseChange f g hβS ≫ₕ
      @qcInverseBaseChange _ (pullback f g) S T _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _ h hβI
    ∃ (s : U ⋙ L ≅ V) (p : L ⋙ Q ≅ P) (b : B ≅ H) (t : c ⋙ L ≅ d),
      (∀ Z : schemeDerivedQCohCategory T,
        Q.map (t.hom.app Z) ≫ adjd.counit.app Z =
          p.hom.app (c.obj Z) ≫ adjc.counit.app Z) ∧
      (∀ E : schemeDerivedQCohCategory X,
        Q.map (s.hom.app E) ≫ δ.app E =
          p.hom.app (U.obj E) ≫ α.app E ≫ b.hom.app ((qcDirectImage f).obj E)) ∧
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
  intro U L V P Q B H α δ
  have geom := rectangle_ordinary_geometric_comparisons.{u, w} f g h hβ hβS hβI k hk₁ hk₂
  dsimp only at geom
  rcases geom with ⟨s, p, b, hL, hα, hs⟩
  let : L.IsEquivalence := hL
  have tr := equivalence_rightAdjoint_counit_transport
    (P := P) (Q := Q) (c := c) (d := d) L adjc adjd p
  rcases tr with ⟨t, ht⟩
  exact ⟨s, p, b, t, ht, hα, hs⟩

end AlgebraicGeometry
