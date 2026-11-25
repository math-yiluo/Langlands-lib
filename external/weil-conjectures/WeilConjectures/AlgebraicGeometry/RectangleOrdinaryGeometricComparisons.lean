/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
import WeilConjectures.AlgebraicGeometry.RectangleOrdinaryGeometricPullback
import WeilConjectures.AlgebraicGeometry.RectangleOrdinaryGeometricDirect

/-! # Ordinary pasting comparisons for the iterated pullback

Source: Stacks Project, Tag 0ATR, Lemma 48.5.2.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

/-- Geometric comparisons for the ordinary rectangle, before introducing right adjoints.
Source: Stacks Project, Tags 0ATR, 08HY, 0ATM and 0D5S.
(blueprint: lem-sc-rectangle-ordinary-geometric-comparisons)

Proof: The pullback universal property identifies k with the canonical iterated
pullback isomorphism. Derived pullback along this isomorphism is an equivalence,
and restriction to the full quasi-coherent subcategories remains an equivalence.
Restrict the fixed derived pullback composition comparisons, using hk₁, to obtain
s, with exactly the displayed ambient component; the base comparison gives b.
The derived direct image composition comparison, the adjunction equivalence for k,
and hk₂ give p. Transpose the ordinary rectangle and the paste under the fixed
pullback/direct image adjunctions. The counit definition of ordinary base change
and associativity of the canonical pullback comparisons identify their transposes.
Injectivity of the adjunction Hom equivalence proves ordinary pasting. Invert the
three base change isomorphisms and use naturality to move p and b, giving the
stated inverse-square equality. This proof is valid for empty schemes and zero
complexes, since all steps are functorial identities or universal properties. -/
theorem rectangle_ordinary_geometric_comparisons
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (g : S ⟶ Y) (h : T ⟶ S)
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
    ∃ (s : U ⋙ L ≅ V) (p : L ⋙ Q ≅ P) (b : B ≅ H),
      L.IsEquivalence ∧
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
  intro U L V P Q B H α δ
  have hpull := rectangle_ordinary_geometric_pullback.{u, w} f g h k hk₁ hk₂
  rcases hpull with ⟨s, hL, hs⟩
  have hdir := rectangle_ordinary_geometric_direct.{u, w}
    (X := X) (Y := Y) (S := S) (T := T) f g h hβ hβS hβI k hk₁ hk₂ s hL hs
  rcases hdir with ⟨p, b, hp⟩
  exact ⟨s, p, b, hL, hp, hs⟩

end AlgebraicGeometry
