/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.RectangleInverseBaseChangeMateTransport

/-! # Right-adjoint mate for two successive base changes

Source: Stacks Project, Duality for Schemes, Tag 0ATR.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- Lifted functors and the two iterated pullbacks require extra definitional-equality checks.
/-- The right-adjoint mate for the rectangle factors through the two square mates
on the genuine iterated pullback. This assertion concerns only successive base
changes, before identifying either pullback with an open restriction.
Source: Stacks Project, Duality for Schemes, Tag 0ATR, Lemma 48.5.2.
(blueprint: lem-sc-right-adjoint-mate-successive-base-change)

Proof: Derived pullback composition and the displayed projection equations give
source comparisons. Derived direct-image composition, and uniqueness of right
adjoints with the unit/counit comparisons, give the middle and target comparisons.
Transpose ordinary base change under the composite pullback/direct-image
adjunction. The counit formula and associativity of pullback composition identify
its transpose with the composite of the square transposes; injectivity of the Hom
equivalence proves ordinary base-change pasting. Expand the second mates as
pullback of the right adjoint of the base unit, inverse conjugate of ordinary base
change, then the upper pullback counit. ConjugateEquiv preserves composition and
inverses. Naturality moves the conjugates past units and counits; the middle unit
and counit cancel by the triangle identities. The remaining factors are the three
comparison isomorphisms and the two square mates in the displayed order. Neither
square mate is inverted. This works for arbitrary qcqs base morphisms and empty
schemes, and does not require flatness or properness. -/
theorem rightAdjoint_mate_successive_baseChange
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (g : S ⟶ Y) (h : T ⟶ S)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (aS : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory (pullback f g))
    (c : schemeDerivedQCohCategory T ⥤ schemeDerivedQCohCategory (pullback f (h ≫ g)))
    (d : schemeDerivedQCohCategory T ⥤
      schemeDerivedQCohCategory (pullback (pullback.snd f g) h))
    (adja : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
        f _ _).fst E.obj E.property) ⊣ a)
    (adjS : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ aS)
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
    (K : schemeDerivedQCohCategory Y)
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let G := Arrow.mk ((derivedPullback k).map
      ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι.map
      (dualityEquationBaseChangeMap f (h ≫ g) a c adja adjc hβ K)))
    let O := Arrow.mk ((derivedPullback (pullback.fst (pullback.snd f g) h)).map
      ((schemeDerivedQCohProperty (pullback f g)).ι.map
      (dualityEquationBaseChangeMap f g a aS adja adjS hβS K)))
    let H := Arrow.mk ((schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
      (@dualityEquationBaseChangeMap _ (pullback f g) S T _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) h aS d adjS adjd hβI ⟨(derivedPullback g).obj K.obj,
        (derivedPullback_tensor_preserve_QCoh g).1 K.obj K.property⟩))
    ∃ (e₀ : G.left ≅ O.left) (e₁ : O.right ≅ H.left) (e₂ : G.right ≅ H.right),
      G.hom ≫ e₂.hom = e₀.hom ≫ O.hom ≫ e₁.hom ≫ H.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  classical
  intro G O H
  let α := qcInverseBaseChange f g hβS
  let δ := @qcInverseBaseChange _ (pullback f g) S T _
    (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
    (pullback.snd f g) _ _ h hβI
  let e₀ := successiveBaseChangeSourceIso f g h k hk₁ (a.obj K).obj
  obtain ⟨e₂, he⟩ := rectangle_inverseBaseChange_mate_transport
    f g h a c d adja adjc adjd hβ hβS hβI K k hk₁ hk₂
  have paste := congrArg (fun σ ↦ σ.app K) (mateEquiv_vcomp adja adjS adjd α δ)
  simp only [TwoSquare.vComp_app] at paste
  have hS := dualityEquationBaseChangeMap_eq_inverseSquareMate
    f g a aS adja adjS hβS K
  have hI := @dualityEquationBaseChangeMap_eq_inverseSquareMate _ (pullback f g) S T _
    (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
    (pullback.snd f g) _ _ h aS d adjS adjd hβI ((qcPullback g).obj K)
  rw [← hS, ← hI] at paste
  have hp := (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.congr_map paste
  simp only [Functor.map_comp] at hp
  change _ = O.hom ≫ H.hom at hp
  refine ⟨e₀, Iso.refl _, e₂, ?_⟩
  simpa only [Functor.map_comp, Category.assoc, Iso.refl_hom,
    Category.id_comp] using he.trans (congrArg (fun φ ↦ e₀.hom ≫ φ) hp)

end AlgebraicGeometry
