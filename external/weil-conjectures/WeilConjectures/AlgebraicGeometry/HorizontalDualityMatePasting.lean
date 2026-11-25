/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Mathlib.CategoryTheory.Comma.Arrow

import WeilConjectures.AlgebraicGeometry.HorizontalDualityMateCommutativity

/-! # Horizontal pasting of canonical duality mates

Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S).
(blueprint: lem-sc-horizontal-duality-mate-pasting).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The horizontal mate-pasting law for two consecutive base morphisms, before
transport to an open subscheme. No mate is assumed invertible.
Source: Stacks Project, duality.tex, Tags 0ATR and 0E9S; cohomology.tex, Tag 0ATM.
(blueprint: lem-sc-horizontal-duality-mate-pasting)

Proof: Use derived pullback composition to identify the two source functors.
The canonical pullback associativity isomorphism identifies the two total spaces;
direct-image composition and uniqueness of right adjoints identify the target functors,
also using pullback composition for the input on Z. Expand the three canonical
mates as unit, pullback of inverse conjugate of ordinary base change, and counit.
Naturality moves the first inverse conjugate past the second unit. The composite
adjunction formulas and triangle identities cancel the middle counit-unit pair.
Ordinary base change pastes under the coherent pullback comparisons (0ATM).
Tor-independence in 0ATR is only used to obtain invertibility of ordinary
base change, which is assumed explicitly here.
Conjugation reverses composition, and inversion restores the order. This gives
the commuting square between the two endpoint isomorphisms, hence the arrow
isomorphism by Arrow.isoMk. The argument is natural in K and valid for zero
objects and empty schemes; it uses no geometric property beyond the hypotheses.
-/
theorem horizontal_duality_mate_pasting
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤ schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
          (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y)
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (h : Z ⟶ Y')
    (c : schemeDerivedQCohCategory Z ⥤
      schemeDerivedQCohCategory (pullback f (h ≫ g)))
    (adjc : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι ⋙
        schemeDerivedDirectImage (pullback.snd f (h ≫ g))) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _ _ _
          (pullback.snd f (h ≫ g)) _ _).fst E.obj E.property) ⊣ c)
    (hβh : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
        (pullback.fst f (h ≫ g)) pullback.condition E.obj))
    (d : schemeDerivedQCohCategory Z ⥤
      schemeDerivedQCohCategory (pullback (pullback.snd f g) h))
    (adjd : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι ⋙
        schemeDerivedDirectImage (pullback.snd (pullback.snd f g) h)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h))
          _ _ _ _ (pullback.snd (pullback.snd f g) h) _ _).fst E.obj E.property) ⊣ d)
    (hβ₂ : ∀ E : schemeDerivedQCohCategory (pullback f g),
      IsIso (schemeDerivedBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h
        (pullback.fst (pullback.snd f g) h) pullback.condition E.obj)) :
    Nonempty (Arrow.mk
      ((derivedPullback (pullback.fst (pullback.snd f g) h)).map
        ((schemeDerivedQCohProperty (pullback f g)).ι.map
            (@dualityEquationBaseChangeMap _ X Y Y'
              (QuasiCompact.compactSpace_of_compactSpace f)
              (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
              f g a a' adjf adjf' hβ K)) ≫
        ((schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
            (@dualityEquationBaseChangeMap _ (pullback f g) Y' Z
              (QuasiCompact.compactSpace_of_compactSpace (pullback.snd f g))
              (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
              (pullback.snd f g) h a' d adjf' adjd hβ₂
              (((schemeDerivedQCohProperty Y').lift
                ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
                (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1
                  E.obj E.property)).obj K)))) ≅
      Arrow.mk ((derivedPullback (pullbackLeftPullbackSndIso f g h).hom).map
        ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι.map
            (@dualityEquationBaseChangeMap _ X Y Z
              (QuasiCompact.compactSpace_of_compactSpace f)
              (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
              f (h ≫ g) a c adjf adjc hβh K)))) := by
  exact ⟨Arrow.isoMk (horizontalMateSourceIso f g h (a.obj K).obj)
    (horizontalMateTargetIso f g h c d adjc adjd K)
    (horizontal_duality_mate_commutativity g f a a' adjf adjf' hβ K h c adjc
      hβh d adjd hβ₂).symm⟩

end AlgebraicGeometry
