/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Compactification.NagataCompactification

/-!
# Relative Künneth theorem

Source: current blueprint, `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/
sk-thm-sf-kunneth-relative/thm-sf-kunneth-relative.md` (blueprint:
lemma-kunneth-formula-compact-supports--1).

This is the statement node `lemma-kunneth-formula-compact-supports--1` from the current blueprint.
The canonical comparison is the published six-factor composite
`AlgebraicGeometry.Etale.relativeKunnethIso`; its naturality is exposed by the published
bifunctor isomorphism `relativeKunnethNatIso`.  The remaining clauses record the canonical
base-change and proper `Rf_!`/`Rf_*` comparisons and the compact-support product after
restriction to closed subschemes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale


/-- Comparison for two equal pullback paths, used in the base-change square.
Source: lemma-kunneth-formula-compact-supports--1, compatibility with base change and proof Step 5
(blueprint: lemma-kunneth-formula-compact-supports--1). -/
noncomputable def leftDerivedUpperStarCompPathIso
    (Λ : Type (u + 1)) [CommRing Λ]
    {T S R U : Scheme.{u}} (a : T ⟶ S) (p : S ⟶ R) (q : T ⟶ U) (r : U ⟶ R)
    (h : a ≫ p = q ≫ r)
    (K : _root_.DerivedCategory (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((a)^*[ModuleCat.{u + 1} Λ])).obj ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (L((q)^*[ModuleCat.{u + 1} Λ])).obj ((L((r)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a p).app K).symm ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) q r (a ≫ p) h).app K

/-- The pasted exchange square expressing base-change compatibility of the canonical
relative Künneth composite.  Every comparison in this definition is a published canonical
comparison; no auxiliary map is chosen.  Source: the base-change clause and proof Step 5 of
`lemma-kunneth-formula-compact-supports--1` (blueprint:
lemma-kunneth-formula-compact-supports--1). -/
def relativeKunnethBaseChangeCompatibility
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    [HasCompactification f] [HasCompactification g] [QuasiCompact f] [QuasiCompact g]
    [HasCompactification (pullback.toBase f g)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  ∀ {B' X' Y' : Scheme.{u}} (b' : B' ⟶ B) (f' : X' ⟶ B') (g' : Y' ⟶ B')
    (pX : X' ⟶ X) (pY : Y' ⟶ Y)
    (sqf : IsPullback pX f' f b') (sqg : IsPullback pY g' g b')
    (π : pullback f' g' ⟶ pullback f g)
    (hX : π ≫ pullback.fst f g = pullback.fst f' g' ≫ pX)
    (hY : π ≫ pullback.snd f g = pullback.snd f' g' ≫ pY)
    (sqt : IsPullback π (pullback.toBase f' g') (pullback.toBase f g) b'),
    letI : HasCompactification f' := HasCompactification.of_isPullback sqf
    letI : HasCompactification g' := HasCompactification.of_isPullback sqg
    letI : QuasiCompact f' :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) sqf inferInstance
    letI : QuasiCompact g' :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) sqg inferInstance
    letI : HasCompactification (pullback.toBase f' g') :=
      HasCompactification.of_isPullback sqt
    letI : QuasiCompact (pullback.toBase f g) := quasiCompact_pullback_toBase f g
    letI : QuasiCompact (pullback.toBase f' g') :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) sqt inferInstance
    let κ := (relativeKunnethIso Λ f g K L).hom
    let κ' :=
      (relativeKunnethIso Λ f' g' ((L((pX)^*[ModuleCat.{u + 1} Λ])).obj K)
        ((L((pY)^*[ModuleCat.{u + 1} Λ])).obj L)).hom
    let exf := (rightDerivedLowerShriekBaseChangeIso Λ sqf K).hom
    let exg := (rightDerivedLowerShriekBaseChangeIso Λ sqg L).hom
    let ext :
        (L((π)^*[ModuleCat.{u + 1} Λ])).obj
            (externalProduct (ModuleCat.{u + 1} Λ) f g K L) ≅
          externalProduct (ModuleCat.{u + 1} Λ) f' g'
            ((L((pX)^*[ModuleCat.{u + 1} Λ])).obj K)
            ((L((pY)^*[ModuleCat.{u + 1} Λ])).obj L) :=
      leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) π _ _ ≪≫
        tensorIso
          (leftDerivedUpperStarCompPathIso Λ π
            (pullback.fst f g) (pullback.fst f' g') pX hX K)
          (leftDerivedUpperStarCompPathIso Λ π
            (pullback.snd f g) (pullback.snd f' g') pY hY L)
    let ext' :=
      (R(pullback.toBase f' g')_![ModuleCat.{u + 1} Λ]).mapIso ext
    let extTensor :=
      leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) b'
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj L)
    let exfTensor :=
      ((-⊗ᴸ-(B')[ModuleCat.{u + 1} Λ]).map exf).app
        ((L((b')^*[ModuleCat.{u + 1} Λ])).obj
          ((R(g)_![ModuleCat.{u + 1} Λ]).obj L))
    let exgTensor :=
      ((-⊗ᴸ-(B')[ModuleCat.{u + 1} Λ]).obj
        ((R(f')_![ModuleCat.{u + 1} Λ]).obj
          ((L((pX)^*[ModuleCat.{u + 1} Λ])).obj K))).map exg
    let ext_t :=
      (rightDerivedLowerShriekBaseChangeIso Λ sqt
        (externalProduct (ModuleCat.{u + 1} Λ) f g K L)).hom
    (L((b')^*[ModuleCat.{u + 1} Λ])).map κ ≫ extTensor.hom ≫ exfTensor ≫ exgTensor =
      ext_t ≫ ext'.hom ≫ κ'

/-- Compatibility with proper direct image, expressed using the canonical forward
ordinary Künneth map and the published forget-supports comparisons
`AlgebraicGeometry.Etale.compactificationForgetSupports` of the chosen compactifications.
The premise permits either factor to be proper. For each proper factor its comparison is the
canonical identification `Rf_! ≅ Rf_*` (`isIso_compactificationForgetSupports`).
Source: lemma-kunneth-formula-compact-supports--1, proper clause and proof Step 6
(blueprint: lemma-kunneth-formula-compact-supports--1). -/
def relativeKunnethProperCompatibility
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {X Y B : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    [HasCompactification f] [HasCompactification g] [QuasiCompact f] [QuasiCompact g]
    [HasCompactification (pullback.toBase f g)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : Prop :=
  IsProper f ∨ IsProper g →
    (compactificationForgetSupports (ModuleCat.{u + 1} Λ)
          (HasCompactification.compactification (pullback.toBase f g))).app
        (externalProduct (ModuleCat.{u + 1} Λ) f g K L) =
      (relativeKunnethIso Λ f g K L).hom ≫
        ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).map
          ((compactificationForgetSupports (ModuleCat.{u + 1} Λ)
          (HasCompactification.compactification f)).app K)).app
          ((R(g)_![ModuleCat.{u + 1} Λ]).obj L) ≫
        ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)).map
          ((compactificationForgetSupports (ModuleCat.{u + 1} Λ)
          (HasCompactification.compactification g)).app L) ≫
        kunnethMap (ModuleCat.{u + 1} Λ) (pullback.fst f g) (pullback.snd f g)
          f g (pullback.toBase f g) (by simp) (by simp) K L

/-- The canonical restriction comparison for exterior products. This is the explicit
pullback-composition/tensor comparison occurring in the proof of the published
`nonempty_iso_leftDerivedUpperStar_externalProduct`, with no choice from `Nonempty`.
Source: lemma-kunneth-formula-compact-supports--1, proof Step 5 (blueprint:
lemma-kunneth-formula-compact-supports--1). -/
def relativeKunnethExteriorPullbackIso
    {Λ : Type (u + 1)} [CommRing Λ]
    {X Y B Z W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((pullback.mapOverBase i j f g)^*[ModuleCat.{u + 1} Λ])).obj
        (externalProduct (ModuleCat.{u + 1} Λ) f g K L) ≅
      externalProduct (ModuleCat.{u + 1} Λ) (i ≫ f) (j ≫ g)
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L) :=
  leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) (pullback.mapOverBase i j f g) _ _ ≪≫
    tensorIso
      (leftDerivedUpperStarCompPathIso Λ (pullback.mapOverBase i j f g)
        (pullback.fst f g) (pullback.fst (i ≫ f) (j ≫ g)) i (by simp) K)
      (leftDerivedUpperStarCompPathIso Λ (pullback.mapOverBase i j f g)
        (pullback.snd f g) (pullback.snd (i ≫ f) (j ≫ g)) j (by simp) L)

/-- The compact-support product of the restrictions to closed subschemes, as the inverse
of the specified Künneth comparison followed by the canonical exterior-product restriction
comparison. Its target is `RΓ_c(Z ×_k W, (iZ × iW)^*(K ⊠ L))`, not cohomology with supports.
Source: lemma-kunneth-formula-compact-supports--1, last display and proof Step 5
(blueprint: lemma-kunneth-formula-compact-supports--1). -/
def relativeKunnethClosedRestrictionMap
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [HasCompactification (i ≫ f)] [HasCompactification (j ≫ g)]
    [QuasiCompact (i ≫ f)] [QuasiCompact (j ≫ g)]
    [HasCompactification (pullback.toBase (i ≫ f) (j ≫ g))]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  (relativeKunnethIso Λ (i ≫ f) (j ≫ g)
      ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L)).inv ≫
    (R(pullback.toBase (i ≫ f) (j ≫ g))_![ModuleCat.{u + 1} Λ]).map
      (relativeKunnethExteriorPullbackIso f g i j K L).inv

end AlgebraicGeometry.Etale
