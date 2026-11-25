/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
/-!
# Underlying abelian sheaf of the small-model module inverse image
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3,
`sites-modules.tex`, labels `lemma-pullback-module` and `lemma-adjoint-push-pull-modules`.
(auxiliary; not a blueprint node).
-/
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- Forgetting the action on the model-site module pullback gives model-site abelian inverse image.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3,
`sites-modules.tex`, labels `lemma-pullback-module` and `lemma-adjoint-push-pull-modules`.
(auxiliary; not a blueprint node).
Proof:
1. Transport the original commutative-ring adjunction through the strict AsSmall
   equivalences and compare its left adjoint with model-site commutative-ring pullback.
   The uniqueness comparison respects the units. Commuting forgetting with filtered
   left Kan extension and sheafification identifies the underlying ring sheaf with set
   inverse image, with unit exactly `proEtaleModelRingUnit f R`.
2. The same canonical comparison presents the actual abelian inverse image as set
   inverse image. Product presentations allow maps to be tested on pairs and triples
   of unit sections. Transport the source scalar action through these presentations.
   Prove its six module laws and semilinearity of restrictions by testing on unit
   sections, where the claims reduce to the source module laws and linearity of the
   abelian unit. The additive carrier is the actual abelian inverse image throughout.
3. An abelian map out of this module is linear if its adjunct is linear: test its two
   scalar-action composites on pairs of unit sections. The reverse implication follows
   by composing with the linear unit. Restricting the abelian hom bijection therefore
   gives a module adjunction to pushforward restricted along the specified ring unit.
4. Uniqueness of left adjoints compares this construction with Mathlib's module
   pullback. Forgetting gives the displayed natural isomorphism. The argument applies
   also to the empty scheme and the zero ring and requires no flatness of `f`. -/
theorem proEtaleModelModuleInverseImage_underlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    let A := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
    let B := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
    let A' := ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj A
    let B' := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj B
    Nonempty (SheafOfModules.pullback.{u + 1} (proEtaleModelRingUnit f R) ⋙
      SheafOfModules.toSheaf B' ≅
      SheafOfModules.toSheaf A' ⋙
        Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
          AddCommGrpCat.{u + 1} (proEtaleModelTopology Y) (proEtaleModelTopology X)) := by
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  let : Limits.PreservesFiniteLimits (proEtaleModelBaseChange f) := by
    change Limits.PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt) ⋙ proEtaleBaseChange f ⋙ AsSmall.up)
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange f) := flat_of_preservesFiniteLimits _
  obtain ⟨p, hp⟩ := proEtaleModelRingPresentation f R
  obtain ⟨e, _⟩ := SheafOfModules.inverseImage_underlying_of_ring_presentation
    (proEtaleModelRingUnit f R) p (by ext U r; exact hp U r)
  exact ⟨e⟩
end AlgebraicGeometry.Scheme
