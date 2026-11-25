/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula

/-! # Composition of raw cohomology pullbacks

Source: Stacks Project, Tag 09Z1, canonical cohomology comparison maps.
(blueprint: lem-sbc-higher-image-raw-pullback-composition).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Two raw pullbacks agree with the pullback of the composite arrow in Over W.
Source: Stacks Project, Tag 09Z1 (lemma-relative-colimit), canonical comparison maps;
Tag 03CB, composition of inverse image functors.
(blueprint: lem-sbc-higher-image-raw-pullback-composition).

Proof: Expand both five-factor formulas. Map the inner five factors through the
outer derived inverse image, using preservation of composition. Naturality of the
single-functor comparison moves the mapped source comparison past the outer
single-functor inverse; the intermediate single comparisons then cancel.
The composition comparison for exact derived inverse images transports the twice
pulled-back class to the pullback along f.left followed by g.left. Associativity
of upperStarComp, applied to f.left, g.left and C.hom followed by k, identifies
the source comparison with the source comparison for the composite. Apply the
same associativity law to f.left, g.left and C.hom to identify the coefficient
comparison. In each case use Over.w f and Over.w g to identify the fixed diagonal.
The single-functor comparison respects composition: verify on the complex concentrated
in degree zero and apply localization. Finally the derived composition comparison
commutes with shifts; naturality and that compatibility combine the two shift
factors into the shift factor for the composite. The five remaining factors are
exactly its defining formula. No affineness, limit, or quasi-compactness hypothesis
is used. Identity arrows, zero sheaves, zero classes, and all integer degrees satisfy
the same comparison equalities. -/
theorem higherDirectImageRawOverPullback_comp
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B C : Over W} (f : A ⟶ B) (g : B ⟶ C) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q C).obj (op U)) :
    higherDirectImageRawOverPullback Λ k G q (f ≫ g) U z =
      higherDirectImageRawOverPullback Λ k G q f U
        (higherDirectImageRawOverPullback Λ k G q g U z) := by
  have h := higherDirectImageRawOverPullback_function_comp Λ k G q f g U
  exact congrFun h z

end AlgebraicGeometry.Etale
