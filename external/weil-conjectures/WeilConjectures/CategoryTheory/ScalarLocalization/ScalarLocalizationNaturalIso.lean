/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.CategoryTheory.Triangulated.Functor
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # Natural isomorphisms descend through raw scalar localization

Source: the universal property of localization, Stacks 04VB and 05R2.
(blueprint: lem-real-raw-localization-natural-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe r u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ScalarLocalization

/-- Integral natural isomorphisms of functors on raw rational objects extend uniquely.
Source: Stacks 04VB, the universal property of localization
(blueprint: lem-real-raw-localization-natural-iso).

Proof: the scalar localization is a categorical localization, by the already proved
comparison with Rationalization. Precomposition with a localization is fully faithful.
Take the preimage of the given natural isomorphism and evaluate its image equation
on each original object. Faithfulness gives uniqueness. No linearity or additivity
of the target functors is needed. -/
theorem naturalIso_of_integral
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R)
    {A : Type u'} [Category.{v'} A] (F G : ScalarLocalization R C p ⥤ A)
    (e : localization R C p ⋙ F ≅ localization R C p ⋙ G) :
    ∃! d : F ≅ G, ∀ K : C, d.hom.app ((localization R C p).obj K) = e.hom.app K := by
  let Q := localization R C p
  let W := Rationalization.W (Submonoid.powers p) C
  have : Q.IsLocalization W := semilinear_localization_isLocalization R C p
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W A
  refine ⟨ff.preimageIso e, ?_, ?_⟩
  · intro K
    exact congr_app (ff.map_preimage e.hom) K
  · intro d hd
    apply Iso.ext
    apply ff.map_injective
    apply NatTrans.ext
    funext K
    exact (hd K).trans (congr_app (ff.map_preimage e.hom) K).symm

end CategoryTheory.ScalarLocalization
