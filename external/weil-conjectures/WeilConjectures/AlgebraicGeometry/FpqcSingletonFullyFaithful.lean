/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDescentDataCategory
import WeilConjectures.AlgebraicGeometry.DescentPullbackConstruction
import WeilConjectures.AlgebraicGeometry.FpqcDescentUnderlyingMorphism
import WeilConjectures.AlgebraicGeometry.FpqcDescentMorphismCompatibility

/-!
# Fully faithful pullback of descent data along an fpqc singleton

Source: Stacks Project, Descent, Lemma 0241 (lemma-fully-faithful)
(blueprint: lem-galois-fpqc-singleton-fully-faithful-0241).

## Main definitions

- `CategoryTheory.Over.DescentDataCategory`: the category `DD(X/S)` of descent data on
  schemes over `X` relative to `a : X ⟶ S`, with the morphisms of descent data.

## Main statements

- `CategoryTheory.fpqc_singleton_pullback_fullyFaithful`: pullback of descent data along a
  singleton fpqc covering `r : X' ⟶ X` is fully faithful.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory

/--
Let `a : X ⟶ S` be a morphism of schemes and let `r : X' ⟶ X` be a singleton
fpqc covering.  Pullback along `r` gives a fully faithful functor from descent
data on schemes over `X` relative to `X/S` to descent data on schemes over
`X'` relative to `X'/S`.

Source: Stacks Project, Descent, Lemma 0241 (lemma-fully-faithful), assumptions
(1)--(2) and conclusion (blueprint: lem-galois-fpqc-singleton-fully-faithful-0241).

For each object, `q` exhibits the image as the pullback of its underlying scheme,
and `IsBaseChange` identifies its datum with the pulled-back datum. Naturality
of `q` says that the functor maps each morphism to its pullback.

For fullness, restrict the compatibility equation of a morphism of pulled-back
data along `X' ×_X X' → X' ×_S X'`. The diagonal identity of a descent datum
makes this the overlap equation. Descend the underlying morphism along the fpqc
cover by Tag 02W0. To check the descended map preserves descent data, pull the
equation back along `X' ×_S X' → X ×_S X`, factor this map into two base changes
of the cover, and use fpqc descent of morphisms twice. The same descent lemma
gives uniqueness and hence faithfulness.
-/
theorem fpqc_singleton_pullback_fullyFaithful
    {S X X' : Scheme.{u}} (a : X ⟶ S) (r : X' ⟶ X)
    (hr : Presieve.singleton r ∈ Scheme.fpqcPrecoverage X) :
    ∃ (F : Over.DescentDataCategory a ⥤ Over.DescentDataCategory (r ≫ a))
      (q : ∀ A : Over.DescentDataCategory a, (F.obj A).V.left ⟶ A.V.left),
      Nonempty F.FullyFaithful ∧
      (∀ A, ∃ hq : q A ≫ A.V.hom = (F.obj A).V.hom ≫ r,
        IsPullback (q A) (F.obj A).V.hom A.V.hom r ∧
        Over.DescentDatum.IsBaseChange rfl hq A.datum (F.obj A).datum) ∧
      ∀ A B (f : A ⟶ B), (F.map f).hom.left ≫ q B = q A ≫ f.hom.left := by
  classical
  obtain ⟨F, q, hq, hn⟩ := descent_pullback_construction a r
  have lift_exists (A B : Over.DescentDataCategory a) (β : F.obj A ⟶ F.obj B) :
      ∃ α : A ⟶ B, q A ≫ α.hom.left = β.hom.left ≫ q B := by
    obtain ⟨α, hα, _⟩ := fpqc_descent_underlying_morphism a r hr F q hq A B β
    exact ⟨⟨α, fpqc_descent_morphism_compatibility a r hr F q hq A B β α hα⟩, hα⟩
  let preimage {A B : Over.DescentDataCategory a} (β : F.obj A ⟶ F.obj B) : A ⟶ B :=
    (lift_exists A B β).choose
  have preimage_eq {A B : Over.DescentDataCategory a} (β : F.obj A ⟶ F.obj B) :
      q A ≫ (preimage β).hom.left = β.hom.left ≫ q B :=
    (lift_exists A B β).choose_spec
  refine ⟨F, q, ⟨{ preimage := preimage, map_preimage := ?_, preimage_map := ?_ }⟩,
    hq, hn⟩
  · intro A B β
    apply Over.DescentDataCategory.Hom.ext
    apply Over.OverMorphism.ext
    obtain ⟨h, hp, _⟩ := hq B
    apply hp.hom_ext
    · simpa only [hn] using (preimage_eq β)
    · exact (Over.w _).trans (Over.w _).symm
  · intro A B α
    obtain ⟨γ, hγ, hu⟩ := fpqc_descent_underlying_morphism a r hr F q hq A B (F.map α)
    apply Over.DescentDataCategory.Hom.ext
    exact (hu _ (preimage_eq (F.map α))).trans (hu _ (hn A B α).symm).symm

end CategoryTheory
