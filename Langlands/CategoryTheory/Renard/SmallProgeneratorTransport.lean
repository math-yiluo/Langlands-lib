import Langlands.CategoryTheory.Renard.SmallProgeneratorTransportStatements
import Langlands.CategoryTheory.Renard.SmallProjectiveFiniteSupport
import Langlands.CategoryTheory.Renard.HomExactnessComparison
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Transport of Renard's small progenerators across equivalences

Proof of `Langlands.Renard.SmallProgeneratorTransportStatement`. Each of the three conjuncts of
`HomSmallProgenerator` is carried along the actual equivalence without comparing the two
integer-module Hom universes:

* projectivity through the published comparison `homProjectiveComparison` with Mathlib's
  `Projective` and Mathlib's `Equivalence.map_projective_iff`;
* coproduct preservation through the published finite-subcoproduct factorization helpers of
  `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteSupport`, moved across the adjunction
  `e.functor ⊣ e.inverse` and the coproduct comparison of `e.inverse`;
* generation through a cancellation characterization of faithfulness of the Hom functor.

The converse direction applies the forward direction to `e.symm` and transports back along the
unit isomorphism. See the paired Markdown for the proof route.
-/

open CategoryTheory CategoryTheory.Limits
open Langlands.CategoryTheory.Renard (preadditiveCoyonedaInt)

universe w v u v' u'

namespace Langlands.Renard

section Helpers

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Renard generation is left cancellation by all morphisms out of `P`: two parallel morphisms
are equal once they agree after precomposition with every morphism from `P`. -/
theorem homGenerator_iff_cancel (P : C) :
    HomGenerator P ↔
      ∀ {X Y : C} (f g : X ⟶ Y), (∀ h : P ⟶ X, h ≫ f = h ≫ g) → f = g := by
  constructor
  · intro hP X Y f g hfg
    have : (preadditiveCoyonedaInt P).Faithful := hP
    apply (preadditiveCoyonedaInt P).map_injective
    ext h
    exact hfg h
  · intro hP
    exact ⟨fun {X Y} f g hfg => hP f g fun h => ConcreteCategory.congr_hom hfg h⟩

/-- Renard projectivity is invariant under isomorphism. -/
theorem homProjective_of_iso {P P' : C} (i : P ≅ P') (hP : HomProjective P) :
    HomProjective P' := by
  have h : HomProjective P ↔ Projective P := homProjectiveComparison P
  have h' : HomProjective P' ↔ Projective P' := homProjectiveComparison P'
  exact h'.2 (Projective.of_iso i (h.1 hP))

/-- Hom coproduct preservation is invariant under isomorphism. -/
theorem homPreservesCoproducts_of_iso [HasCoproducts.{w} C] {P P' : C} (i : P ≅ P')
    (hP : HomPreservesCoproducts.{w} P) : HomPreservesCoproducts.{w} P' := by
  refine homPreservesCoproducts_of_finiteSubcoproduct_factor fun I M φ => ?_
  obtain ⟨s, g, hg⟩ := exists_finiteSubcoproduct_factor_of_homPreservesCoproducts hP M (i.hom ≫ φ)
  exact ⟨s, i.inv ≫ g, by rw [Category.assoc, hg, Iso.inv_hom_id_assoc]⟩

/-- Renard generation is invariant under isomorphism. -/
theorem homGenerator_of_iso {P P' : C} (i : P ≅ P') (hP : HomGenerator P) :
    HomGenerator P' := by
  rw [homGenerator_iff_cancel] at hP ⊢
  intro X Y f g hfg
  exact hP f g fun h => by simpa using i.hom ≫= hfg (i.inv ≫ h)

/-- Renard's small-progenerator condition is invariant under isomorphism. -/
theorem homSmallProgenerator_of_iso [HasCoproducts.{w} C] {P P' : C} (i : P ≅ P')
    (hP : HomSmallProgenerator.{w} P) : HomSmallProgenerator.{w} P' :=
  ⟨⟨homProjective_of_iso i hP.1.1, homPreservesCoproducts_of_iso i hP.1.2⟩,
    homGenerator_of_iso i hP.2⟩

/-- An equivalence carries Renard projective objects to Renard projective objects. -/
theorem homProjective_functor_obj (e : C ≌ D) {P : C} (hP : HomProjective P) :
    HomProjective (e.functor.obj P) := by
  have h : HomProjective P ↔ Projective P := homProjectiveComparison P
  have h' : HomProjective (e.functor.obj P) ↔ Projective (e.functor.obj P) :=
    homProjectiveComparison (e.functor.obj P)
  exact h'.2 ((e.map_projective_iff P).2 (h.1 hP))

omit [Abelian C] [Abelian D] in
/-- The coproduct comparison of a functor is compatible with the canonical maps from finite
subcoproducts. -/
theorem sigmaComparison_map_finiteSubcoproduct_desc [HasCoproducts.{w} C]
    [HasCoproducts.{w} D] (G : D ⥤ C) {I : Type w} (N : I → D) (s : Finset I) :
    sigmaComparison G (fun j : s => N j.val) ≫ G.map (Sigma.desc fun j : s => Sigma.ι N j.val) =
      (Sigma.desc fun j : s => Sigma.ι (fun i => G.obj (N i)) j.val) ≫ sigmaComparison G N := by
  ext j
  simp

/-- An equivalence carries objects whose Hom functor preserves `w`-indexed coproducts to objects
with the same property. A morphism `e.functor.obj P ⟶ ∐ N` corresponds under the adjunction to
a morphism `P ⟶ e.inverse.obj (∐ N) ≅ ∐ (e.inverse.obj ∘ N)`; its finite-subcoproduct
factorization in `C` corresponds back to one in `D`. -/
theorem homPreservesCoproducts_functor_obj [HasCoproducts.{w} C] [HasCoproducts.{w} D]
    (e : C ≌ D) {P : C} (hP : HomPreservesCoproducts.{w} P) :
    HomPreservesCoproducts.{w} (e.functor.obj P) := by
  refine homPreservesCoproducts_of_finiteSubcoproduct_factor fun I N ψ => ?_
  let adj := e.toAdjunction
  obtain ⟨s, g, hg⟩ := exists_finiteSubcoproduct_factor_of_homPreservesCoproducts hP
    (fun i => e.inverse.obj (N i)) (adj.homEquiv _ _ ψ ≫ inv (sigmaComparison e.inverse N))
  refine ⟨s, (adj.homEquiv _ _).symm (g ≫ sigmaComparison e.inverse (fun j : s => N j.val)), ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc,
    sigmaComparison_map_finiteSubcoproduct_desc, ← Category.assoc, hg, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id]

/-- An equivalence carries Renard generators to Renard generators. -/
theorem homGenerator_functor_obj (e : C ≌ D) {P : C} (hP : HomGenerator P) :
    HomGenerator (e.functor.obj P) := by
  rw [homGenerator_iff_cancel] at hP ⊢
  intro X Y f g hfg
  apply e.inverse.map_injective
  refine hP _ _ fun h => (e.toAdjunction.homEquiv _ _).symm.injective ?_
  rw [e.toAdjunction.homEquiv_naturality_right_symm,
    e.toAdjunction.homEquiv_naturality_right_symm]
  exact hfg _

/-- An equivalence carries Renard small progenerators to Renard small progenerators at the same
coproduct index size. -/
theorem homSmallProgenerator_functor_obj [HasCoproducts.{w} C] [HasCoproducts.{w} D]
    (e : C ≌ D) {P : C} (hP : HomSmallProgenerator.{w} P) :
    HomSmallProgenerator.{w} (e.functor.obj P) :=
  ⟨⟨homProjective_functor_obj e hP.1.1, homPreservesCoproducts_functor_obj e hP.1.2⟩,
    homGenerator_functor_obj e hP.2⟩

end Helpers

/-- An actual equivalence transports Renard's small-progenerator predicate at the same coproduct
index size, with independent source and target object and Hom universes. -/
theorem smallProgeneratorTransport
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (D : Type u') [Category.{v'} D] [Abelian D] [HasCoproducts.{w} D] :
    SmallProgeneratorTransportStatement.{w, v, u, v', u'} C D :=
  fun e P => ⟨homSmallProgenerator_functor_obj e, fun h =>
    homSmallProgenerator_of_iso (e.unitIso.app P).symm (homSmallProgenerator_functor_obj e.symm h)⟩

end Langlands.Renard
