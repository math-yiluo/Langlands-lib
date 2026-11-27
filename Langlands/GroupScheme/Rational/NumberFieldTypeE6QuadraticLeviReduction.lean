import Langlands.GroupScheme.Rational.NumberFieldTypeE6HasseReduction
import Langlands.GroupScheme.Rational.NumberFieldQuadraticOppositeMinimalParabolicLevi

/-! # The type `E_6` Hasse kernel on quadratic covers from a Levi subgroup

This module states two propositions about simply connected absolutely almost-simple groups of
type `E_6` over number fields, following Platonov–Rapinchuk, §6.8 (after Harder):

* `NumberFieldTotallyComplexTypeE6DistinguishedVerticesStatement`: over a totally complex number
  field, the vertices `α₂` and `α₄` of the Tits index (Bourbaki numbering) are distinguished.
* `NumberFieldTypeE6QuadraticLeviHasseStatement`: if `α₂` and `α₄` are distinguished over a
  quadratic Galois extension `E/F`, then a cocycle of the intersection `C = P ∩ σ(P)` of a
  minimal parabolic subgroup `P` of `G_E` with its Galois translate, on the cover
  `Spec E → Spec F`, that is trivial at the real places has trivial image in `G`
  (Lemma 6.33 and the construction preceding it).

It proves that these two statements and `NumberFieldQuadraticOppositeMinimalParabolicLeviStatement`
together give `NumberFieldTypeE6QuadraticHasseStatement`. The three statements are not proved
here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- Over a totally complex number field, the vertices numbered `1` and `3` by
`CartanMatrix.E 6` (Bourbaki's `α₂` and `α₄`) of every actual Tits index of a simply connected
absolutely almost-simple group of type `E_6`, inner or outer, are distinguished. -/
def NumberFieldTotallyComplexTypeE6DistinguishedVerticesStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K], IsTotallyComplex K →
    ∀ (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    e.symm 1 ∈ d.distinguishedVertices ∧ e.symm 3 ∈ d.distinguishedVertices

/-- Let `G` be a simply connected absolutely almost-simple group of type `E_6` over a number
field `F`, and let `E/F` be a finite Galois extension such that the vertices numbered `1` and
`3` (Bourbaki's `α₂` and `α₄`) of every actual Tits index of `G_E` numbered by
`CartanMatrix.E 6` are distinguished. Let `t : C ⟶ G` satisfy
`IsQuadraticOppositeMinimalParabolicLevi E t`, so that `E/F` is quadratic and `C_E = P ∩ σ(P)`
is a Levi subgroup of a minimal parabolic subgroup `P` of `G_E`. Then every cocycle `δ` with
values in `C` on the cover `Spec E → Spec F` whose pullback to the full base-changed cover at
every real place of `F` is trivial has trivial image `δ.map t` in `G`. -/
def NumberFieldTypeE6QuadraticLeviHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    ∀ (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E],
      (∀ [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom]
        [LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom]
        (d' : TitsIndexData ((GroupScheme.baseChange (algebraBaseMap F E)).obj G))
        (e' : d'.Vertex ≃ Fin 6),
        (∀ a b, d'.cartan a b = CartanMatrix.E 6 (e' a) (e' b)) →
        e'.symm 1 ∈ d'.distinguishedVertices ∧ e'.symm 3 ∈ d'.distinguishedVertices) →
      ∀ (C : GroupScheme (Spec (CommRingCat.of F))) (t : C ⟶ G),
        IsQuadraticOppositeMinimalParabolicLevi E t →
        ∀ δ : Cocycle C (GaloisCocycle.cover F E),
          (∀ w : InfinitePlace F, w.IsReal →
            (δ.baseChangePullback
              (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial) →
          (δ.map t).IsTrivial

/-- The type `E_6` Hasse kernel on a totally complex quadratic cover follows from the
distinguished vertices over totally complex fields, the reduction of quadratic cocycles to the
Levi subgroup of an opposite pair of minimal parabolic subgroups, and the Levi Hasse statement.
A locally trivial cocycle is trivial at the real places; it is cohomologous to the image of a
Levi cocycle trivial at the real places, whose image in `G` is trivial. -/
theorem numberFieldTypeE6QuadraticHasse_of_minimalParabolicLevi
    (hI : NumberFieldTotallyComplexTypeE6DistinguishedVerticesStatement.{u})
    (hII : NumberFieldQuadraticOppositeMinimalParabolicLeviStatement.{u})
    (hIII : NumberFieldTypeE6QuadraticLeviHasseStatement.{u}) :
    NumberFieldTypeE6QuadraticHasseStatement.{u} := by
  intro F _ _ G _ _ d e hsc habs hcar E _ _ _ _ _ hdeg hEc ξ hξ
  have : IsTotallyComplex E := hEc
  have hscE : IsSimplyConnected ((GroupScheme.baseChange (algebraBaseMap F E)).obj G) :=
    isSimplyConnectedFieldExtension F E G hsc
  have habsE : IsAbsolutelyAlmostSimple ((GroupScheme.baseChange (algebraBaseMap F E)).obj G) :=
    habs.baseChange_of_algebraicExtension
  obtain ⟨C, t, ht, hred⟩ := hII F E hdeg G hsc.isSemisimple
  obtain ⟨δ, hδ, hδreal⟩ := hred ξ (fun w _ => hξ (.inl w))
  exact Cocycle.IsTrivial.of_cohomologous hδ
    (hIII F G d e hsc habs hcar E (fun d' e' h => hI E hEc _ d' e' hscE habsE h)
      C t ht δ hδreal)

end Langlands.GroupScheme
