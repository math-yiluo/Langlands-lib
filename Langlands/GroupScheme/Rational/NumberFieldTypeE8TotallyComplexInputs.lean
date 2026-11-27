import Langlands.GroupScheme.Rational.NumberFieldTypeE8HasseReduction

/-! # Two inputs for groups of type `E_8` over totally complex number fields

This module states two propositions about simply connected absolutely almost-simple
groups of type `E_8` and proves that together they give
`NumberFieldTotallyComplexTypeE8Statement`.

* `TypeE8QuasiSplitOfQuasiSplitCohomologyStatement`: over any field `K`, if every
  quasi-split simply connected group of type `E_8` over `K` has trivial cocycles on
  finite Galois field covers, then every simply connected group of type `E_8` over `K`
  is quasi-split (Platonov–Rapinchuk, Proposition 6.16(A)).
* `NumberFieldTotallyComplexQuasiSplitTypeE8Statement`: over a totally complex number
  field, a quasi-split simply connected group of type `E_8` has trivial cocycles on
  finite Galois field covers (Chernousov; Platonov–Rapinchuk, §6.8).

The two statements are not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Quasi-splitness of groups of type `E_8` from the vanishing of the cohomology of the
quasi-split ones. Let `K` be a field and `G` a simply connected absolutely almost-simple
group of type `E_8` over `K`. If every cocycle of every quasi-split simply connected
absolutely almost-simple group of type `E_8` over `K` on every finite Galois field cover
of `K` is trivial, then `G` is quasi-split. -/
def TypeE8QuasiSplitOfQuasiSplitCohomologyStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
    (∀ (H : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom H.X.hom]
      [LocallyOfFiniteType H.X.hom] (d' : TitsIndexData H) (e' : d'.Vertex ≃ Fin 8),
      IsSimplyConnected H → IsAbsolutelyAlmostSimple H →
      (∀ a b, d'.cartan a b = CartanMatrix.E 8 (e' a) (e' b)) →
      IsQuasiSplit H →
      ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
        (ξ : Cocycle H (GaloisCocycle.cover K L)), ξ.IsTrivial) →
    IsQuasiSplit G

/-- Chernousov's vanishing theorem for quasi-split groups of type `E_8`: over a totally
complex number field `K`, every cocycle of a quasi-split simply connected absolutely
almost-simple group of type `E_8` on a finite Galois field cover of `K` is trivial. -/
def NumberFieldTotallyComplexQuasiSplitTypeE8Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
    IsQuasiSplit G →
    ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      (ξ : Cocycle G (GaloisCocycle.cover K L)), ξ.IsTrivial

/-- The two inputs give `NumberFieldTotallyComplexTypeE8Statement`. The vanishing
statement over the totally complex field `K` supplies the hypothesis of the
quasi-splitness statement, so `G` is quasi-split; the vanishing statement applied to
`G` itself then makes its cocycles trivial. -/
theorem numberFieldTotallyComplexTypeE8_of_quasiSplit
    (hqs : TypeE8QuasiSplitOfQuasiSplitCohomologyStatement.{u})
    (hvan : NumberFieldTotallyComplexQuasiSplitTypeE8Statement.{u}) :
    NumberFieldTotallyComplexTypeE8Statement.{u} := by
  intro K _ _ _ G _ _ d e hsc habs hE8
  have hG : IsQuasiSplit G := hqs K G d e hsc habs hE8
    (fun H _ _ d' e' hsc' habs' hE8' hqs' => hvan K H d' e' hsc' habs' hE8' hqs')
  exact ⟨hG, hvan K G d e hsc habs hE8 hG⟩

end Langlands.GroupScheme
