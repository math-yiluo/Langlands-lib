import Langlands.GroupScheme.Rational.NumberFieldHasseKernelTypeReduction
import Langlands.GroupScheme.Reductive.QuasiSplit
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Three inputs of Harder's argument for the Hasse kernel in type `E_7`

This module states three propositions about simply connected absolutely
almost-simple groups whose simple vertices are numbered by `CartanMatrix.E 7`:
vanishing of first cohomology of quasi-split groups over totally complex number
fields, existence of a totally complex quadratic extension over which a given
group becomes quasi-split, and the Hasse kernel on a quadratic cover over which
the group becomes quasi-split. The statements are not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over a totally complex number field, a quasi-split simply connected absolutely
almost-simple group of type `E_7` has trivial first cohomology: every cocycle on
every finite Galois field cover is trivial. -/
def NumberFieldTotallyComplexTypeE7Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
    IsQuasiSplit G →
    ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      (ξ : Cocycle G (GaloisCocycle.cover K L)), ξ.IsTrivial

/-- A simply connected absolutely almost-simple group of type `E_7` over a number
field becomes quasi-split over some totally complex quadratic extension, taken
inside the separable closure of the base. -/
def NumberFieldTypeE7QuadraticSplittingFieldStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
    ∃ E : IntermediateField F (SeparableClosure F),
      Module.finrank F E = 2 ∧ NumberField.IsTotallyComplex E ∧
        IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap F E)).obj G)

/-- Let `L/F` be a quadratic extension of a number field over which a simply connected
absolutely almost-simple group of type `E_7` becomes quasi-split. A cocycle of the group
on the cover `Spec L → Spec F` that is trivial after pullback to every completion is
trivial. -/
def NumberFieldTypeE7QuadraticHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
    ∀ (L : Type u) [Field L] [Algebra F L], Module.finrank F L = 2 →
      IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap F L)).obj G) →
      ∀ ξ : Cocycle G (GaloisCocycle.cover F L), ξ.LocallyTrivial → ξ.IsTrivial

end Langlands.GroupScheme
