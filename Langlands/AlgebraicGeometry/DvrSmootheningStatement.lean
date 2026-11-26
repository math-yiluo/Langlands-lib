import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-! # Smoothenings over a discrete valuation ring -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A local homomorphism `R → R'` of local rings has ramification index one when the
maximal ideal of `R` generates the maximal ideal of `R'` and the residue field extension
is separable, that is, geometrically reduced. For discrete valuation rings the ideal
equality says that the image of a uniformizer of `R` is a uniformizer of `R'`;
separability of the residue field extension is a separate condition. -/
def IsRamificationIndexOne (R R' : Type u) [CommRing R] [IsLocalRing R] [CommRing R']
    [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] : Prop :=
  (IsLocalRing.maximalIdeal R).map (algebraMap R R') = IsLocalRing.maximalIdeal R' ∧
    Algebra.IsGeometricallyReduced (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')

/-- Every scheme of finite type over a discrete valuation ring with smooth generic fibre
has a smoothening: a proper morphism that is an isomorphism on generic fibres, through
whose smooth locus every point with values in an extension of ramification index one
lifts. -/
def DvrSmootheningStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)),
    LocallyOfFiniteType f → QuasiCompact f →
    Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) →
    ∃ (X' : Scheme.{u}) (g : X' ⟶ X), IsProper g ∧
      IsIso (pullback.map (g ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R K))) f
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) g (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])) ∧
      ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
        [Algebra R R'] [IsLocalHom (algebraMap R R')], IsRamificationIndexOne R R' →
        ∀ a : Spec (CommRingCat.of R') ⟶ X,
          a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) →
          ∃ (U : X'.Opens) (a' : Spec (CommRingCat.of R') ⟶ U),
            Smooth (U.ι ≫ g ≫ f) ∧ a' ≫ U.ι ≫ g = a

end Langlands.AlgebraicGeometry
