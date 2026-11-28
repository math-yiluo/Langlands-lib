import Langlands.GroupScheme.Rational.NumberFieldHasseKernelTypeReduction
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Torus.Maximal
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Torus orders and cyclic covers for simply connected groups of type `E_8`

This module states three propositions about simply connected absolutely almost-simple
groups whose simple vertices are numbered by `CartanMatrix.E 8`: over a field of
characteristic zero, every cocycle of a maximal torus on a finite Galois field cover has a
trivial power of exponent `2^a 3^b 5^c`; and over a totally complex number field, a
quasi-split such group has trivial cocycles on every Galois field cover of degree `2` or `3`,
and on every Galois field cover of degree `5`. The statements are not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `G` be a simply connected absolutely almost-simple group of type `E_8` over a field
`K` of characteristic zero and `i : T ⟶ G` a maximal torus. Every cocycle of `T` on a finite
Galois field cover `Spec L → Spec K` has a trivial `2^a 3^b 5^c`-th power. The `n`-th power
of a cocycle `τ` of `T` is its image under the endomorphism `n • 𝟙 T`, which raises points
of `T` to the `n`-th power. -/
def TypeE8MaximalTorusCocycleOrderStatement : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G), IsMaximalTorus i →
    ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      (τ : Cocycle T.toGrp (GaloisCocycle.cover K L)),
      ∃ a b c : ℕ,
        (τ.map (CommGroupScheme.groupHom ((2 ^ a * 3 ^ b * 5 ^ c : ℕ) • 𝟙 T))).IsTrivial

/-- Over a totally complex number field `K`, a quasi-split simply connected absolutely
almost-simple group of type `E_8` has trivial cocycles on every finite Galois field cover
`Spec L → Spec K` of degree `2` or `3`. -/
def NumberFieldTotallyComplexTypeE8QuadraticCubicStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
    IsQuasiSplit G →
    ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      (Module.finrank K L = 2 ∨ Module.finrank K L = 3) →
      ∀ ξ : Cocycle G (GaloisCocycle.cover K L), ξ.IsTrivial

/-- Over a totally complex number field `K`, a quasi-split simply connected absolutely
almost-simple group of type `E_8` has trivial cocycles on every finite Galois field cover
`Spec L → Spec K` of degree `5`. -/
def NumberFieldTotallyComplexTypeE8QuinticStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
    IsQuasiSplit G →
    ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      Module.finrank K L = 5 →
      ∀ ξ : Cocycle G (GaloisCocycle.cover K L), ξ.IsTrivial

end Langlands.GroupScheme
