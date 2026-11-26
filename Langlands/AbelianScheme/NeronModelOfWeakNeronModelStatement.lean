import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.WeakNeronMappingProperty
import Langlands.AlgebraicGeometry.BirationalGroupLaw

/-! # The birational group law on ω-minimal models and its solution -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open NeronModelInfra Langlands.AlgebraicGeometry

/-- Let `B` be an abelian variety over the fraction field `K` of a discrete valuation ring
`R` with a smooth separated model `W` of finite type which has the weak Néron mapping
property. Then `B` has a smooth separated faithfully flat model `X` of finite type with an
`R`-birational group law `m` which is defined on the whole generic fibre of `X ×_R X`,
where both universal translations map onto the generic fibre; and every solution of `m`
containing all of `X` has the Néron mapping property. -/
def NeronModelOfWeakNeronModelStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) (W : Over (Spec (CommRingCat.of R))),
    Smooth W.hom → IsSeparated W.hom → LocallyOfFiniteType W.hom → QuasiCompact W.hom →
    Nonempty (B.X ≅ (Over.pullback (specGenericFibreInclusion R K)).obj W) →
    WeakNeronMappingProperty R K W.hom →
    ∃ (X : Over (Spec (CommRingCat.of R)))
      (_ : B.X ≅ (Over.pullback (specGenericFibreInclusion R K)).obj X)
      (m : BirationalGroupLaw X.hom),
      Smooth X.hom ∧ IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
      Surjective X.hom ∧
      (∀ p : ↑(pullback X.hom X.hom),
        (pullback.fst X.hom X.hom ≫ X.hom).base p ≠ IsLocalRing.closedPoint R →
          p ∈ m.domain ∧
          p ∈ Set.range (leftTranslation X.hom m.domain m.mul m.mul_comp).base ∧
          p ∈ Set.range (rightTranslation X.hom m.domain m.mul m.mul_comp).base) ∧
      ∀ σ : m.Solution, σ.domain = ⊤ → NeronModelPropertyBundle R K σ.group.X.hom

end Langlands.AbelianScheme
