import Langlands.AlgebraicGeometry.BirationalGroupLaw

/-! # Strict birational group laws on an open subscheme -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {S X : Scheme.{u}}

/-- Density of `W ⊆ X ×_S X` in the open subscheme `X' ×_S X'`, relative to the projection
`q : X ×_S X ⟶ X`: every point of `X' ×_S X'` has a generization in `W` with the same image
under `q`. For a projection `q` and an open subset `W` of `X' ×_S X'`, when `f` is locally
of finite type, this is `X'`-density of `W` in that square viewed as an `X'`-scheme through
`q`. -/
def SquareFibreGenerizationDense (f : X ⟶ S) (q : pullback f f ⟶ X) (X' : X.Opens)
    (W : Set ↑(pullback f f)) : Prop :=
  ∀ p : ↑(pullback f f), (pullback.fst f f).base p ∈ X' → (pullback.snd f f).base p ∈ X' →
    ∃ p' ∈ W, q.base p' = q.base p ∧ p' ⤳ p

namespace BirationalGroupLaw

variable {f : X ⟶ S}

/-- The law `m` restricts to a strict birational group law on the open subscheme `X'` of
`X` (Bosch–Lütkebohmert–Raynaud, *Néron Models*, §5.2 Definition 1): there is an open `U`
of `X ×_S X`, contained in `X' ×_S X'` and in the domain of `m` and mapped into `X'` by `m`,
such that `U` and its images under the universal left and right translations are
`X'`-dense in `X' ×_S X'` with respect to both projections. -/
def IsStrictOn (m : BirationalGroupLaw f) (X' : X.Opens) : Prop :=
  ∃ U : (pullback f f).Opens,
    U ≤ m.domain ∧ U ≤ pullback.fst f f ⁻¹ᵁ X' ∧ U ≤ pullback.snd f f ⁻¹ᵁ X' ∧
    m.domain.ι ⁻¹ᵁ U ≤ m.mul ⁻¹ᵁ X' ∧
    SquareFibreGenerizationDense f (pullback.fst f f) X' U ∧
    SquareFibreGenerizationDense f (pullback.snd f f) X' U ∧
    SquareFibreGenerizationDense f (pullback.fst f f) X'
      ((leftTranslation f m.domain m.mul m.mul_comp).base '' (m.domain.ι ⁻¹ᵁ U)) ∧
    SquareFibreGenerizationDense f (pullback.snd f f) X'
      ((leftTranslation f m.domain m.mul m.mul_comp).base '' (m.domain.ι ⁻¹ᵁ U)) ∧
    SquareFibreGenerizationDense f (pullback.fst f f) X'
      ((rightTranslation f m.domain m.mul m.mul_comp).base '' (m.domain.ι ⁻¹ᵁ U)) ∧
    SquareFibreGenerizationDense f (pullback.snd f f) X'
      ((rightTranslation f m.domain m.mul m.mul_comp).base '' (m.domain.ι ⁻¹ᵁ U))

end BirationalGroupLaw

end Langlands.AlgebraicGeometry
