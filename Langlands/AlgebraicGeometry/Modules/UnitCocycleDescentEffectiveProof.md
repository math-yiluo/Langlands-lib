# Effective descent of unit cocycles to line bundles

This module proves the published statement
`Langlands.Scheme.Modules.UnitCocycleDescentEffectiveStatement` from
`Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentStatements`, unchanged.

## Statement

`Langlands.Scheme.Modules.unitCocycleDescentEffective :
UnitCocycleDescentEffectiveStatement.{u}`. Let `p : X ⟶ Y` be an affine, flat, surjective
morphism of schemes. Let `c` assign a unit `c U a b h` of `Γ(U, ⊤)` to every pair
`a b : U ⟶ X` with `h : a ≫ p = b ≫ p`. Assume that `c` is natural under precomposition and
multiplicative along triples. Then there are a line bundle `L` on `Y` and an isomorphism
`α : p^* L ≅ 𝒪_X` whose comparison scalar on every such pair, namely
`structureAutScalar (equalCompositeUnitAut p a b h α)`, is `c U a b h`.

This is the effectivity half of faithfully flat descent for invertible modules with
trivialized pullback (Stacks Project, Descent, Proposition 3.9, Tag 023N, for modules along
a faithfully flat ring map).

## Proof

The theorem applies `Langlands.Scheme.UnitCocycleDescent.unitCocycleDescentEffective_of_localUnits`
from `UnitCocycleDescent.Effective` to the published proof
`Langlands.Algebra.unitCocycleLocalUnits` of
`Langlands.Algebra.UnitCocycleLocalUnitsStatement`.

The helper modules carry out the following construction. Their Markdown files describe the
proofs in detail.

1. `UnitCocycleDescent.Submodule`: `L` is the subsheaf of `p_* 𝒪_X` whose sections over an
   open `W` of `Y` are the functions `σ` on `p ⁻¹ᵁ W` with `c · a^* σ = b^* σ` on every open
   of `U`, for every pair `a`, `b`.
2. `UnitCocycleDescent.FunctionDescent`: functions on `p ⁻¹ᵁ V` with equal pullbacks along
   all such pairs come from `V`, and `p.app V` is injective. This uses that a quasi-compact
   flat surjection is an effective epimorphism, from Mathlib's fpqc topology.
3. `UnitCocycleDescent.Affine`: over an affine open `W`, `c` yields a unit
   `u` of `Γ(X, p ⁻¹ᵁ W) ⊗ Γ(X, p ⁻¹ᵁ W)` over `Γ(Y, W)` satisfying the cocycle identity.
   The ring map `Γ(Y, W) → Γ(X, p ⁻¹ᵁ W)` is faithfully flat. The algebraic statement then
   yields, near every point of `Y`, a section of `L` that is a unit upstairs.
4. `UnitCocycleDescent.Frame`: such a section trivializes `L` on its open, so `L` is a line
   bundle.
5. `UnitCocycleDescent.StalkCriterion` and `UnitCocycleDescent.Effective`: the map
   `p^* L ⟶ 𝒪_X` adjoint to the inclusion `L ⟶ p_* 𝒪_X` sends these local sections to
   units, so it is an isomorphism `α`. Its comparison scalars are computed by transposing
   along the pullback–pushforward adjunction. On sections they reduce to the defining
   condition of `L`, which gives `c U a b h`.
