# Full finite-place matching for a cyclic algebra, from the field case

`Langlands.BaseChange.CyclicAlgebraFullMatching`. Namespace `Langlands.BaseChange`.

## Statement

- `cyclicAlgebraFullMatching_of_finitePlaceFullMatching :
  FinitePlaceFullMatchingStatement.{u, v} → CyclicAlgebraFullMatchingStatement.{u, v}`.

The universes are the same on both sides: the field `L = E ⧸ 𝔪` to which the hypothesis is applied
lives in the universe `v` of `E`.

## Proof

The setting of `cyclicAlgebraNearIdentityMatching` (field coordinates `c : E ≃ₐ[F] (Fin (m + 1) → L)`
from `exists_cyclicAlgebraFieldCoordinates`, the module topology on `L`, the Borel σ-algebra on
`GL_n(L)`, `κ = cyclicProductGLCoordinates c hc hc'`, and a Haar measure `μ` of `GL_n(L)` with
`MeasurePreserving κ μE (Measure.pi fun _ => μ)` from `exists_isHaarMeasure_measurePreserving_pi`),
and the hypothesis applied to `(F, L, τ, d, n, μF, μ)`:

- from `GL_n(E)`: `exists_concordant_ordinary_cyclicProduct` gives `φL` (the fibre integral of
  `φ ∘ κ⁻¹`); the field statement matches it with some `f`, which is concordant with `φ`;
- from `GL_n(F)`: `VanishesOffNorms σ ((m + 1) d) μF f` is `VanishesOffNorms τ d μF f`
  (`vanishesOffNorms_cyclicProduct_iff`, through `cyclicProductGLCoordinates_isNorm_iff`); the
  field statement gives `φL`, and `exists_concordant_twisted_cyclicProduct` gives `φ`.

## Declarations, in order

`cyclicAlgebraFullMatching_of_finitePlaceFullMatching`.

## Literature

G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle*, Mém. SMF 124 (2011), §I.2.6, p. 18 (the same two constructions, for
functions with regular support); J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the
Advanced Theory of the Trace Formula* (1989), Chapter 1, §5, pp. 48–49.
