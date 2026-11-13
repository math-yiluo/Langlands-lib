# The quadratic field `K[X]/(X² - c)` and its embeddings

Module `Langlands.GroupScheme.Quaternionic.KneserThreeField`, namespace
`Langlands.GroupScheme.KneserThree.QuadField`. This is internal support for the explicit
A₃ = D₃ comparison (see `KneserThreeSplitting`). It makes no literature claim.

## Definitions

* `poly c = X² - C c` for `c : K`, a field. `poly_monic`, `poly_natDegree` (= 2) and
  `poly_ne_zero` hold for every `c`.
* `irreducible_poly`: if `r * r ≠ c` for every `r : K`, then `poly c` is irreducible. The proof
  uses the Mathlib criterion for polynomials of degree at most three without roots.
* `field c = AdjoinRoot (poly c)`, an abbreviation, and `root = AdjoinRoot.root (poly c)`.
* `powerBasis`: Mathlib's power basis `AdjoinRoot.powerBasis'` of the monic polynomial `poly c`.
  `powerBasis_dim` says its dimension is `2`.

## Results under `Fact (Irreducible (poly c))`

* An instance `Algebra.IsQuadraticExtension K (field c)`, from the power basis of `AdjoinRoot`.
* `isSeparable`: if `(2 : K) ≠ 0` and `c ≠ 0`, then `Algebra.IsSeparable K (field c)`. The minimal
  polynomial of the root is `poly c`, which is separable by `separable_X_pow_sub_C`, and the root
  generates the field. This is a theorem, not an instance.
* `root_mul_self`: `root * root = algebraMap K (field c) c`.
* `exists_eq`: every `a : field c` is `a₀ • 1 + a₁ • root` for some `a₀ a₁ : K`.
* `trace_root`: `Algebra.trace K (field c) root = 0`. This holds because the next coefficient of
  `poly c` is zero.
* `conjugation_root`: assuming in addition `[Algebra.IsSeparable K (field c)]`, the Library's
  conjugation `SU3Root.conjugation K (field c)` of the quadratic extension sends `root` to `-root`.
  The proof uses the Library identity `algebraMap K (field c) (trace a) = a + ā`
  (`SU3Root.algebraMap_trace`) together with `trace_root`.

## The embedding

For a ring `D` that is a `K`-algebra (it need not be commutative) and `x : D` with
`x * x = algebraMap K D c`, `embed x hx : field c →ₐ[K] D` is the `K`-algebra homomorphism that
sends `root` to `x` (`embed_root`). It is the map induced on the quotient by `Polynomial.aeval x`,
which kills `poly c` because `x² = c`.
