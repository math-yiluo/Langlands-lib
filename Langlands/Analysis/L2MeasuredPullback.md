# Bounded pullback between measured L² spaces

`Langlands.Analysis.boundedL2Pullback` is the continuous complex-linear
pullback from `Lp E 2 ν` to `Lp E 2 μ` along a measurable `φ : X → Y`.
It takes a nonnegative finite scale `c` and the measure domination
`map φ μ ≤ c² • ν`. The complex normed target `E` need not be complete.

- `norm_boundedL2Pullback_le` gives the operator-norm bound `c`.
- `boundedL2Pullback_ae` identifies the result with `f ∘ φ` almost everywhere
  for the chosen representative of an `Lp` element; the `_toLp_ae` version
  works with any supplied `MemLp` representative.
- `restrictL2` is the special case of the identity map from the restricted
  measure to the original measure, with `c = 1`. `restrictL2_ae` gives its
  representative agreement on the restricted measure.

## Construction

The measure domination implies absolute continuity of `map φ μ` with
respect to `ν`. Thus an almost-everywhere equality for `ν` pulls back to
one for `μ`. Compose the actual representatives and use `MemLp.toLp`:
square-integrability follows by first using measure domination and then
changing variables through `map`. The almost-everywhere pullback property
and the `Lp` representative formulas for addition and scalar multiplication
prove linearity. The extended norm bound for the dominated measure has
factor `(c²)^(1/2) = c`. Taking finite real norms gives the bound used in
`LinearMap.mkContinuous` and in the operator-norm theorem.

## Provenance

Derived measure-theoretic infrastructure for the pullbacks and restrictions
of weighted spaces in Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234, §§7.3–7.5
(pp.214–219), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`.
The source uses those operators on specific adelic domains. This construction
handles one supplied pushforward inequality; it does not assert those
adelic domain identities or prove compactness of any convolution operator.
