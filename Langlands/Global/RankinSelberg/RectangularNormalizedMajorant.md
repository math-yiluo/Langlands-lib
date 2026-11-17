# Joint Schwartz majorants after determinant normalization

This internal module defines `rectangularRootPowerWeight F r τ c` as
`∏ i, |c_i/c_(i+1)|^(i*τ)`, the fixed nonnegative root powers left by
`normalized_gauge_weight_le_roots` when `τ ≥ 0`.

For a number field in universe `u` with compact additive adelic
quotient, every `Φ ∈ schwartzBruhat F (t+1+d)` and every `τ ≥ 0`
admit one genuine Schwartz–Bruhat function `Ψ` of rank
`t+1+d*(t+1)`. For every leading idelic diagonal `b`, rectangle `x`
and supplied standard-compact Iwasawa factorization of the lower
unipotent at `x`, the root-power weight times the norm of `Φ` at the
actual corrected roots is at most the norm of `Ψ` at the joint row
of the original block roots and all rectangular entries. The same
`Ψ` works for every such factorization and leading diagonal. The
statement includes an empty rectangle and makes no measurability
claim for a choice of factors.

The implemented proof uses an arbitrary parameter family containing
all these factorization witnesses; the private parameter structure
retains the actual upper-unitriangular and standard-compact
conditions and the exact matrix identity. Its two associated rows
are the actual corrected simple-root row and the original joint row.

At the finite places, domination of `Φ` supplies one nonzero
algebraic integer `q` clearing all actual roots on its support. The
preceding rectangular estimate gives the denominator `q^E` for
`x`, where `E=d*(d+1)`. The correction and its inverse inherit that
denominator. Recovering the original block roots gives denominator
`q*(q^E)^2`, which also clears the joint row. This denominator is
independent of the parameter in the family.

At infinity, the rectangle norm is bounded by
`(d+1)!*(1+‖Y‖)^E` for the actual root row `Y`. The correction and
its inverse have at most linear growth in the rectangle norm, and
recovering the leading roots costs their square. An elementary
polynomial estimate therefore bounds the entire joint row by
`G*(1+‖Y‖)^(2*E+1)`, with `G` depending only on the ranks.

The remaining root powers are also polynomially bounded on the
finite support. `IdeleDenominatorNorm` bounds each full idele norm
by a field-degree power of its archimedean norm and a constant
from `q`. Every exponent `i*τ` is bounded by the common natural
ceiling `ceil(r*τ)`, since the common upper bound for the bases is
at least one. Taking the product yields an integer growth degree
`P=[F:ℚ]*ceil(r*τ)*r`. For a requested joint decay order `N`, the
proof uses the input's decay order `(2*E+1)*N+P` and takes a
nonnegative maximum of its bound.

These finite-support and rapid-decay estimates meet the exact
hypotheses of the published
`SchwartzMajorant.exists_schwartzBruhat_majorant`. Applying that
theorem gives the asserted `Ψ`. No continuity or measurability of
the factorization parameters is needed for that majorant theorem.

The result is the joint pointwise majorant for the normalized
root-profile expression. Integration over the rectangle and torus,
the Whittaker quotient comparison, and the exact Mellin convergence
theorem remain separate steps; none is claimed here.
