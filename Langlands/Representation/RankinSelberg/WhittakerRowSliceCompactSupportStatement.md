# Compact support of Whittaker row data on a determinant slice

Worker 724 states
`Langlands.RankinSelberg.WhittakerRowSliceCompactSupportStatement.{uF,uV}`
in `Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportStatement`.
Worker 484 proposed this focused interface and the proof route sketched below.
This module defines a proposition and does not prove it.

## Complete statement

The parameters are an arbitrary `p : ℕ` with `[Fact p.Prime]`,
`F : PadicField.{uF} p`, a supplied `T : F.TopologicalData`, and `n : ℕ`.
The actual group is `Langlands.GeneralLinear (n + 1) F.Carrier`, so `n = 0`
is `GL₁`. The statement installs `T.topology`, `T.valuativeRel` and
`T.localField`. The general linear group then carries Mathlib's topology on
the units of the matrix ring. The quotient
`LeftUnipotentQuotient n F.Carrier` is the published right-relation quotient
`QuotientIntegration.LeftQuotient (upperUnipotent (n + 1) F.Carrier)`, that is,
the left coset space `N_(n+1) \ GL_(n+1)`, with Mathlib's quotient topology.
No other topology or measurable structure is used.

After these local instances the proposition quantifies, in order:

1. Every `ψ : UnitaryAdditiveCharacter F.Carrier`. This structure already
   contains continuity, unit-circle values and nontriviality.
2. Every carrier `V : Type uV` with `AddCommGroup` and `Module ℂ` instances,
   and every actual representation
   `π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V`.
3. The hypothesis `IsSmooth π`: every vector is fixed by some open subgroup.
4. Every `ℓ : Whittaker.glFunctionals ψ n π`, that is, every linear functional
   with `ℓ(π(u)v) = θ_ψ(u) ℓ(v)` for the standard character on the upper
   unipotent subgroup. The zero functional is included.
5. Every actual coefficient-image element
   `W : (Whittaker.coefficientModel π ℓ).toSubmodule`. Its value
   `W.val : WhittakerFunctions ψ n` is a function `g ↦ ℓ(π(g)v)` for some
   `v : V`. The zero coefficient is included.
6. Every `Φ : HarmonicAnalysis.SchwartzBruhat (Fin (n + 1) → F.Carrier)`,
   including the zero test function.
7. Every integer `k`.

The conclusion is exactly

```text
HasCompactSupport
  ((determinantSlice T n k).indicator
    (fun q : LeftUnipotentQuotient n F.Carrier =>
      whittakerNorm ψ W.val q * ‖Φ (quotientLastRow n q)‖))
```

Here the imported constructions have the following representative values:

- `determinantSlice T n k` is the set of cosets `N g` with
  `T.ord (det g) = k`. The published
  `mk_mem_determinantSlice_iff_normalizedAbs` identifies this with
  `|det g| = q^(-k)` for the residue-normalized absolute value and
  `q = T.residueCardinality`.
- `whittakerNorm ψ W.val (N g) = ‖W.val.val g‖` (`whittakerNorm_mk`).
  This is well defined because the standard character has norm one.
- `quotientLastRow n (N g)` is the last row of `g` (`quotientLastRow_mk`),
  which is unchanged by left multiplication by an upper unipotent matrix.

The function inside the indicator is therefore the real-valued function
`N g ↦ ‖W(g)‖ · ‖Φ(η g)‖` with `η g` the last row of `g`.
`Set.indicator` extends it by zero off the slice to the whole quotient.
`HasCompactSupport` asserts that the closure of its support in the quotient
topology is compact. The statement does not assert that the slice itself
is compact.

The field and carrier universes `uF` and `uV` remain independent.
The proposition contains no existential choice; the compact set is not
claimed to be uniform in `W`, `Φ` or `k`.

## Source correspondence and scope

The registered original is H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin–Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, source `jpss-1983-rankin-selberg`,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 385, 404–407 and 410–412 were read visually for this statement.
No source-specific erratum was found among the registered literature
pointers, the Library notes or the project notes.

In §4.2, (4.2.1), p.406, the source writes
`G_r^m = {g : |det g| = q^(-m)}` and integrates over `N_r \ G_r^m`.
Here `r = n + 1`, `η_r g` is the last row of `g`, and the source index `m`
is the integer `k` of this statement. In §4.6, (4.6.4), p.411, the
determinant-slice integral `Ψ^m(W, W'; Φ)` is rewritten as an integral over
`N \ G^m` of `Φ(η g) W(g)` times an inner integral over `Ū_Q`.
Page 412 justifies this step with the sentence: "It is easy to see
(c.f. (4.2)) that the function `W(g)Φ(η_r g)` on `G_r^m` is compactly
supported modulo `N_r`. Thus the integral in (4) is absolutely convergent,
and our step is justified."

"Compactly supported modulo `N_r`" means that the support in `G_r^m`
lies in `N_r C` for a compact set `C`, equivalently that its image in
`N_r \ G_r^m` has compact closure. The function `W(g)Φ(η_r g)` is not
itself left `N_r`-invariant, since `W` transforms by the character `θ_ψ`.
Its absolute value is invariant, and the source's support condition depends
only on where the function is nonzero. The present statement therefore
uses the descended norm `‖W(g)‖ · ‖Φ(η g)‖`, whose support is the image of
the source support. The source works on the slice `G_r^m` alone; extending by
zero to all of `N \ G` changes no support inside the slice, and the slice is
clopen in the quotient (`isClopen_determinantSlice`). Compactness in the
quotient is the source's "modulo `N_r`" condition.

The source's reference to (4.2) is its argument on p.407, (4.2.3). It writes
the torus element as `a = diag(a_1 ⋯ a_r, a_2 ⋯ a_r, …, a_r)`, so that
its source coordinates `a_i` for `i < r` are ratios of adjacent diagonal
entries and `a_r` is the last diagonal entry. Gauge domination of the
Whittaker function bounds the coordinates `a_i` for `i < r` (the source
normalizes the bound as `|a_i| ≤ 1`), and `Φ_i(a_r) ≠ 0` bounds `a_r`.
On a fixed slice the determinant is also fixed, which bounds the diagonal
entries below as well as above.

JPSS §2.1, p.385, defines a representation of Whittaker type as an admissible
representation of finite type whose space of `θ`-equivariant linear forms is
one-dimensional. By §3.1, p.404, all representations of Theorem 3.1, whose
proof contains §4.6, are of Whittaker type, and the function `W` of §4.6
lies in their Whittaker space `𝒲(π; ψ)`. This statement covers a larger class,
derived inside the project rather than taken from the source. It quantifies
every smooth representation, with no admissibility, finite-type,
multiplicity-one, irreducibility or central-character hypothesis. Every
representation of Whittaker type is admissible, hence smooth, so the
source's representations, including reducible ones, are covered. The
statement also allows every functional in the space of standard Whittaker
functionals, including zero. Zero functionals, zero coefficients and zero
test functions make the function inside the indicator identically zero,
and its support is then empty. For `n = 0` the unipotent group is trivial,
and each slice `{g ∈ F^× : ord g = k}` is already compact.

The smooth scope rests on the published theorem
`Langlands.Whittaker.smoothSimpleRootSupport` in
`Langlands.Representation.Whittaker.SmoothSimpleRootSupportProof`, which
proves `Langlands.Whittaker.SmoothSimpleRootSupportStatement`. For every
actual coefficient of a smooth representation it gives one positive bound on
every adjacent diagonal ratio `|a_i / a_(i+1)|` in an Iwasawa factorization
`diag(a) κ`, uniformly over the integral factor `κ`. This replaces the
source's gauge domination. A unipotent-equivariant function that is not an
actual coefficient need not be smooth, so this statement quantifies actual
coefficient images rather than all of `WhittakerFunctions ψ n`.

A prospective proof can combine that bound with
`Langlands.RankinSelberg.exists_schwartzBruhat_row_bound` and the method of
`Langlands.RankinSelberg.normalizedAbs_determinant_le_of_simpleRoot`
from `Langlands.Representation.RankinSelberg.EqualRankSliceSupportProof`.
Write `g = u · diag(t_1, …, t_r) · κ` with `κ` integral and diagonal entries
`t_i`. The last row of `g` is `t_r` times the last row of `κ`, which has a unit
entry, so the compact support of `Φ` bounds `|t_r|` where the integrand is
nonzero. The ratio bounds then bound every `|t_i|` above. Fixing
`|det g| = ∏ |t_i|` bounds every `|t_i|` below. The diagonal parameters
then lie in compact annuli, and up to integral diagonal units they range over
a finite set. The support is therefore contained in the image of a compact
subset of the group. That image is compact, and closed because the quotient by
the closed subgroup is Hausdorff. These steps are proof obligations of a
separate successor and are not established here.

## Boundary of this unit

The proposition adds no compactness, support bound, integrability, quotient
measure, gauge estimate, asymptotic expansion, factor existence or
multiplicativity premise. It involves no measure and states no convergence.
In particular it does not claim that compact support alone proves absolute
convergence of the inner `Ū_Q` integral or of the integral (4.6.4). That
inner integral, together with the source's convergence for `u ≫ 0`, is a
separate input. This statement differs from
`Langlands.RankinSelberg.EqualRankSliceSupportStatement`, which asserts that
integral slice coefficients vanish for all sufficiently negative indices;
compact support on each fixed slice is a different conclusion. The determinant
slice, Whittaker norm and quotient-last-row modules are imported without
changes.
