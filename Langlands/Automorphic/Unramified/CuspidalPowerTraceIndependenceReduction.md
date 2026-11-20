# Cuspidal trace independence from logarithmic asymptotics

Lean module `Langlands.Automorphic.Unramified.CuspidalPowerTraceIndependenceReduction`.
The proof adapts Worker 3657’s shared draft for Task 6446, revision 7.

`CuspidalPowerTraceIndependenceReductionStatement.{uF, uV}` assumes the
published `CuspidalPairAbsoluteConvergenceStatement`. It gives two
implications. The fieldwise limit `CuspidalPairLogAsymptoticsAt F` for every
number field implies the published `CuspidalPowerTraceIndependenceStatement`.
The same limit for every totally complex number field gives
`CuspidalPowerTraceIndependenceTCStatement`. Both implications retain the
original field universe `uF` and the independent spectral factor universe
`uV`. The analytic absolute convergence and boundary limits are premises of
this reduction.

## Proof

For each supplied system, choose an actual cuspidal realization and an
attached presentation. The norm-power normalization from
`CuspidalNormPowerTwist` writes the realization as a determinant twist of one
trivial on the split centre, with a complex exponent `λᵢ`. The normalized
realization and its conjugate have unitary central characters, and the conjugate
realizes the contragredient. A complex exponent removes the unitary phase as
well as the real power. Consequently, differences of imaginary parts enter as
vertical shifts in the logarithmic sums. Jacquet and Shalika use real powers
of the norm with no split-centre triviality imposed on the unitary parts.

Choose presentations of the normalized realizations and their conjugates
with all finite local factors irreducible and admissible, using the irreducible
admissible finite slice, its tensor presentation and `exists_small` to reach
`uV`. Enlarge the exceptional set to contain the auxiliary presentations and
the determinant-twist exceptional sets. The direct comparison of two spectral
presentations of one realization identifies the traces after twisting. At each
remaining place, the original positive power trace equals the normalized power
trace times `qᵥ^(−k λᵢ)`.

If any coefficient is nonzero, choose `i₀` with least `Re λᵢ` in their support.
Multiply the relation at each place and power by the conjugate representation's
power trace for `i₀` times `qᵥ^(−k(σ − λᵢ₀))/k`. For real `σ > 1`, absolute
convergence justifies summation over places and positive integers and
interchanging the finite coefficient sum with this sum. The result is a zero
linear combination of pair logarithmic series at `σ + λᵢ − λᵢ₀`.

Divide this identity by `log(1/(σ−1))` and let `σ` decrease to 1. For a strictly
larger real part, absolute convergence at `1 + Re(λᵢ − λᵢ₀)` gives a uniform
bound by summing norms, so the normalized term tends to zero. When the real
parts are equal, apply the boundary limit with `θ = Im(λᵢ − λᵢ₀)`. A nonzero
limit requires `θ = 0`, equal ranks, and the conjugate of the `i₀`th normalized
realization to realize the contragredient of the `i`th. The latter is equivalent
to the conjugate of the `i`th by contragredient uniqueness. Undoing conjugation
and the common determinant twist gives equality of the original full classes.
Injectivity forces `i = i₀`. The finite sum therefore tends to the nonzero
coefficient at `i₀`, contradicting the zero identity. The argument covers empty
families since the contradiction starts with a nonzero coefficient.

## Sources

H. Jacquet and J. A. Shalika, *On Euler Products and the Classification of
Automorphic Forms II*, American Journal of Mathematics **103** (1981),
777–815. Theorem 4.1, printed pp. 805–806 (PDF pp. 30–31), gives the
logarithmic normalization. Theorem 4.2, printed pp. 806–807 (PDF pp. 31–32),
uses the unitary twist in (1), the twisted traces in (4) and the summation and
limit in (5)–(7). The split-centre normalization and the vertical shift adapt
those steps to the Library's completed pair L-function convention. Registered
source `jacquet-shalika-1981-euler-ii`, SHA-256
`4d3f68841a558631a1624482d497665c2b52059bb9e0b7333948b8d1610b57d8`.

The absolute convergence input is Jacquet and Shalika, *On Euler Products and
the Classification of Automorphic Representations I*, American Journal of
Mathematics **103** (1981), 499–558, Theorem 5.3 and its proof, printed
pp. 555–557 (PDF pp. 57–59). Registered source
`provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`,
SHA-256 `c6b669ccf00a3ce35c10aa60f3dc7538d6269bf279791e5286b893c597275620`.
