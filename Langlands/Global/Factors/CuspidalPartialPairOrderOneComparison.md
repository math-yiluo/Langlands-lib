# Order transfer from a shifted completed cuspidal pair L-function

`Langlands.Global.CuspidalPartialPairOrderOne.completedOrder_eq` compares a supplied partial
pair L-function `L` with a supplied completed pair L-function `Λ`. The partial product uses
the original presentations and an arbitrary finite set `S` containing both exceptional sets.
The completed product uses the certified finite factors and the actual real and complex
parameters of two unitary cuspidal realizations of the same respective ranks. The auxiliary
presentations may lie in a different universe from the original presentations. The lemma
assumes that their Euler factors at `s + d` match those of the original presentations at
`s` outside `S`, where `d.re = 0`. Its conclusion is
`meromorphicOrderAt L 1 = meromorphicOrderAt Λ (1 + d)`.

On the common right half-plane, `Finset.hasProd` and `HasProd.mul_compl` attach the factors
at `S` to the product defining `L`. Uniqueness of the product identifies `Λ(s + d)` with
`L(s)` multiplied by those finite factors and the shifted archimedean product. The local
factor denominators are entire, so the products involved are meromorphic. The half-plane
identity theorem gives equality of their punctured germs at `1`.

The shifted point `1 + d` has real part `1`. Two Library theorems give nonzero
denominators there: `cuspidalFinitePairRegularity` at the finite places, and
`Automorphic.cuspidalArchimedeanPairRegularity` at the real and complex places. The
archimedean theorem is the absolute convergence of the archimedean pair factors for
`Re s ≥ 1` that Getz–Hahn (2024) invoke on printed p. 309. The inverses of these
denominators are holomorphic and nonzero at that point. The
`PoleComparison.finiteOmittedOrder` lemma removes their contributions to the order at `1`.
Translation then identifies the order of `s ↦ Λ(s + d)` at `1` with the order of `Λ` at
`1 + d`.

This is an internal comparison for the completed-function route to Arthur–Clozel (1989),
III.2 (2.2)–(2.3), printed p. 200 (`arthur-clozel-1989-base-change`). The partial boundary
assertions there come from Jacquet–Shalika (1981), *On Euler Products and the Classification
of Automorphic Forms II* (`jacquet-shalika-1981-euler-products-ii`): Proposition (3.3),
stated on printed p. 795 with its proof on pp. 795–802; Proposition (3.6), pp. 802–804; and
Theorem (3.7), p. 804. The Lean comparison uses local regularity and
an equality of genuine Euler products to transfer whatever completed order is supplied.
The archimedean source is Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), §11.7, printed p. 309 (`getz-hahn-2024-automorphic-representations`).
