# Partial cuspidal pair L-functions from completed pole data

Lean module `Langlands.Global.Factors.CuspidalPairPartialContinuation`.

`partialPairContinuationReduction` proves
`PartialPairContinuationReductionStatement.{u,uQ}`. Given the published
absolute convergence of cuspidal pair logarithmic series, the completed
pole statement gives `PartialPairContinuationAt F` over any number field.
The totally complex completed pole statement suffices over totally complex
fields. Both implications keep `u` for the number field and `uQ` for the
attached spectral factors.

`CompletedPoleProfileAt F` packages the witnesses used in the partial
continuation argument. For each pair it gives certified finite L-data,
archimedean parameters, and a completed L-function with its simple pole
profile. `completedPoleProfileAt_of_poleAt` chooses these witnesses from the
fieldwise pole theorem. `exists_partialPairL_of_completedPoleProfile` applies
the continuation argument directly to this data, and `exists_partialPairL`
combines the two steps for callers with the fieldwise pole theorem.

For the fieldwise implication, let `T` and `T'` have unitary central characters
and be trivial on the split centre. Their spectral presentations have
irreducible admissible components at every finite place. Enlarge the omitted
set as needed to contain both exceptional sets. The conclusion supplies a
meromorphic representative `L` of the partial pair L-function outside the
chosen set. For `Re s > 1`, `L(s)` is the exponential of the absolutely
convergent double logarithmic series. It is analytic away from 0 and 1, and
its meromorphic order at 1 is at least −1. That order is nonnegative when
the first realization does not realize the contragredient of the second
with the ranks identified. The witness also has order exactly −1 in the
contragredient case if both the finite and archimedean pair regularity
statements hold. The latter assertions are about germs and so allow different
assigned values at removable singularities.

## Construction and proof

Choose finite local L-data and archimedean parameters using the completed
pole premise. Write `Λ` for the resulting completed function and `G` for the
product of the entire denominators of the archimedean factors and the
finitely many omitted finite factors. Set `L = G Λ`.

On a sufficiently far right half-plane the omitted finite denominators are
nonzero since their constant terms are 1 and `qᵥ^(−s)` tends uniformly to zero
as `Re s` grows. The archimedean denominators are nonzero off their isolated
zeros. At the other finite places the Library's unramified polynomial
comparison identifies the local factors of `Λ` with the Euler factors of the
presentations. Multiplicative splitting over the finite omitted set then
gives equality of `L` with the partial product, which is `exp` of the series
by absolute convergence. For `Re s > 1`, the series is analytic by locally
uniform absolute convergence. In a neighbourhood of a point with real part
`σ`, bound its terms by the summable absolute values at a real point strictly
between 1 and `σ`. The holomorphic identity theorem on the right half-plane
extends the equality with `exp` of the series throughout `Re s > 1`.

Multiplication by `G` preserves analyticity outside 0 and 1 and adds a
nonnegative order at 1. If the two local regularity statements are supplied,
all factors of `G` are nonzero at 1, so the order there equals that of `Λ`.
The completed pole profile gives the exact simple pole in the
contragredient case. The construction gives the lower bound on the order
without either local regularity statement.

## Sources

J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*
(2024), (11.23), printed p. 308 (PDF p. 319), for the completed product,
and Theorem 11.7.1, printed p. 309 (PDF p. 320), for the completed pole
profile. Theorem 11.5.2, printed p. 305 (PDF p. 316), supplies the local
regularity used in the conditional pole preservation. Registered source
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

H. Jacquet and J. A. Shalika, *On Euler Products and the Classification of
Automorphic Representations I*, American Journal of Mathematics **103**
(1981), 499–558. Remark 4.11, printed pp. 553–554 (PDF pp. 55–56), discusses
the partial pole at 1. Theorem 5.3 and its proof, printed pp. 555–557
(PDF pp. 57–59), supply the absolute convergence input and the exponential
identity. The Lean reduction obtains the partial germ by removing factors
from the completed function of Getz–Hahn's theorem. Registered source
`provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`,
SHA-256 `c6b669ccf00a3ce35c10aa60f3dc7538d6269bf279791e5286b893c597275620`.
