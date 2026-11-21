# Prime and central heights on the same split primal chart

`IdempotentImageCover.restrictCentralQuasiIsogeny_chartRank` constructs the
actual prime-normalized height function on a test chart. It measures the
section obtained by pulling back the original rigidifier and restricting it
using the two division-image retractions. Its inputs include the actual
uniformizer heights of the central source and target test laws, the scalar
relation `p = u ϖ^e`, and the residue cardinality relation `q = p^l` with
positive `l`.

The integral chart comparisons give scalar-kernel ranks on the centrally
linear division retractions. Rewriting the scalar powers and identifying their
kernel functors gives the prime-normalized ranks on the original retractions.
The published local rank-height theorem then gives a verified height function
for the actual projected prime-local quasi-isogeny.

For every test prime, this function is divisible by `l`. The exact quotient
is a verified uniformizer-normalized height of the evaluated global central
tensor. The proof uses the residue-degree comparison, integral transport, and
the chart-section identity relating this global tensor to the actual local
projection.

The construction gives the chart form of the primal normalization in
Rapoport–Zink, (6.17) and Lemma 6.44, printed pp. 309–310, and Harris 1997,
Appendix, printed pp. 112–113.
