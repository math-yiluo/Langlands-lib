# Haar measure in the real Iwasawa chart

`RealLocalIwasawaHaar.RealIwasawaHaarChartStatement` gives the Haar pushforward
formula on the actual group $G=\mathrm{GL}_n(\mathbb R)$ in diagonal, upper
unipotent, orthogonal order. The measures on the groups are Borel measures.
Use the Library's $N$ of upper unitriangular matrices and $K=\mathrm O(n)$,
represented by `unitaryCompact ℝ n`. For $y\in\mathbb R^n$ write
$a(y)=\operatorname{diag}(e^{y_i})$ (`RealIwasawa.torus`).

The first assertion is that for any left Haar measures $\mu$ on $G$, $\nu$
on $N$, and $\kappa$ on $K$, there is a positive constant $c$ such that

\[
 \mu=c\,( (y,u,k)\mapsto a(y)u k)_*(dy\otimes\nu\otimes\kappa).
\]

In the second assertion, use Lebesgue measure in the strictly upper entries
of $u$ in place of the supplied $\nu$. With $z$ the list of these entries,
`(upperEntryCoordinates n).symm z` is the actual element $u(z)$ of $N$.
There is a positive constant, not specified to be the same as in the first
assertion, giving the pushforward of $dy\otimes dz\otimes\kappa$ by
$(y,z,k)\mapsto a(y)u(z)k$.

## Lean proof

The homeomorphism `triangularHomeomorph` sends $(y,u)$ to $a(y)u$ in the
closed subgroup where the orthogonal Iwasawa coordinate is $1$. A left
translation by the point corresponding to $(q,v)$ acts on $(y,u)$ by

\[
 (y,u)\longmapsto (q+y,(a(-y)v a(y))u).
\]

The first component is an additive translation and each second-component
map is a left translation in $N$. The skew-product measure-preserving
lemma and the homeomorphism give left Haar measure on the positive triangular
subgroup. The Library's compact factorization theorem then gives the
pushforward up to scale on $G$, using the Iwasawa decomposition and the
compactness of $K$. Finally, `upperEntryProductMeasure_isHaar` supplies Haar
measure on $N$ by transporting the Lebesgue product in the entries, and
composition of pushforwards proves the entry-coordinate form.

## Source and scope

Hervé Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
`jacquet-2009-archimedean-rankin-selberg`, §3.1 (p. 11, the Iwasawa
coordinates and their use on the quotient), Lemma 3.2 (p. 12, its proof
writes the unipotent measure using strictly upper entries), and §4.7
(pp. 30–31, the square-matrix coefficient zeta integrals that will use
this measure). The pushforward is a derived measure statement; it uses
$a(y)u k$, not $u a(y)k$. The proof adapts the Library's
`ComplexLocalIwasawaHaar` and the entry-coordinate transport of
`ComplexSquareIwasawaEntries` to the real group. It does not fix an exact
Haar normalization, replace the positive diagonal by the full diagonal,
or prove the zeta integral functional equation.
