# Smooth integral models of induced tori at shallow positive depth

`Langlands.BruhatTits.IntegralModels.InducedTorusShallowModelStatement`
expresses the model-existence clause of Kaletha–Prasad, Proposition B.3.6(1), over
the maximal unramified extension at depths \(0<r<1\). Let \(F\) be a
nonarchimedean local field, \(K=\texttt{inertiaFixedField}\ F\), and
\(\mathcal O=\texttt{fixedFieldIntegers}\ F\). For an induced \(K\)-torus \(R\)
and such a depth \(r\), the proposition asks for an `IntegralModel` with generic
group `R.toGrp`, a smooth structural morphism, and geometrically connected
fibres. The structure includes affineness, flatness, finite type and the
specified generic-fibre isomorphism. The image of its \(\mathcal O\)-sections in
\(R(K)\) equals `localGeometricCharacterCongruence F R r` as a subgroup.

That subgroup uses all characters over the fixed separable closure, with the
additive valuation normalized by the order on \(F\). On an induced torus,
`localTorusFiltrationAtSplitting_eq_geometric_of_induced` identifies the
positive-depth subgroup with the same character test intersected with the
norm-defined Iwahori subgroup. The proposition allows wildly ramified factors,
residue characteristic two and the trivial torus.

## Source

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge
University Press, 2023). Proposition B.3.6(1) and its proof, printed pp. 658–659
(one-based PDF pp. 689–690). The proof works over \(K\), reduces by products to
\(R_{E/K}\mathbb G_m\) for finite separable \(E/K\), and restricts the
multiplicative congruence model from the integers of \(E\). The statement here
takes the model-existence clause in the shallow positive range.

- Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`
- SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`
