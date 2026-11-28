# Unipotence of shallow standard special fibres of induced tori

Let \(F\) be a nonarchimedean local field and \(S\) an induced torus over
\(K=\texttt{inertiaFixedField}\ F\).
`InducedTorusStandardShallowUnipotentStatement` applies to every real depth
\(0<r<1\) and every smooth affine `IntegralModel` \(M\) of \(S\) over
\(\mathcal O=\texttt{fixedFieldIntegers}\ F\) whose integral-point image
in \(S(K)\) equals `localTorusFiltration F S hS r`. It asserts
`IsUnipotent M.specialFibre` for the whole group scheme obtained by base change
to the residue field of \(\mathcal O\). The scope includes wild ramification and
residue characteristic two.

## Source

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*
(Cambridge University Press, 2023), Proposition B.3.6(2) and its proof,
printed pp. 658–659 (one-based PDF pp. 689–690). The proof uses the
Artinian coefficient algebra of the special fibre of a Weil restriction.
The additive successive quotients of the resulting group filtration give
unipotence by extension. The induced-torus example at depth \(1/3\) has a
special-fibre point of order four in characteristic two. A vector group in
that characteristic has exponent two.
[Induced-torus example](TorusFiltration/RadicalStatement.md)
[Integral Models of Tori](https://doi.org/10.1017/9781108933049.026)

- Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`
- SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`
