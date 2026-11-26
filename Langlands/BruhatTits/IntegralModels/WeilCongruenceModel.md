# An integral model for congruent units of a Weil restriction

Let \(A\) be a principal ideal domain with fraction field \(K\). Let \(C\)
be a commutative finite free \(A\)-algebra, and let \(J\) be an ideal of \(C\)
containing the image of a nonzero scalar of \(A\). The Weil restriction of
\(\mathbb G_m\) from the coefficient algebra of congruence pairs has a split
map to the Weil restriction from \(A\) itself. Both maps are induced by the
literal maps of coefficient algebras on tensor-valued units. The section
induces a retraction onto the scheme-theoretic kernel. The kernel is affine
and smooth by `AffineRetractGeometry.smooth_of_retract`. After base change
to each field the retraction is a surjection from the connected ambient
Weil restriction. Thus the kernel has geometrically connected fibres.

`WeilCongruence.integralModel` packages this kernel as an `IntegralModel` of
the Weil restriction from the generic coefficient algebra \(B\), given an
identification \(K\otimes_A C\simeq B\). The congruence-pair algebra becomes
\(K\times B\) on the generic fibre. Its first projection has kernel exactly
the second Weil factor, as seen on the tensor-valued unit groups. The map
`WeilCongruence.toAmbient` compares the kernel model to
`WeilGm.integralModel` by the second coefficient projection, with the
identity on the generic group.

`WeilCongruence.mem_integralPoints_iff` computes the literal image of
integral sections. A section of the kernel corresponds to a pair of units
\((1,w)\) with \(w\in C^\times\) and \(w-1\in J\). Its generic point has
unit coordinate given by the image of \(1\otimes w\) in \(B\). Conversely,
the pair \((1,w)\) gives an actual section for every such unit.

This is a coordinate route to the Weil restriction construction in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition
B.3.6(1), printed p. 659 (one-based PDF p. 690). The model uses the ideal of
coefficient differences directly. For a principal congruence ideal this is
the usual multiplicative congruence parameter, with the product induced by
multiplication of the units in the second coordinate.

- Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`
- SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`
