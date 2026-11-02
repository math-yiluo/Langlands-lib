# Uniformizer sections and the contracting cones

This module supplies intrinsic definitions needed by the actual-group simultaneous
small-subgroup statements. Its source is Renard, *Représentations des groupes
réductifs p-adiques*, registered 9 July 2026 edition,
`renard-2026-representations-groupes-reductifs-padiques`, V.2.5
(printed 107, PDF 113), V.3.21 (printed 116, PDF 122), and V.3.22–V.3.23
(printed 117, PDF 123). These are the section and cone conventions used in
V.5.2(ii)–(iv), entries S21–S23 of the
[Chapter V source map](../../../../notes/renard/chapter-v-structural-inputs.md).

`cocharacterPoints F A c` evaluates the actual group-scheme homomorphism
`c : Gm → A` on a field unit, through `rationalPoints.map` and the existing
`Gm.affinePointsEquiv`. This is the intrinsic version of
`SplitTorusValuation.cocharacterPoints`; it requires no chosen coordinates or
splitness hypothesis. `latticeSection` uses the *same*
`SplitTorusValuation.uniformizerUnit F` for every `A`, including split subtori of
one another. The two homomorphism laws are proved by the published
`comp_groupHom_zero` and `comp_groupHom_add` evaluation laws.

`CA` is the image subgroup of `c ↦ c(π)` inside the actual `A(F)`. This is
Renard's chosen lifting of the cocharacter lattice, not the whole group `A(F)`.
No arbitrary section or desired compact-subgroup properties are stored as data.
`characterNorm` is the existing `Plancherel.rationalNormCharacters` evaluated on
the actual rational character corresponding to an element of the character
lattice. In particular the norm is the residue-normalized absolute value already
used by the rational-character and positive-valuation interfaces.

For a set `R` of actual characters, `CAplus` imposes norms at most one,
`CAstrict` imposes norms strictly below one, and `CAepsilon R ε` imposes norms
strictly below `ε`. The last definition does not additionally intersect with
`CAplus`: Renard V.3.22 imposes no such extra condition when `ε > 1`.
At the intended standard-parabolic application, `R` is the restrictions to the
actual central split component of the simple roots outside the standard-Levi
index. Supplying arbitrary `R` here makes no claim that it is such a root set.
In rank zero the character conditions are empty, as in the source.

`IsUniformizerLatticeSection` states the retained mathematical obligations:
the section is injective, its actual rational-character valuation pairs with
each character as `latticePairing`, and every rational point has a unique
cocharacter representative modulo the actual common norm kernel.
`SplitTorusUniformizerSectionStatement` universally quantifies over
nonarchimedean local fields and actual split tori, without restricting
characteristic or choosing coordinates. It is a proposition definition and is
not proved here. The public coordinate-torus valuation and uniformizer proofs
in `SplitTorusValuation` motivate this general target; their transport to an
arbitrary actual split torus remains a proof obligation.

This unit supplies the section/cone vocabulary used by S21–S23. It asserts
neither the existence of the S20 simultaneous basis nor contraction or
cofinality. Those statements must apply these definitions to the actual
standard-Levi split components and the fixed geometrically defined `K0`.
Representability and reductivity of the standard Levis, existence of their
compatible central split components, shared KP data and special points, and
the S20–S23 structural proofs remain separate obligations.
