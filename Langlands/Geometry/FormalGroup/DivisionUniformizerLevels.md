# Published division levels in a uniformizer coordinate

For a scalar field `k` and a finite-dimensional division algebra `D`
over `k` with the hypotheses of the Library's `LocalDivisionLevels`, choose
an ambient unit `Π` with regular norm less than one. At a positive
integer `N`, `uniformizerLevel` is the published `congruenceLevel`
at radius `|Π|^N`.

`mem_uniformizerLevel_iff` identifies its elements with the ambient
units of the form `1 + Π^N x` for `x` in the published integer ring.
The forward direction takes `x = (Π^N)⁻¹(g-1)`. Multiplicativity of
the norm gives the integer bound. Conjugation preserves the norm
of `g-1`, so the subgroup is normal in the full division-unit group.
It lies in the maximal compact level. Its quotient inside that level
is finite by openness and compactness.

Harris 1997, §2, printed p. 88 (PDF page 14), writes the congruence
subgroup using the `N`-th power of the central maximal ideal of `O_F`.
The Appendix, printed p. 113 (PDF page 39), chooses a division unit
`Π` whose `d`-th power is a central uniformizer. The theorem
`uniformizerLevel_pow_subgroup` identifies the level with the central
uniformizer at exponent `N` with the level with `Π` at exponent `d * N`.
The group quotient here is one ingredient of
the Galois group in the level construction on printed pp. 115–116
(PDF pages 41–42).
