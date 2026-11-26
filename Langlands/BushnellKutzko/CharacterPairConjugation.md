# Conjugation of subgroup–character pairs

`CharacterPair G` consists of a subgroup `H` of `G` and a group homomorphism
`θ : H →* ℂˣ`. The dependent pair remembers the domain of each character.

`CharacterPair.conj x` takes `(H, θ)` to `(x⁻¹Hx, θˣ)`, where
`θˣ(h) = θ(xhx⁻¹)`. It uses `conjSubgroupEquiv x⁻¹ H` from
[`PairConjugation`](PairConjugation.md), the same subgroup isomorphism used to
transport representations. Its inverse carries elements of `x⁻¹Hx` back to `H`
before applying `θ`. `CharacterPair.AreConjugateBy U` requires a conjugating
element of `U` and equality of the resulting subgroup–character pairs. For
simple characters the subgroup `U` is `U(𝔄)`.

The character convention comes from Bushnell and Kutzko, *The admissible dual
of GL(N) via compact open subgroups* (1993), §3.3, printed p. 104 (PDF p. 116).
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
The use of `U(𝔄)`-conjugacy for simple characters is in Bushnell and Kutzko,
*Simple types in GL(N): computing conjugacy classes* (1994), (2.1)(ii),
printed p. 118 (PDF p. 131). Literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.

The carrier `CharacterPair G` is the subgroup–character type `Langlands.FiniteRep.MonomialTrace.Entry G`.
