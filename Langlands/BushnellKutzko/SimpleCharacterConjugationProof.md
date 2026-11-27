# Transport of simple characters by conjugation: proof

`Langlands.BushnellKutzko.simpleCharacterConjugation` proves
`Langlands.BushnellKutzko.SimpleCharacterConjugationStatement.{uF, uV}`, with the field and the
vector space in independent universes. Fix a simple stratum `S = [𝔄,n,m,β]` with `m ≥ 0` on the
chain `L`, a unit `g`, the linear equivalence `f` given by `g`, and the image chain
`L' = L.linearEquivMap f`. `LatticeChain.corresponds_linearEquivMap` says that `L` and `L'`
correspond under `f` in the sense of `LatticeChain.Corresponds`.

## The order

`L'.order` is hereditary because it is the order of `L'`. Its elements are the conjugates
`gxg⁻¹` of the elements of `L.order`, by `LatticeChain.Corresponds.mem_order`.
`LatticeChain.period_linearEquivMap`, from the module `FundamentalStratumPowerCondition`,
gives equality of periods, since `f` commutes with multiplication by `𝔭_F`.
`LatticeChain.isPrincipal_linearEquivMap` preserves principality, because `f` maps each `L_i`
onto `L'_i` and so preserves the indices `(L_i : L_{i+1})`
(`AddSubgroup.relIndex_map_map_of_injective`).

## The stratum and its groups

The new stratum is `T = Stratum.transport S f L'`. Its chain is `L'`, it has the same `n` and
`r`, and its element is `gβg⁻¹`. It is simple by `Stratum.Corresponds.isSimple_iff`.

The groups use the independence of the lattices from the defining sequence.
`simpleLattices_eq_of_definingSequence` deduces it for a simple stratum with nonnegative index.
It applies part (a) of `simpleStratumLatticeProperties` to the stratum and its defining
sequences moved to index zero by `Stratum.DefiningSequenceChoice.atDepthZero`, which keeps the
tail. Part (a) packages both independence assertions of BK93: for `ℌ` the remark following
(3.1.9), printed pp. 91–92, and for `𝔍` the remark following (3.1.10), printed p. 94.
`simpleHGroup_eq_of_definingSequence` and `simpleJGroup_eq_of_definingSequence` follow. Let
`q` be a defining sequence for `S`, `q'` one for `T`, and `q^g` the image of `q` under
`Stratum.DefiningSequenceChoice.transport`. Then `H^k` of `T` computed from `q'` equals `H^k`
computed from `q^g`. By `LatticeChain.Corresponds.simpleHGroup_eq` this is the image of `H^k`
of `S` computed from `q` under `unitsConj f`. By `map_unitsConj_toLinearEquiv` that image is
`conjugateSubgroup g`. The groups `J^k` are treated in the same way.

## The simple-character pairs

`characterPair_eq_conj` shows the following. Let `θ'` be a character of `gHg⁻¹` with
`θ'(ghg⁻¹) = θ(h)`, that is, corresponding to `θ` in the sense of `CharacterCorresponds`. Then
the pair `(gHg⁻¹, θ')` is `CharacterPair.conj g⁻¹ (H, θ)`, in the convention of BK93 p. 104.

Let `(H, θ)` be a pair of `S` from a defining sequence `q`. Take the corresponding character
`θ'` of the conjugated group from `exists_characterCorresponds`. It is a simple character for
`q^g` by `LatticeChain.Corresponds.mem_simpleCharacters`. Hence `CharacterPair.conj g⁻¹ (H, θ)`
is a pair of `T`.

Conversely, let `(H', θ')` be a pair of `T` from a defining sequence `q'`. Its image `q''`
under `f⁻¹` is a defining sequence for `S`, and the conjugate of the tail of `q''` is the tail
of `q'`. `exists_characterCorresponds_symm` gives a character `θ''` of `H^{m+1}` of `S`
computed from `q''`, corresponding to `θ'`. It is simple by
`LatticeChain.Corresponds.mem_simpleCharacters`, and `(H', θ')` is its conjugate. The variants
`simpleHGroup_eq_of_eq` and `mem_simpleCharacters_of_eq` take the tail and element through an
equation, so that the dependent types of the characters need no rewriting.

## The field invariants

The ramification index and residue degree of `F[gβg⁻¹]` equal those of `F[β]`, by
`elementRamificationIndex_endConj` and `elementResidueDegree_endConj`.

The proof does not use the hypothesis `IsBKAdditiveCharacter ψF` or the finite-dimensionality
hypothesis on `V`; finite-dimensionality follows from the lattice chain where it is needed.

The statement and its sources are those of `SimpleCharacterConjugationStatement`. Bushnell and
Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), §1.1, printed
pp. 20–21, (3.1.7)–(3.1.8), pp. 90–91, the remarks following (3.1.9), pp. 91–92, and
(3.1.10), p. 94, (3.1.14), p. 95, (3.2.3), p. 99, and the character convention, p. 104.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. Bushnell and
Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994), §2, printed p. 118 (PDF
p. 131). Literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
