# Transport of simple characters by conjugation

For a simple stratum `[𝔄,n,m,β]` at `m ≥ 0` and `g ∈ Aut_F(V)`,
`SimpleCharacterConjugationStatement` uses `LatticeChain.linearEquivMap` for
the chain with lattices `gLᵢ`. Its order is `g𝔄g⁻¹`, is hereditary, has the
same period and is principal when `𝔄` is principal. The stratum
`[g𝔄g⁻¹,n,m,gβg⁻¹]` is simple. Its `H^k` and `J^k` are the conjugates by
`g` of the old groups for every `k ≥ 0` and every pair of defining
sequences. Its character pairs are the image of the old set under
`CharacterPair.conj g⁻¹`. The inverse here implements the character
convention of BK93 p. 104, giving the domain `gH^{m+1}g⁻¹`. Conjugation also
preserves the ramification index and residue degree of the generated field.
The base is an arbitrary nonarchimedean local field, with `V`
finite-dimensional and `ψ_F` satisfying `IsBKAdditiveCharacter`.

This is transport of the constructions used in BK93 and BK94 without a
separate numbered result in either source. Linear transport of the lattices
gives transport of the endomorphism filtration and the adjoint lattices.
It also identifies the generated fields over `F`. The group and character
transports use the defining-sequence constructions and invariance of the
trace and relative determinant under change of coordinates.

Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), §1.1, printed pp. 20–21, (3.1.7)–(3.1.8), pp. 90–91, (3.1.14),
p. 95, (3.2.3), p. 99, and the character convention, p. 104. Literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes*
(1994), §2, printed p. 118 (PDF p. 131). Literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
