# Norm characters using the actual residue cardinality

Authored by Worker 53. This construction uses the actual residue field of
an accepted `PadicField.TopologicalData`, and specializes to the accepted
canonical constructor for every finite extension of every `Padic p`.
The prime has the sole constraint `[Fact p.Prime]`. The field carrier
universe `u` and the group carrier universe `v` are independent.

`residueCardinalityUnit T` constructs a nonzero complex unit from
`T.residueCardinality = Nat.card T.ResidueField`. The proof installs only
the topology, valuative relation and local-field certificates already present
in `T`. Mathlib then supplies finiteness of the actual residue field. Its field
structure gives nonemptiness, so `Nat.card_pos` justifies the nonzero natural
cast. There is no arbitrary scalar `q` or finiteness assumption in this
constructor, and no global instances are installed.

For any explicitly supplied continuous integer degree `d`, the constructed
`residueNormCharacter T d` is the continuous character with degree-one value
`(T.residueCardinality : ℂ)⁻¹`. The target carries the usual complex units
topology. Its complex value at `w` is exactly the actual residue cardinality
raised to the negative integer degree. It is trivial on `ker d`.
The degree-one and degree-minus-one evaluation lemmas expose both sign
conventions.

`canonicalResidueNormCharacter F d` uses `F.canonicalTopologicalData` and
therefore takes no chosen topological realization as a hypothesis. It is
available for every algebraic p-adic field in the accepted interface.
The degree is still supplied: the actual local residue-Galois map and its
finite-field Frobenius comparison belong to the separate local assembly.
These characters alone do not supply an actual local Weil group or a
geometric Frobenius lift.

## Source correspondence

This is the actual-residue specialization of the formulas documented in
`DegreeCharacters.md`. Tate, *Number theoretic background* (Corvallis, Part II,
1979), §1.4.1, printed p. 6 / PDF p. 15, defines `q` as the actual residue
cardinality and sends uniformizers to inverse Frobenius with norm `q⁻¹`.
Sections 1.4.6, printed p. 7 / PDF p. 16, and 4.1.3, printed p. 20 /
PDF p. 29, give the norm and negative-degree convention.
These original pages were read. Literature ID
`tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The bundled constructors and their short typeclass and evaluation proofs
are internal derived content, not additional arithmetic theorems.

## Dependencies and authorship

The accompanying `Langlands.Weil.Local.DegreeCharacters` is authored by
Worker 53. Its sole project import is the accepted generic pullback.
The additional exact published project definitions are:

| Module | Artifact, version | Original author |
| --- | --- | --- |
| `Langlands.LocalField.Definitions` | `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, v1 | Worker 1 |
| `Langlands.LocalField.Normalization.Definitions` | `e3d7bbd4-f2b9-4970-a60f-bf6aa0b34bb2`, v1 | Worker 27 |
| `Langlands.LocalField.Canonical` | `c342ec21-e5ee-4ba4-aec6-b4c1b1e2b629`, v1 | Worker 26 |

The normalization pair has Lean SHA256
`b997a64a0f59ce13d45e2b5349de9ad87466a5e2d3e16ab3f1a4ef97a048214b`
and Markdown SHA256
`dac7d3aeb5229c505e5271f66d7decf6c7c4404853e9f15a363b4f9401902436`,
published at `9db46907db3181b0c1dfd287b8ab2f1f02054cab`, receipt
`5d095fa472fd49acb7a360c6f2ade9de`.
The canonical pair has Lean SHA256
`e702bb7808fc344bda47a3093d9438d5cda71dcb165be7110be7b393f61d7c48`
and Markdown SHA256
`94a7a93a2ac19a6c106542cd76530caf8244892f29b98eea8755b031ec7e872d`,
published at the same commit, receipt `24df660d770545809d3f2ad0d607c9bb`.
Both were fetched and confirmed accepted, published, and current at Library
commit `5bc58c2525e0499012801c80f17b6a9c04d57263`.

Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, pins
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The finite-residue instance is reused from Mathlib's nonarchimedean-local-field
interface; its general theory is not reproved. This pair remains a development
contribution pending independent semantic review and publication.
