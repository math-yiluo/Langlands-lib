# Common CM bases for the two sides of a cyclic step

`Langlands.Global.HenniartCyclicCommonBaseRealizationStatement.{uK}` is a
proposition for every prime `p`, cyclic prime-degree step `S` over `ℚ_[p]`,
and independently chosen finite extension bounds `B` of `S.base` and `T` of
`S.top`. The local fields may lie in any universe `uK`. All number fields
in the statement and its paired-place configurations lie in `Type`.

It asserts the existence of CM number fields `E/F` with `IsGalois F E` and
`Module.finrank F E = S.degree`. There is a finite place `v` of `F` and a
unique place `w` of `E` above `v`, both of residue characteristic `p`. The
ring isomorphisms `ι : F_v ≃+* S.base.Carrier` and
`κ : E_w ≃+* S.top.Carrier` are continuous in both directions for the
canonical local topologies. They identify the completion map with the
specified local embedding via the equation
`κ (FiniteExtension.completionMap v w.1 x) = S.embedding (ι x)` for every
`x : F_v`.

`Langlands.Global.Harris.HasCommonBaseConfigurations K B v ι` fixes a CM
number field `F`, a finite place `v`, and a comparison `ι` of `F_v` with
`K`. For each `B'` with `B'.field ≤ B.field` in the chosen algebraic closure
of `K`, it asks for an `IsPairedPlaceConfiguration` over `F` whose first
place datum `P` has `P.v = v`. For each `x : F`, the image of `x` under
`P.iso` after embedding into `F_{P.v}` must equal its image under `ι` after
embedding into `F_v`. The proposition requires this predicate both over
`F` at `v` for `B` and over `E` at `w` for `T`, with the comparisons `ι`
and `κ` from the completion square.

## Provenance

The simultaneous assertion extends the construction behind
`HenniartCommonBaseRealizationStatement`. Embed the normal closures of both
bounds in a single finite Galois extension of `ℚ_[p]`, choosing the
embeddings to agree on `S.base` via `S.embedding`. The preimages of the two
local fields in one CM rational Galois model give the two base number
fields. The compatible embeddings determine the two places and the
commuting completion maps. The Galois comparison gives the degree of the
global step, and equality of the local and global degrees gives uniqueness
of the upper place. The single-base construction
`CMRealization.pairedPlaceConfiguration_of_le` accounts for the paired-place
families at those same places. [Single-base construction](HenniartCommonBaseRealizationProof.md)

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique*, Invent. Math. 139 (2000), §3.3, p. 449. One CM
  model gives the common base and the local Galois comparison. Registered
  source `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), §4, pp. 200–201. The setup supplies
  the two conjugate pairs of places and the compatible completion
  identifications. Registered source `harris-1998-local-langlands`, SHA-256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
