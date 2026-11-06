# The single-block assembly witness of a zero-monodromy parameter

Author: Worker 1700.

Henniart 2002, §2.9 (printed p. 596, PDF p. 10), states that the assembled map
`π` satisfies `π(σ) = π_0(σ)` for every irreducible Weil class `σ`. In the
assembly relation of `AssemblyRelation`, this is the case `r = 1`, `m = 0`: the
zero-monodromy parameter `σ ⊗ Sp(1)` and the one-element multisegment
`{[c0 σ]}`, whose Langlands head is `St_1(c0 σ) = c0 σ` (§2.6–2.7).

This module proves that witness. It uses no unproved statement. It does not
prove `AssemblyExtendsStatement`, which also requires every irreducible Weil
class to have a zero-monodromy parameter class. That existence is neither
assumed nor proved here: the zero-monodromy class `D` is a hypothesis.

## Main results

- `isAssembledFrom_of_isZeroMonodromyOf F c0 h`: if
  `IsZeroMonodromyOf F σ D`, then
  `IsAssembledFrom F c0 D (supercuspidalToAutomorphic F (c0 n σ))`. The map
  `c0` is an arbitrary supercuspidal map.
- `assembly_apply_of_isZeroMonodromyOf F hwd hc h`: assume
  `AssemblyWellDefinedStatement F` as the hypothesis `hwd`. Then every assembly
  `c` of `c0` satisfies `c n D = supercuspidalToAutomorphic F (c0 n σ)` on the
  zero-monodromy class `D` of `σ`. This is the uniqueness part of
  well-definedness, applied to `c n D` and to the witness above.

## Parameter side

- `WeilDeligneRepresentation.directSumConstFinOneEquiv A`: the direct sum of the
  constant family `Fin 1 → A` is equivalent to `A` as a Weil–Deligne pair. The
  linear map is Mathlib's `DirectSum.lid`, which evaluates at the unique
  index. The action and the monodromy are componentwise, so both commute with
  it.
- `WeilDeligneRepresentation.Special.raising_one`: on the special block of
  length one, the raising monodromy is zero.
- `WeilDeligneRepresentation.blockOneLinearEquiv A` sends `v ⊗ w` in
  `A ⊗ K^1` to `w 0 • v`. `blockOneEquiv ν A` makes it an equivalence of
  pairs from `block ν A 1` to `zeroMonodromy ν A`. The weight of the single
  coordinate is `ν^0 = 1`, so the action matches. The block monodromy is
  `0 ⊗ 1 + 1 ⊗ raising`, which is zero, so the monodromy matches.
- `isBlockSum_of_isZeroMonodromyOf`: a zero-monodromy certificate
  `(A, hA, hD)` for `D` gives `IsBlockSum` with one block, length `0 + 1`,
  representative `A`, and the composite of the two equivalences above.

## Representation side

`T` is the canonical topological data of `F`, and `ρ` is a supercuspidal
representative `S` of `c0 σ`, of rank `k + 1`.

- `TopologicalData.castRankEquivOfEquiv`: if `X` is equivalent to the published
  rank transport `castRank h' Y`, then `castRank h X` is equivalent to `Y`. The
  proof substitutes the rank equality.
- `isSegmentHead_single`: `T.segmentInduced S.obj 1` is a segment head of the
  segment `segmentOf F c0 σ 0` of length one. The published
  `singletonSegmentInducedEquiv` identifies it with a rank transport of `S`,
  which is irreducible (`isIrreducible_castRank`). An irreducible
  representation is its own irreducible head
  (`Classification.isIrreducibleHead_self`).
- `singleSegmentDatum F c0 σ π` is the `SegmentProductDatum` with one segment
  `segmentOf F c0 σ 0` and block `π`. Its multisegment is literally
  `multisegmentOf F c0 (fun _ => σ) (fun _ => 0)`
  (`singleSegmentDatum_multisegment`), and it is precedence-ordered because
  it has one segment (`singleSegmentDatum_isPrecedenceOrdered`).
- `singleSegmentDatumInducedEquiv`: the published one-block equivalence
  `singleBlockNormalizedProductEquiv`, followed by `castRankEquiv`, identifies
  the induced representation of the datum with a rank transport of its block.
- `isMultisegmentHeadClass_single`: choose `S` with class `c0 σ` and take the
  block `π_1 = i(S)`. The induced representation `J` of the datum is
  irreducible by the preceding equivalence, so it is its own Langlands head.
  `J` is equivalent to `S` by composing the two rank transports
  (`castRankEquivOfEquiv`). The automorphic object `S.toIrreducibleAdmissible`
  has class `supercuspidalToAutomorphic F (c0 σ)` by the definition of the
  forgetful class map.

## Provenance

This is an internal supporting module. The construction is Henniart's single
indecomposable case: §2.2 decomposes parameters into blocks `ρ ⊗ Sp(n)`, §2.6
defines `St_n(ρ)` as the unique irreducible quotient of
`i(ρ, νρ, …, ν^(n-1) ρ)`, and §2.9 records `π(σ) = π_0(σ)` for
`σ ∈ G_0`. The Lean proofs use only the published definitions and lemmas
cited above.
