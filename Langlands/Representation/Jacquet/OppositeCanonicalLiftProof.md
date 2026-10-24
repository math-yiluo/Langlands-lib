# Core opposite-radical canonical Jacquet lifts

Author: Worker 322.

The theorem `Langlands.Jacquet.blockOppositeCanonicalLift` proves exactly
`Langlands.Jacquet.BlockOppositeCanonicalLiftStatement` from
`Langlands.Representation.Jacquet.OppositeCanonicalLiftStatement`. It retains
independent universes `uF` and `uV`, every prime `p` and primality instance,
every `F : PadicField p`, supplied `T : F.TopologicalData`, natural rank `n`,
block shape `B`, and complex module carrier `V`. The statement and all imported
Lean/Markdown pairs are unchanged.

## Exposed results

All names below are in `Langlands.Jacquet`, with arguments `F T B V`.

| Theorem | Conclusion |
| --- | --- |
| `blockOppositePowerKernelJacquet` | The exact `BlockOppositePowerKernelJacquetClause` |
| `blockOppositeStableImageJacquetBijective` | The exact `BlockOppositeStableImageJacquetBijectiveClause` |
| `blockOppositeStableImageJacquetMap_bijective` | Pointwise bijectivity of the actual opposite stable-image Jacquet map |
| `blockOppositeCanonicalLift` | The published conjunction, in its original order |

The pointwise theorem explicitly quantifies `ρ`, `hAdmissible`, `K`, `hK`,
the block Iwahori factorization, `a`, and its upper strict-contraction proof.
Its domain is the existing all-power `stableImage` of normalized compression
at `(B.blockScalar F.Carrier a)⁻¹`. Its codomain is the existing fixed submodule
of the opposite coinvariants, for the **unnormalized** action of the same
embedded Levi and the actual subgroup `K.toSubgroup.comap M.subtype`.
It is a direct application of the proved bijectivity clause.

## Implemented transport argument

Both clauses install precisely `T.topology` and
`T.generalLinearTopologicalGroup n`. Fix the data quantified by a clause, and
write

- `e := T.generalLinearInverseTranspose n`;
- `K' := K.comap e.toMonoidHom e.continuous`;
- `ρ' := ρ.comp e.toMonoidHom`;
- `s := B.blockScalar F.Carrier a`;
- `N := B.unipotentSubgroup F.Carrier`,
  `Nop := B.oppositeUnipotentSubgroup F.Carrier`, and
  `M := B.leviSubgroup F.Carrier`.

These are local abbreviations of existing constructions, with no new carriers.
The published `inverseTranspose_compact_comap` supplies compactness of `K'`.
The published `inverseTranspose_iwahoriFactorization` gives the original
`HasBlockIwahoriFactorization T K'` for the same shape and chamber.
`Subgroup.map_comap_eq_self_of_surjective`, applied to surjectivity of `e`,
gives the actual image equality `K'.toSubgroup.map e.toMonoidHom = K.toSubgroup`.
The existing `isAdmissible_comp_continuousMulEquiv` gives admissibility of `ρ'`.
Its smoothness witness is the one required by the transport results, up to
Lean's proof irrelevance.

For the kernel clause, apply the published `blockPowerKernelJacquet` to `ρ'`,
`K'`, and the original tuple `a`. This proves

`powerKernelSup ρ' K' s = ker (fixedJacquetMap ρ' N M K')`,

with the smoothness, compactness and normalizer proofs understood. Apply the
forward implication of `powerKernelSup_eq_ker_groupTransport` to this equality.
The two required subgroup image identities are the published
`inverseTranspose_unipotent_map` and `inverseTranspose_levi_map`, identifying
the images with `Nop` and `M`. Use the existing normalizer inclusions for both
radicals. The resulting equality is the actual opposite quotient-kernel
identity for `ρ`, `K`, and `e s`. Finally,
`inverseTranspose_blockScalar` gives `e s = s⁻¹`; rewriting this equality
produces the exact opposite kernel clause.

For the bijectivity clause, apply the published
`blockStableImageJacquetBijective` to the same pulled-back admissible data.
The forward implication of
`stableImageJacquetMap_bijective_groupTransport`, with the same subgroup image
equalities and normalizer inclusions, transfers this result to the actual
opposite `stableImageJacquetMap` at `e s`. Rewriting `e s = s⁻¹` also rewrites
the dependent stable-image domain and yields precisely the requested map.
The generic transport theorem identifies both the quotient map and its actual
fixed-vector codomain; no replacement quotient or abstract isomorphism is used
as the conclusion.

The closing theorem pairs the two named clause proofs. The argument reuses the
published upper results, including their finite-dimensional stabilization
argument, without repeating those proofs or assuming their conclusions.

## Provenance and scope

This is an internal derived proof using the upper canonical-lift proofs and the
independently published inverse-transpose and group-transport proofs. The
mathematical motivation of the target is Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III: *Induced representations and the
Jacquet module*, revision April 29, 2019, sections 4–6, especially III.5.4–III.5.5
on pages 6–7. The registered source is `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`, retained at
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
The original was read during preparation; no applicable project errata was
found. The inverse-transpose proof route is an internal specialization, not a
verbatim proof from that source. The source's unnormalized coset-sum operator
is not substituted for the project's normalized compression. This proof uses
the published normalized upper theorems and exact normalized-average transport.

There is no added finite-dimensionality assumption on `V`, no positive-rank,
proper-parabolic or nonzero-representation restriction, and no chosen lift or
canonical-lift conclusion among the hypotheses. The original upper strict tuple
is retained; strict contraction of its inverse is not assumed. Rank zero, empty
and one-block shapes, and the zero representation remain included. The module
adds no axioms and uses only `propext`, `Classical.choice`, and `Quot.sound`.
Nested-average compatibility and the final pairing are separate obligations.
Their reusable averaging and pointwise transport results remain available from
the imported `CanonicalLiftGroupTransportProof` module.
