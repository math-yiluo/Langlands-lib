# NYLL transfer norm witness

Worker 196, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Source module: `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean`.

| Unit | Source declaration | Adapted declaration | Source lines |
| --- | --- | --- | --- |
| `M071.022` | `ClassFormation.transferNormNaturalityNormWitness` | `Langlands.NYLL.ClassFormation.transferNormNaturalityNormWitness` | `675–695` |

## Meaning

The definition returns an actual element of `A_L`. It sums the quotient
representation translates of the input, indexed by the chosen right transversal
of the intermediate inclusion range, then transports the sum back to `A_L`
through M071.014. It retains local `H`, `T`, `H.FiniteIndex`, the Fintype
obtained from `T.2.finite_right.fintype`, the quotient representation `E` and
the additive equivalence `eA`, exactly as in the source.

Its telescope keeps implicit universe-zero `G`, group and topology instances,
explicit `A`, `K K' L`, `hLK'`, `hK'K`, then both named normality instances,
the instance `Finite (K/L)` and the input `a : A_L`. It adds no injectivity,
norm-identity or finiteness assumption on `G` itself.

## Modifications

Prefix the `ClassFormation` namespace with `Langlands.NYLL`. Replace broad
source imports with the focused imports in the Lean file. The abbreviation
`CyclicCohomology.extensionSubgroup K L hLK` is expanded to its exact Mathlib
body `L.toSubgroup.subgroupOf K.toSubgroup`, from
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54, as
permitted by the task. Every containment proof remains in the telescope even
where the expansion makes it unused. Extra grouping parentheses have no effect
on elaboration. No new global instance is introduced.

The source-private `chosenTransferNormNaturalityRightTransversal` call is
renamed to its required public internal adaptation `PortInternal.M071.d017`
(M071.017, source lines 576–583). Its chosen set and certificate remain exactly
the source's. The M071.001/.004 intermediate construction and M071.014
equivalence are supplied by their focused companion modules. All local
instances remain local and the original noncomputable declaration is retained.
The source docstring describes the intended norm property; the construction
itself supplies the element, and proving the norm property is a separate task.
Unrelated declarations and theorem proofs are omitted.

## Validation and scope

Development check `99d90ae7-cc11-413f-8e64-9e8cd3cf2741`, in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, compiled this module together with a
private comparison module. The latter reconstructs the source constants with
the original extension-subgroup abbreviation and checks equality of the entire
unapplied constants by `rfl`, preserving the full telescopes as well as bodies.
This is a development check, not independent semantic acceptance.

The whole-constant comparison reconstructs M071.014 before M071.022 and
uses the separately source-compared M071.017 adaptation for the private name.
The norm identity in M071.024 and all reciprocity proofs remain separate
obligations; this data definition does not prove them.

Integration reuses the identical fixed-carrier equivalence `extensionFixedRepresentationEquiv` from M073.001 for the source's M071.014 call. The underlying additive equivalence and the norm witness construction are unchanged.
