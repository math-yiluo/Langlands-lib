# Finite-cyclic Tate boundary homology

Port author: Worker 170. Original author: Naganori Yamaguchi (assisted by
OpenAI Codex). The construction imports Worker 170's published M003.001
boundary comparison and Worker 45's published degree-minus-one comparison.
No unreviewed draft or patch is copied.

## Exact data and parameters

This module defines the following actual categorical isomorphisms:

| Source unit and declaration | Adapted declaration | Result |
| --- | --- | --- |
| M003.002, `TateCohomology.isoFiniteCyclicZero`, lines 52–86 (definition at 54) | `Langlands.NYLL.TateCohomology.isoFiniteCyclicZero` | `tateCohomology A 0 ≅ (Rep.FiniteCyclicGroup.normHomCompSub A g).homology` |
| M003.003, `TateCohomology.isoFiniteCyclicNegOne`, lines 88–136 (definition at 90) | `Langlands.NYLL.TateCohomology.isoFiniteCyclicNegOne` | `tateCohomology A (-1) ≅ (Rep.FiniteCyclicGroup.subCompNormHom A g).homology` |

Both preserve the source parameter order and binder kinds:

```lean
{R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
(A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
```

There is one arbitrary universe `u`, shared by the coefficient ring, group
and representation. The representation, chosen generator and its generation
certificate are explicit. The conclusions are data in `ModuleCat R`, with
forward and inverse morphisms and their two inverse laws.

Here `N` is the representation norm, the sum of the actions over all group
elements. The first target is Mathlib's actual short complex
`A --N--> A --(ρ(g) - 1)--> A`; the second is
`A --(ρ(g) - 1)--> A --N--> A`. The left sides are Mathlib's actual Tate
cohomology objects. The intermediate quotient presentations below are used
to construct comparisons with the required homology objects.

## Implemented degree-zero construction

Set

```lean
S := ShortComplex.mk A.norm.toModuleCatHom (groupCohomology.d₀₁ A)
  (Rep.norm_comp_d_eq_zero A)
T := Rep.FiniteCyclicGroup.normHomCompSub A g
```

The published definition
`Langlands.NYLL.TateCohomology.isoZeroBoundary A` already identifies
`tateCohomology A 0` with `S.homology`. It is imported from
[`U001/Definitions.lean`](../U001/Definitions.lean), which reuses
`Langlands.Tate.zeroShortComplexIso A` from Worker 45's
[`ZeroDefinitions.lean`](../../../../../Cohomology/Tate/ZeroDefinitions.lean).

The local equality `hker` identifies `ker S.g.hom` with `ker T.g.hom`.
It rewrites the former using
`groupCohomology.d₀₁_ker_eq_invariants`, then applies
`Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg`.
The equality `(ρ(g) - 1)(x) = 0` is equivalent to `ρ(g)(x) = x` by
`Rep.sub_hom` and `sub_eq_zero`. Thus `LinearEquiv.ofEq` gives a linear
identification `eK` of these kernels, acting as the identity on underlying
coefficient vectors.

The two incoming maps are the same norm map. Consequently the local
`hboundary` transports the range of `S.moduleCatToCycles` under `eK` to
the range of `T.moduleCatToCycles`. Each inclusion uses the same input
vector; `Subtype.ext` reduces the required equality to `rfl`.
`Submodule.Quotient.equiv` descends `eK` to the quotient by these ranges,
and `toModuleIso` turns it into the isomorphism `eQ` of the explicit
homology presentations. The final composite is

```lean
isoZeroBoundary A ≪≫
  S.moduleCatHomologyIso ≪≫ eQ ≪≫ T.moduleCatHomologyIso.symm
```

## Implemented degree-minus-one construction

Set

```lean
S := ShortComplex.mk (groupHomology.d₁₀ A) A.norm.toModuleCatHom
  (Rep.comp_eq_zero A)
T := Rep.FiniteCyclicGroup.subCompNormHom A g
```

The current Library supplies exactly the necessary short-complex comparison:

```lean
Langlands.Tate.minusOneShortComplexIso A :
  (tateComplex A).sc (-1) ≅ Langlands.Tate.minusOneShortComplex A
```

The abbreviation on its right unfolds to this exact `S`, including
`Rep.comp_eq_zero A`. The implementation imports this data from Worker 45's
[`Coinduced.lean`](../../../../../Cohomology/Tate/Coinduced.lean) and uses it
as `eS`. It replaces the source's repeated construction of `eS`.
The reused construction uses `HomologicalComplex.isoSc'` in degrees
`-2, -1, 0`, then `ShortComplex.isoMk` with
`groupHomology.chainsIso₁ A`, `groupHomology.chainsIso₀ A` and
`groupCohomology.cochainsIso₀ A`. Its first square is
`groupHomology.comp_d₁₀_eq A`; its second follows by unfolding
`Rep.tateNorm` and canceling the component isomorphisms. These are the
same component comparisons used in source lines 96–104.

Both outgoing maps are the norm, so `eK` is `LinearEquiv.ofEq _ _ rfl`
between their kernels. For the incoming maps, the local equality `hRange`
rewrites `range S.f.hom` using
`groupHomology.range_d₁₀_eq_coinvariantsKer`, and then applies the existing
`Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ g hg`.
After unfolding the short complexes, the latter's difference map is
exactly `T.f.hom`.

The local `hboundary` transports the corresponding ranges inside the norm
kernel. In each direction, `hRange` supplies a preimage for the same
coefficient vector; `Subtype.ext` lifts its equality to equality of cycles.
As in degree zero, `Submodule.Quotient.equiv` gives `eQ`, and the final
composite is

```lean
ShortComplex.homologyMapIso eS ≪≫
  S.moduleCatHomologyIso ≪≫ eQ ≪≫ T.moduleCatHomologyIso.symm
```

`ShortComplex.homologyMapIso` supplies the isomorphism on the actual
homology objects. `ShortComplex.moduleCatHomologyIso` identifies each
abstract homology with its explicit kernel modulo the image of
`moduleCatToCycles`. `LinearEquiv.ofEq`, `Submodule.Quotient.equiv`,
`toModuleIso` and categorical composition supply the forward/inverse
maps and inverse laws. No new substantive kernel/image theorem or assumed
comparison is introduced: the mathematical identifications are the cited
published Mathlib laws, and the local range transport checks only their
compatibility with the subtype presentations.

## Reuse scope

The semantic reuse search inspected the host Tate degree-zero quotient,
its zero and minus-one short-complex comparisons, Mathlib's ordinary
finite-cyclic homology/cohomology comparisons, and the host cyclic H2
norm construction. The ordinary finite-cyclic isomorphisms start from
ordinary group (co)homology and do not directly have the boundary Tate
sources required here. The host `zeroEquiv` ends in the quotient of
invariants by norms; it does not end in the required finite-cyclic
short-complex homology. The host cyclic H2 helpers use that same
invariant quotient for a different source, and are private. The present
module reuses the exact available boundary comparisons and the public
kernel/image/quotient API instead of rebuilding them.

M003.003 does not call M003.002. They share a focused module because they
construct the two adjacent boundary-degree comparisons with the same
parameters and quotient method. This removes the inventory's conservative
scheduling edge as a mathematical dependency; it does not assert any
further cohomological or reciprocity comparison.

## Pinned source and complete modifications

The original is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/TateComparison.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/TateComparison.lean>).
The complete file, including its section context and M003.001, was read.
Its SHA-256 is
`673ea55ceb079f0c1a342ab625ce475b66106e9a54e504eeb08ceece6c1c826c`.
The source registration is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No matching NYLL erratum was found in the current Library's `notes/errata`.

The changes from the source are:

- Extract only M003.002 and M003.003 into the requested
  `Langlands/NYLL/GaloisCohomology/Cyclic/TateComparison/FiniteCyclic/Definitions.lean`.
  Change namespace `TateCohomology` to `Langlands.NYLL.TateCohomology`.
- Preserve both declaration names after the prefix, docstrings, shared
  universe, complete parameter order, binder kinds and categorical result
  types. Preserve the source's local kernel, range and quotient arguments.
- Import the accepted U001 module for M003.001 instead of defining it again.
  Its body reuses Worker 45's published zero short-complex comparison.
- Replace M003.003's repeated `eS` construction with
  `Langlands.Tate.minusOneShortComplexIso A`, imported from
  `Langlands.Cohomology.Tate.Coinduced`.
- Retain the original direct
  `Mathlib.RepresentationTheory.Homological.FiniteCyclic` import. The original
  `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic` import is
  supplied transitively by the two host imports. No compatibility options
  or new instances are added.
- Replace the module docstring to describe this focused extraction. Retain
  the original copyright, license and author header verbatim.

The original Apache-2.0 license and NOTICE are retained at
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original source header credits Naganori Yamaguchi assisted by OpenAI
Codex; Mathlib retains its own source authorship and licenses.

The current Lean environment is `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`,
Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
These two definitions provide only the stated finite-cyclic Tate boundary
isomorphisms; host class-formation, cup, transfer and reciprocity targets
retain their independent obligations.
