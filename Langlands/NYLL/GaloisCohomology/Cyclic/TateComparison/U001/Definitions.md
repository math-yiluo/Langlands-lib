# Degree-zero Tate boundary homology

Port author: Worker 170. Original author: Naganori Yamaguchi (assisted by
OpenAI Codex). The implementation imports Worker 45's published construction
`Langlands.Tate.zeroShortComplexIso`; no draft or patch is copied.

`Langlands.NYLL.TateCohomology.isoZeroBoundary` constructs the actual categorical
isomorphism

```lean
tateCohomology A 0 ≅
  (ShortComplex.mk A.norm.toModuleCatHom (groupCohomology.d₀₁ A)
    (Rep.norm_comp_d_eq_zero A)).homology
```

Its parameters, in source order, are implicit `R G : Type u`, followed by
`[CommRing R] [Group G] [Fintype G]`, then explicit `(A : Rep R G)`. There is
one universe `u`. The group is any finite group; a cyclicity hypothesis is
unnecessary for this boundary construction.

The left side is Mathlib's Tate cohomology of its spliced inhomogeneous
chain/cochain complex. The right side is Mathlib's homology object of the
displayed short complex. Both are objects of `ModuleCat R`, with the original
representation universe. The construction includes forward and inverse
morphisms and their two inverse identities.

## Implemented construction and reused laws

The current Library already provides exactly the needed short-complex
comparison in
[`Langlands/Cohomology/Tate/ZeroDefinitions.lean`](../../../../../Cohomology/Tate/ZeroDefinitions.lean):

```lean
Langlands.Tate.zeroShortComplexIso A :
  (tateComplex A).sc 0 ≅ Langlands.Tate.zeroShortComplex A
```

`Langlands.Tate.zeroShortComplex A` is an abbreviation for the exact
`ShortComplex.mk` in the result above, including the same
`Rep.norm_comp_d_eq_zero A` certificate. Thus the present definition applies
Mathlib's `ShortComplex.homologyMapIso` directly to this existing isomorphism.
Mathlib's `tateCohomology A 0` unfolds to the homology of `(tateComplex A).sc 0`.
No quotient replacement or assumed comparison is introduced.

The reused comparison implements the same route as source lines 34–49:

1. `HomologicalComplex.isoSc'` identifies the short complex at zero with
   the terms in degrees `-1, 0, 1`. In the shape `ComplexShape.up ℤ`, the
   predecessor and successor of zero are `-1` and `1`.
2. `ShortComplex.isoMk` uses the three existing component isomorphisms
   `groupHomology.chainsIso₀ A`, `groupCohomology.cochainsIso₀ A` and
   `groupCohomology.cochainsIso₁ A`.
3. The first commutative square follows by unfolding `Rep.tateNorm` as
   `(chainsIso₀ A).hom ≫ A.norm.toModuleCatHom ≫ (cochainsIso₀ A).inv`
   and canceling the cochain isomorphism with its inverse. The second
   square is the existing theorem `groupCohomology.comp_d₀₁_eq A`.
   `Rep.norm_comp_d_eq_zero A` supplies the target short-complex law.

Finally, `ShortComplex.homologyMapIso` maps the comparison and its inverse
to homology. Its inverse laws follow from `ShortComplex.homologyMap_comp`
and `ShortComplex.homologyMap_id`. All comparison equations needed here
already occur in published Library or Mathlib constructions; no missing
substantive equality or existence lemma is assumed.

## Pinned source and modifications

This is source unit M003.001 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/TateComparison.lean`, lines 28–50](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/TateComparison.lean>).
The file SHA-256 is
`673ea55ceb079f0c1a342ab625ce475b66106e9a54e504eeb08ceece6c1c826c`.
The full source file, including section context and the later cyclic
constructions, was read for this extraction.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, with
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The complete changes from this source unit are:

- Extract only M003.001 into the required `U001/Definitions` module and
  change the namespace from `TateCohomology` to
  `Langlands.NYLL.TateCohomology`.
- Preserve its parameter order, one shared universe, hypotheses, docstring
  and actual categorical result type.
- Replace the local construction of `S` and `eS` with the published
  `Langlands.Tate.zeroShortComplexIso A`, retaining the final
  `ShortComplex.homologyMapIso` step.
- Replace the two original direct Mathlib imports with
  `Langlands.Cohomology.Tate.ZeroDefinitions`. This transitively imports
  `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`.
  `Mathlib.RepresentationTheory.Homological.FiniteCyclic` is unnecessary
  for this finite-group construction.
- Add a module docstring describing the reuse. Preserve the original
  copyright, license and author header verbatim. No instances or
  compatibility options are added.

The original Apache-2.0 license and NOTICE are retained at
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`; their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The declaration provides this boundary isomorphism only. The finite-cyclic
degree-zero and degree-minus-one constructions M003.002–003 and further
cohomological or reciprocity comparisons remain separate work.
