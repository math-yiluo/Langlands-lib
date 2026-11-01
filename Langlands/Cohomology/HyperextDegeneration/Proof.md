# Proof of the degeneration of the hyperext spectral sequence

Author: Worker 894. The two halves of the proof are published results of
Worker 61: `edgeMap_injective_of_ext` in
`Langlands.Cohomology.HyperextGradedVanishing` and `edgeMap_surjective_of_ext`
in `Langlands.Cohomology.HyperextEdgeMapSurjective`. The statement and the
edge map are Worker 3's, in `Langlands.Cohomology.HyperextDegeneration.Statement`.

This module proves the published proposition
`Langlands.Cohomology.HyperextDegenerationStatement`, unchanged and in full.

## The theorem

```lean
theorem Langlands.Cohomology.hyperextDegenerationStatement_proof
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C] :
    HyperextDegenerationStatement.{w, w'} C
```

Its universe parameters are `w`, `w'`, `v` and `u`, all arbitrary. `C` is an
abelian category with objects in `Type u` and morphisms in `Type v`.
`HasDerivedCategory.{w} C` fixes a model of `DerivedCategory C` with morphisms
in `Type w`, and `HasExt.{w'} C` makes Mathlib's groups `Abelian.Ext.{w'}`
available in `Type w'`. These are exactly the binders of the statement, and
the theorem has no other hypotheses: `C` and both instances are arbitrary.

Unfolded, the conclusion says the following. Let `K` be an object of
`DerivedCategory C` and `b` an integer such that `H^i(K)` is zero for every
`i > b`, where `H^i` is `DerivedCategory.homologyFunctor C i`. Let `W` be an
object of `C` such that `Abelian.Ext.{w'} (H^k(K)) W i` is a subsingleton for
every integer `k` and every natural number `i > 0`. Then for every integer
`n` the edge map

`HyperextDegeneration.edgeMap K W n : Hom(K, W⟦n⟧) → Hom(H^{-n}(K), W)`

is bijective. Here `W⟦n⟧` is `W` placed in degree zero
(`DerivedCategory.singleFunctor C 0`) and shifted by `n`, and the edge map
applies `H^{-n}` and identifies `H^0` of the single complex with `W`.

## The proof

The proof is one term:

```lean
fun K b hK W hW n =>
  ⟨HyperextAbutment.edgeMap_injective_of_ext K b hK W hW n,
    HyperextAbutment.edgeMap_surjective_of_ext K b hK W hW n⟩
```

`Function.Bijective` is the conjunction of injectivity and surjectivity. Both
published lemmas, in the namespace `Langlands.Cohomology.HyperextAbutment`,
take exactly the data of the statement: `K`, `b`, the vanishing hypothesis
`hK`, `W`, the `Ext` hypothesis `hW` and the degree `n`, with the same
instances `HasDerivedCategory.{w} C` and `HasExt.{w'} C`. So the proof passes
the hypotheses of the statement to each lemma unchanged.

- Injectivity, `edgeMap_injective_of_ext`
  (`Langlands.Cohomology.HyperextGradedVanishing`). The kernel of the edge map
  is the step `F^1` of the abutment filtration of `Hom(K, W⟦n⟧)` by
  truncations of `K`. For `p > 0` the morphisms from the degree-`(p - n)`
  piece of `K` to `W⟦n⟧` correspond to elements of `Ext^p(H^{p-n}(K), W)`,
  which is zero by `hW`; so `F^p = F^{p+1}`. Since `K` is bounded above,
  `F^p = 0` for large `p`, hence `F^1 = 0`.
- Surjectivity, `edgeMap_surjective_of_ext`
  (`Langlands.Cohomology.HyperextEdgeMapSurjective`). It uses the truncation
  triangles of the canonical t-structure. Let `K₁ = τ_{≥ -n} K`; the map
  `K ⟶ K₁` is an isomorphism on `H^{-n}`. A morphism on `H^{-n}` is first
  realized on the degree-`(-n)` part `Z` of `K₁`. The obstruction to
  extending it from `Z` to `K₁` is a morphism from `X = τ_{≥ 1-n} K₁`, which
  lies in degrees `1 - n` through `b`, to `W⟦n+1⟧`. A dévissage over these
  finitely many degrees shows that it is zero, because each step involves
  `Ext^{j+n+1}(H^j(K), W)` with `j + n + 1 ≥ 2`, zero by `hW`. The extension
  to `K₁`, precomposed with `K ⟶ K₁`, is the required preimage.

These two summaries describe the published proofs of those lemmas; this
module only combines their conclusions. Neither proof constructs the hyperext
spectral sequence or a convergence statement, and neither does this module.

The Markdown of the statement also gives a direct proof by induction over
the truncation triangles `τ≤(m-1) K → τ≤m K → H^m(K)[-m] →`. The Lean proof
does not follow it.

## Provenance

The statement is a derived formulation of the degeneration step in Harris,
*Galois properties of cohomological automorphic forms on GL(n)*, J. Math.
Kyoto Univ. 39-2 (1999), 299-318 (source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`).
Proposition 4.10, printed p.311 (one-based PDF page 13), gives the spectral
sequence (4.10.1), with `Ext^i` "the i-th derived functor of Hom in the
category of smooth `L_ℓ[GJ]`-modules". On printed p.312 (PDF page 14) Harris
writes: "since `π_v` is supercuspidal, the higher Ext's vanish and the
spectral sequence (4.10.1) degenerates to an isomorphism" (5.2). Worker 894
reread both passages in the text layer of the PDF for this module. The
Markdown of the statement also cites Harris, Invent. Math. 129 (1997), 75-119
(source `harris-1997-drinfeld-cohomology`), where the spectral sequence (10),
p.96, collapses to the isomorphisms (11). The statement's Markdown records
how the Lean statement corresponds to both sources; the correspondence is
derived, since the Lean statement asserts bijectivity of the edge map
directly rather than the degeneration of a spectral sequence.

The proof is ours, assembled from the published Library lemmas above and
Mathlib; it does not follow a printed proof.

## Scope

- This module proves only `HyperextDegenerationStatement`. The Harris-specific
  specialization, the identification of Harris's `Ext` groups with
  `Abelian.Ext`, and the vanishing of the higher `Ext` groups for a
  supercuspidal coefficient representation are not proved here; the statement
  takes that vanishing as its hypothesis `hW`.
- Only bounded-above `K` are covered, as in the statement.
- The bijection is not packaged as an additive or linear equivalence here.

## Dependencies and checks

Imports: `Langlands.Cohomology.HyperextDegeneration.Statement`,
`Langlands.Cohomology.HyperextGradedVanishing` and
`Langlands.Cohomology.HyperextEdgeMapSurjective`, all unchanged. No other file
is added or edited. Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`).

Check `96d7335a-37fe-4cac-8351-0794ab328327` built the module with Lake with no
errors or warnings and inspected `hyperextDegenerationStatement_proof`: a
theorem with universe parameters `w`, `w'`, `v`, `u`, depending only on
`propext`, `Classical.choice` and `Quot.sound`. Compilation does not establish
acceptance; publication requires independent review and exact-target
validation.
