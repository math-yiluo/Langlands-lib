# Total ramification from disjointness with the actual inertia fixed field

Author: Worker 107.

## Exact theorem and scope

`Langlands.PadicField.inertiaDisjointTotallyRamified.{u}` proves exactly the
published proposition `Langlands.PadicField.InertiaDisjointTotallyRamified.{u}`
from `Langlands.Galois.Local.InertiaDisjointRamificationStatement`.
There are no additional outer hypotheses.

For a prime `p`, a p-adic field `F : PadicField.{u} p`, and an actual finite
intermediate extension `D` of `F.Carrier` in `AlgebraicClosure F.Carrier`, set

```lean
U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
```

From `D.field.LinearDisjoint U` the theorem proves

```lean
(D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
  Module.finrank F.Carrier D.field * F.canonicalTopologicalData.ramificationIndex
```

The universe is arbitrary. The proof covers degree one and non-Galois `D`.
It uses the actual inclusion of `D.field` in the specified algebraic closure,
the inherited `F.Carrier` scalar map, and the composite `Padic p` scalar map
used by `D.asPadicField`. The two ramification indices are the canonical
absolute indices, namely the normalized orders of `p`; they are not relative
indices. No residue-degree, normality, ramification, or norm premise is added.
The proof changes neither the statement pair nor its import closure.

## Implemented proof

Write `G` for the absolute Galois group of `F`, `I` for its actual canonical
inertia subgroup, and `T = D.field.fixingSubgroup` for the subgroup fixing the
prescribed intermediate field. Characteristic zero is inherited from
`Padic p`, so the algebraic closure is Galois over `F.Carrier`.

First set `H = T ⊔ I`. Linear disjointness gives `D.field ⊓ U = ⊥` by
`IntermediateField.LinearDisjoint.inf_eq_bot`. The fixed field of `H` lies
in both the fixed field of `T` and that of `I` because fixed fields reverse
subgroup inclusions. `InfiniteGalois.fixedField_fixingSubgroup` identifies
the former with `D.field`. Thus `fixedField H = ⊥`.

Finite dimensionality of `D.field` makes `T` open in the Krull topology.
`Subgroup.isOpen_mono` makes `H` open as well, and an open subgroup is closed.
The closed-subgroup direction of infinite Galois correspondence,
`InfiniteGalois.fixingSubgroup_fixedField`, therefore identifies `H` with
the fixing subgroup of its fixed field. Since the fixing subgroup of the
bottom intermediate field is all of `G`, this proves `H = ⊤`. Closedness is
explicitly justified; the argument does not infer equality of arbitrary
subgroups merely from equality of their fixed fields.

Now write `E = D.asPadicField` and `f = intermediateEmbedding F D`. The
published residue-index theorem uses the image `S` of
`extensionGaloisMap F E f`, which arises from a chosen isomorphism of
algebraic closures. For a non-Galois `D`, that image need not equal `T`.
The proof uses the published `intermediateClosureCorrection F D`, denoted
`c`, to compare them. `extensionGaloisMap_range` and
`intermediateClosureCorrection_conj_mem` show directly, in both directions,
that conjugation by `c` maps `S` onto `T`. Normality of absolute inertia
and `Subgroup.Normal.map_conj_eq` show that the same conjugation maps `I`
to itself. Consequently it maps `S ⊔ I` onto `T ⊔ I = G`. The Lean proof
uses injectivity of this conjugation to deduce `S ⊔ I = ⊤` element by element.
No normality of `D` or of its fixing subgroup is used.

The published theorem
`extensionGaloisMap_range_sup_absoluteInertia_index` identifies the index
of `S ⊔ I` with `extensionResidueDegree F E f`. Since the subgroup is top,
this residue degree is one. Finally,
`ramificationIndex_mul_extensionResidueDegree` gives

```text
e_abs(E) * extensionResidueDegree(F,E,f) = extensionDegree(F,E,f) * e_abs(F).
```

The proof explicitly identifies `extensionAlgebra F E f` with the inherited
`Algebra F.Carrier D.field` by equality of their scalar maps, using
`Algebra.algebra_ext`. Rewriting `extensionDegree` with this equality gives
the exact `Module.finrank F.Carrier D.field` in the target. Substituting
residue degree one into the displayed identity finishes the proof.

## Dependencies and provenance

The new module directly imports only the published statement and
`Langlands.Galois.Local.UnramifiedCriterionProof`. Its mathematical inputs
are the residue-index and absolute-index degree identities from that proof,
the actual intermediate embedding and closure-correction lemmas from its
imported `Langlands.Weil.Local.IntermediateWeil`, normality of canonical
absolute inertia, and Mathlib's linear disjointness, Krull topology, and
infinite Galois correspondence. These are reused as published Lean results;
no unsubmitted draft is reused. Worker 107 authored this proof and companion.

The result is the finite-model ramification implication underlying Serre's
Lemma 7 in Chapter V, section 4. Its original proof passes through a maximal
unramified subextension. The implemented proof instead uses the existing
absolute Galois residue-index identity and infinite Galois correspondence.
The arithmetic content of the residue-index and degree identities remains
in their published dependencies. This theorem constructs no common finite
stage, proves no descent statement, and draws no norm or cohomological
conclusion.

Original source: Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, Springer GTM 67 (1979), registered as `serre-1979-local-fields`.
File: `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
SHA256: `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 107 read and checked the following original passages for this task:

- V.4, Lemmas 6–7 and the proof of Proposition 7, printed pages 89–90,
  PDF pages 96–97: disjoint finite models have residue degree one and are
  totally ramified; the subsequent norm conclusion is outside this theorem.
- III.5, Theorems 2–3 and Corollaries 1–3, printed pages 54–55, PDF pages
  61–62: unramified extensions and maximal unramified subextensions of
  arbitrary finite extensions.
- IV.1, Proposition 1 and the corollary to Proposition 2, printed pages
  62–63, PDF pages 69–70: inertia and its fixed-field interpretation.
- I.4, definitions, Proposition 10 and the valuation restriction formula,
  printed pages 14–15, PDF pages 22–23: ramification and residue degrees,
  the degree identity and normalization under field restriction.

The source fingerprint was verified. No project errata entry for this source
was present in the workspace or supplied public notes when checked.
