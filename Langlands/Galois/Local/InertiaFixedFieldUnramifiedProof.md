# Proof of finite unramified exhaustion of the actual inertia fixed field

Author: Worker 107.

`Langlands.PadicField.inertiaFixedFieldUnramifiedExhaustion` proves exactly
`Langlands.PadicField.InertiaFixedFieldUnramifiedExhaustion.{u}`, in arbitrary
universe `u`, with no additional outer hypotheses. The statement is imported
unchanged from `Langlands.Galois.Local.InertiaFixedFieldUnramifiedStatement`.
For every prime `p` and `F : PadicField.{u} p`, write

```lean
U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
```

The theorem proves both clauses of the published conjunction: every finite
Galois intermediate field whose canonical absolute ramification index equals
that of `F` lies in `U`, and every finite subset of `U` is contained in one
such finite Galois intermediate field. The equality retains the orientation
`F.canonicalTopologicalData.ramificationIndex =
(E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex`.

## Implemented proof

The proof first installs characteristic zero on `F.Carrier` using its existing
algebra over `Padic p`. This supplies Galoisness of the existing algebraic
closure over `F.Carrier`. The published `F.absoluteInertia_normal` and
Mathlib's `IsGalois.of_fixedField_normal_subgroup` then prove `IsGalois
F.Carrier U`, in particular normality of `U` over the base. No new valuation,
closure, scalar map or local-field realization is introduced.

For the first clause, the forward direction of the published theorem
`canonicalUnramifiedCriterion p F E` converts equality of canonical absolute
ramification indices to

```lean
F.absoluteInertia F.canonicalTopologicalData ≤ E.field.fixingSubgroup.
```

Mathlib's `IntermediateField.le_iff_le` converts this subgroup inclusion to
`E.field ≤ U`.

For the second clause, let `s` be the supplied finite subset, and set

```lean
A := IntermediateField.adjoin F.Carrier (s : Set (AlgebraicClosure F.Carrier))
L := IntermediateField.normalClosure F.Carrier A (AlgebraicClosure F.Carrier)
```

All elements of the algebraic closure are integral over the base field.
`IntermediateField.finiteDimensional_adjoin` therefore makes `A` finite
dimensional over `F.Carrier`. Mathlib's `normalClosure.is_finiteDimensional`
instance makes `L` finite dimensional as well. Since the ambient algebraic
closure is Galois over the characteristic-zero base,
`IsGalois.normalClosure` supplies `IsGalois F.Carrier L`. The intermediate-field
algebras and scalar towers in these applications are the existing ones for
`F.Carrier ⊆ A ⊆ AlgebraicClosure F.Carrier`.

The hypothesis on `s` gives `A ≤ U` by
`IntermediateField.adjoin_le_iff`. Normality of `U` and
`IntermediateField.normalClosure_le_iff_of_normal` give `L ≤ U`. Thus the normal
closure is taken within the actual ambient algebraic closure and remains in
the actual inertia fixed field; it is not merely an abstract isomorphic model.

The witness `E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier`
is the pair of `L` and its finite-dimensionality certificate. Its field is
literally `L`. `IntermediateField.le_iff_le` now converts `L ≤ U` to the
inertia-fixing condition, and the reverse direction of the published
`canonicalUnramifiedCriterion p F E` supplies the required equality of
canonical absolute ramification indices. Finally,
`IntermediateField.subset_adjoin` followed by
`IntermediateField.le_normalClosure A` puts every element of `s` in `E.field`.
This construction works unchanged for the empty finite set: neither the
finite-adjoin theorem nor the normal-closure construction requires a
nonempty generating set.

## Dependencies and provenance

The module imports the target statement, the published
`Langlands.Galois.Local.UnramifiedCriterionProof`, and Mathlib's
`Mathlib.FieldTheory.Normal.Closure`. The canonical criterion supplies the
arithmetic comparison; the remaining argument is finite generation and Galois
theory. The proof assumes neither that criterion nor exhaustion as an extra
premise. It proves the field exhaustion only; extension descent, norms and
cohomology vanishing remain separate results.

The source context is Jean-Pierre Serre, *Local Fields*, translated by Marvin
Jay Greenberg, Springer GTM 67 (1979), registered as
`serre-1979-local-fields`, file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 107 read III.5, Theorems 2–3 and Corollaries 1–3, printed pages 54–55
(PDF pages 61–62); IV.1, Proposition 1 and the corollary to Proposition 2,
printed pages 62–63 (PDF pages 69–70); and V.4, Lemmas 6–7, printed pages
89–90 (PDF pages 96–97). No project errata entry for this source was present
in the current public notes when checked.

The first passages describe finite unramified extensions, their maximal
unramified union, and the inertia fixed-field characterization. Lemmas 6–7
explain the finite-level role of finitely many structure constants. The
published target is a derived formulation for the actual canonical inertia
fixed field, not a verbatim statement from Serre. The implemented proof uses
the already proved canonical criterion together with Mathlib's normal-closure
construction rather than repeating Serre's residue-extension construction.
