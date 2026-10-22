# Restriction of arithmetic Frobenius coordinates in finite base-change squares

Author: Worker 271.

This module states one proposition,
`Langlands.ClassFieldTheory.Local.UnramifiedBaseChangeCoordinateCompatibility.{u}`.
It is a proposition-valued definition. This module does not prove it; the
proof is a separate task.

## The square

The statement quantifies every prime `p` (with `[Fact p.Prime]`) and four
fields `F E L M : PadicField.{u} p` in one arbitrary common universe `u`.
It assumes exactly the same structures as the published
`UnramifiedInvariantBaseChangeCompatibility` in
[`UnramifiedInvariantCompatibilityStatement`](UnramifiedInvariantCompatibilityStatement.md):

- algebra structures `F → E`, `F → L`, `F → M`, `E → M` and `L → M` on the
  carriers;
- scalar towers `Padic p → F → E`, `Padic p → F → L` and `Padic p → E → M`,
  so these embeddings are compatible with the specified p-adic structures,
  and scalar towers `F → E → M` and `F → L → M`, so both paths from `F` to
  `M` agree;
- finite dimensionality of `E/F`, `L/F` and `M/E`;
- `IsGalois F L` and `IsGalois E M`;
- the canonical unramifiedness conditions: the canonical absolute
  ramification index (`canonicalTopologicalData.ramificationIndex`) of `F`
  equals that of `L`, and that of `E` equals that of `M`.

The last two hypotheses are named `_hFL` and `_hEM` in the Lean source. They
are ordinary hypotheses of the proposition. The leading underscore only
records that the conclusion does not mention them by name, which silences
Lean's unused-variable linter. They keep the square identical to the one in
`UnramifiedInvariantBaseChangeCompatibility`.

The statement does not assume that `M/F` is normal or Galois. It does not
assume that `E/F` is Galois or unramified, that `M` is the compositum of `L`
and `E`, or any compatibility between the two coordinates. It has no local
invariant, class formation or reciprocity hypothesis. Every degree,
including degree one for any of `E/F`, `L/F` or `M/E`, is in scope.

## Coordinates and the asserted formula

Write `n = Module.finrank F.Carrier L.Carrier` and
`m = Module.finrank E.Carrier M.Carrier`. Both are positive because the
extensions are finite field extensions. The local `NeZero n` and `NeZero m`
instances are built from `Module.finrank_pos`; they are not extra premises.

The statement quantifies every pair of group isomorphisms

```text
χL : Gal(L/F) ≃* Multiplicative (ZMod n)
χM : Gal(M/E) ≃* Multiplicative (ZMod m)
```

that satisfy the published predicates
`IsArithmeticUnramifiedCoordinate F L.Carrier χL` and
`IsArithmeticUnramifiedCoordinate E M.Carrier χM` from
[`Invariants`](Invariants.md). For `χL`, the predicate requires that the
actual residue action `LocalGalois.residueHom F.Carrier L.Carrier` be
injective. It also requires that `χL.symm (ofAdd 1)` act on the actual
residue field of `L` by `x ↦ x ^ q_F`, where `q_F` is the cardinality of
the actual residue field of `F`. The predicate for `χM` says the same
over `E`, with exponent `q_E`. Thus both coordinates use the arithmetic
Frobenius convention.

Let `σM = cyclicCoordinateGenerator χM`, the element `χM.symm (ofAdd 1)`
of `Gal(M/E)` defined in [`UnramifiedInvariant`](UnramifiedInvariant.md).
Let

```text
f = Langlands.Weil.Local.extensionResidueDegree F E
      (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier).
```

This is the dimension of the canonical residue field of `E` over that of
`F`. The scalar structure comes from the residue map induced by the actual
embedding `F → E` regarded as a `Padic p`-algebra map; see
[`ExtensionResidue`](../../Weil/Local/ExtensionResidue.md). The proposition
asserts

```text
χL ((σM.restrictScalars F.Carrier).restrictNormal L.Carrier)
  = Multiplicative.ofAdd (f : ZMod n).
```

The cast of `f` is the ordinary cast from `ℕ` to `ZMod n`.

The group map on the left is the actual composite

```text
Gal(M/E) → Gal(M/F) → Gal(L/F),   σ ↦ (σ.restrictScalars F).restrictNormal L.
```

The first arrow forgets `E`-linearity; it uses the tower `F → E → M`. The
second restricts an `F`-automorphism of `M` to the normal subextension `L`;
it uses the tower `F → L → M` and the normality of `L/F` supplied by
`IsGalois F L`. Normality of `M/F` is not needed. By definition, this
composite equals `AlgEquiv.restrictNormalHom L` applied after
`AlgEquiv.restrictScalarsHom F`. These are the group homomorphisms used by
`relativeInflation F L M` and `relativeRestriction F E M` in
[`Cohomology`](Cohomology.md). The author checked this agreement by `rfl` in
a private development file. That check is not part of this module.

In words: the arithmetic Frobenius generator of `M/E`, viewed in
`Gal(M/F)` and restricted to `L`, is the `f`-th power of the arithmetic
Frobenius generator of `L/F`. Equivalently, its `χL`-coordinate is `f`
modulo `n`.

## Derivation (provenance)

This is a derived specialization, not a verbatim statement from a source.
The standard argument is as follows. The future proof must carry it out for
the actual Library constructions.

1. Reduction commutes with restriction. The embedding `L → M` maps the
   integers and residue field of `L` into those of `M`. Every
   `F`-automorphism of `M` preserves the image of `L`, because `L/F` is normal. Its
   action on the image of the residue field of `L` is the residue action
   of its restriction to `L`.
2. `σM` acts on the residue field of `M` by `x ↦ x ^ q_E`. Hence its
   restriction to `L` acts on the residue field of `L` by `x ↦ x ^ q_E`.
3. `q_E = q_F ^ f`. For the canonical residue fields, this is the published
   `Langlands.Weil.Local.extensionResidueCardinality`.
4. `(χL.symm (ofAdd 1)) ^ f` acts on the residue field of `L` by
   `x ↦ x ^ (q_F ^ f) = x ^ q_E`. By injectivity of the residue action of
   `L/F`, the restricted element equals `(χL.symm (ofAdd 1)) ^ f`.
   Applying `χL` gives `ofAdd (f • 1) = ofAdd (f : ZMod n)`.

The predicates use `LocalGalois` residue fields, built from the spectral
norm on the base. `extensionResidueDegree` uses the canonical residue
fields of `canonicalTopologicalData`. The proof must also compare these
constructions and the residue map of the embedding `L → M`. This statement
takes no such comparison as a hypothesis. It also does not assume the
existence of coordinates. Existence is the separate published
`ArithmeticUnramifiedCoordinateExistence`, proved in
`UnramifiedArithmeticProof`, and gives no restriction compatibility.

Original source: Jean-Pierre Serre, *Local Fields*, English translation by
Marvin Jay Greenberg, Graduate Texts in Mathematics 67, Springer, 1979.
Registered source `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 271 read the following pages.

- Chapter III, Section 5, Theorem 3 and Corollaries 1–3, printed
  pp. 54–55 / PDF pp. 61–62. For a finite unramified `K'/K` and an
  arbitrary finite `K''/K`, reduction gives a bijection between
  `K`-embeddings `K' → K''` and `k`-embeddings of the residue fields. In
  particular, an automorphism of the unramified `L/F` is determined by its
  residue action, which is step 4.
- Chapter XIII, Section 3, Proposition 7 and its proof, printed
  pp. 193–194 / PDF pp. 198–199. In case (a), with `L/K` unramified of
  degree `n`, the distinguished generator of the subgroup `g_n` of
  `G(K_nr/K)` is `F^n`. In case (b), with `L/K` totally ramified, the group
  and its Frobenius are unchanged. The general case passes through the
  maximal unramified subextension.

The present proposition is the finite-stage analogue. The base extension
`E/F` plays the role of Serre's `L/K`, and the finite unramified `M/E` and
`L/F` replace the maximal unramified extensions. Under restriction, the
Frobenius of the larger base becomes the `f`-th power of the Frobenius of
the smaller base. Here `f` is the residue degree of `E/F`: `f = n` in
Serre's case (a) and `f = 1` in case (b). No source-specific errata file for
this source exists in the project notes.

## Intended use

The proposition supplies the generator comparison needed to prove
`UnramifiedInvariantBaseChangeCompatibility` for the same square. Taking
`E` to be `F` with its identity algebra structure compares the generators
of `M/F` and `L/F`, as needed for
`UnramifiedInvariantInflationCompatibility`. This module states neither of
these consequences and makes no cohomological claim.

The reused definitions and their sources are imported unchanged from
[`Invariants`](Invariants.md), [`UnramifiedInvariant`](UnramifiedInvariant.md)
and [`ExtensionResidue`](../../Weil/Local/ExtensionResidue.md).
