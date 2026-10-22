# Finite unramified Galois extensions of every positive degree

Authors: Worker 271 and Worker 90.

The theorem
`Langlands.ClassFieldTheory.Local.unramifiedExtensionDegreeExistence.{u}`
has type `UnramifiedExtensionDegreeExistence.{u}`, the proposition published in
[UnramifiedArithmeticStatement](UnramifiedArithmeticStatement.md). For every
prime `p`, every `F : PadicField.{u} p` in an arbitrary universe `u` and every
natural number `n > 0`, it produces an actual intermediate field `E` of
`AlgebraicClosure F.Carrier` with

- `E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier`,
- a proof of `IsGalois F.Carrier E.field`,
- `F.canonicalTopologicalData.ramificationIndex =
  (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex`, and
- `Module.finrank F.Carrier E.field = n`.

The statement pair and its imports are unchanged. No hypothesis is added: the
only assumption beyond the quantified data is `0 < n`, which is part of the
statement, and degree one is the case `n = 1` of the same argument. Besides the
statement module, the file imports the published modules
`Langlands.ClassFieldTheory.Local.FixedFieldStages`,
`Langlands.Galois.Local.UnramifiedCriterionProof` and
`Langlands.Weil.Local.Assembly`. The theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Strategy

Write `G_F = Field.absoluteGaloisGroup F.Carrier`. The published continuous
homomorphism `Langlands.Weil.Local.localResidueDegree F : G_F →ₜ* ProfiniteIntegers`
is the actual residue action followed by the published identification of the
residue absolute Galois group with the profinite completion of the integers.
It is surjective (`localResidueDegree_surjective`) and its kernel is the
absolute inertia group `F.absoluteInertia F.canonicalTopologicalData`
(`localResidueDegree_ker`). Composing it with reduction modulo `n` gives a
continuous surjection of `G_F` onto a group of order `n`. Its kernel `N` is an
open normal subgroup of index `n` that contains absolute inertia. The fixed
field `E` of `N` is then a finite Galois extension of degree `n`, and the
published canonical unramified criterion turns `I_F ≤ N` into equality of
canonical ramification indices.

This is a different route from the source proof cited in the statement
Markdown (Serre, *Local Fields*, Chapter III, section 5), which lifts a
separable residue extension. The implemented proof instead uses the already
published identification of `G_F / I_F` with the profinite integers and the
published inertia criterion.

## Implemented proof

All declarations below are in the namespace
`Langlands.ClassFieldTheory.Local`. `Degree` is the published
`Langlands.Weil.Degree = Multiplicative ℤ` and `ProfiniteIntegers` is the
published Mathlib profinite completion of `Degree`.

1. `degreeModHom n : Degree →* Multiplicative (ZMod n)` is the integer cast
   `Int.castAddHom (ZMod n)` written multiplicatively.
   `degreeModHom_surjective` proves it is surjective, using
   `ZMod.intCast_surjective`.

2. For `[NeZero n]`, `degreeModSubgroup n` is the kernel of `degreeModHom n`
   (the subgroup `n ℤ`) packaged as a `FiniteIndexNormalSubgroup Degree`.
   `degreeModSubgroup_index` proves that its index is `n`: by
   `Subgroup.index_ker` the index is the cardinality of the range, the range
   is everything by surjectivity, and `Nat.card (ZMod n) = n`.

3. `profiniteModProjection n` is the limit-cone projection of the profinite
   completion to its component at `degreeModSubgroup n`, that is to the finite
   quotient `Degree ⧸ n ℤ`, as a continuous homomorphism. On integer Frobenius
   elements it is the quotient map (`profiniteModProjection_frobenius`, by
   definition), so it is surjective (`profiniteModProjection_surjective`).

4. `residueDegreeMod F n` is the composite of `localResidueDegree F` with this
   projection, and `residueDegreeMod_surjective` combines the two
   surjectivity results.

5. `residueDegreeModKernel F n : OpenNormalSubgroup G_F` is the kernel of
   `residueDegreeMod F n`. It is normal as a kernel, and open because the
   finite quotient carries the discrete topology, so the kernel is the
   preimage of the open set `{1}` under a continuous map.
   `residueDegreeModKernel_index` proves its index is `n`, again via
   `Subgroup.index_ker`, surjectivity, and step 2.

6. `absoluteInertia_le_residueDegreeModKernel` rewrites absolute inertia as
   the kernel of `localResidueDegree F` (`localResidueDegree_ker`); an element
   with trivial residue degree is sent to `1` by the projection.

7. The closing theorem fixes `p`, `F`, `n` and `0 < n`, installs
   `NeZero n`, `CharZero F.Carrier` (from `Algebra.charZero_of_charZero`
   over `Padic p`) and `IsGalois F.Carrier (AlgebraicClosure F.Carrier)`. Let
   `N = residueDegreeModKernel F n` and let `E` be the published
   `finiteStageFixedField F.Carrier N`, the actual fixed field of `N` in
   `AlgebraicClosure F.Carrier`, with the published instance
   `finiteStageFixedField_finiteDimensional` as its finiteness certificate.
   The published instance `finiteStageFixedField_isGalois` gives the required
   `IsGalois` witness. Mathlib's `InfiniteGalois.fixingSubgroup_fixedField`,
   applied to the closed subgroup `finiteStageClosedSubgroup F.Carrier N`,
   shows `E.field.fixingSubgroup = N`.
   - Ramification: the published theorem
     `Langlands.PadicField.canonicalUnramifiedCriterion` states, for this
     `E`, that the canonical ramification indices agree if and only if
     `F.absoluteInertia F.canonicalTopologicalData ≤ E.field.fixingSubgroup`.
     After rewriting the fixing subgroup as `N`, step 6 supplies the
     inclusion.
   - Degree: Mathlib's `IntermediateField.finrank_eq_fixingSubgroup_index`
     gives `finrank F.Carrier E.field = E.field.fixingSubgroup.index`; after
     rewriting this is the index of `N`, which is `n` by step 5.

## Scope

The theorem asserts existence only; it makes no uniqueness claim and does not
identify the Galois group of `E` or a Frobenius coordinate. The auxiliary
declarations are general helper constructions for the profinite integers and
for `localResidueDegree`; they add no hypotheses to the target.
