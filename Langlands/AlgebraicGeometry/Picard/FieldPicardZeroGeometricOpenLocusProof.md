# Geometric-point openness in a universal rigidified field Picard parameter

Author: Worker 1543.

The theorem
`Langlands.AbelianScheme.fieldPicardZeroGeometricOpenLocus.{u}` proves the
unchanged published proposition
`Langlands.AbelianScheme.FieldPicardZeroGeometricOpenLocusStatement.{u}`.
It takes an arbitrary field `k : Type u`, an abelian scheme `A` over
`Spec k`, a parameter `P : Over (Spec k)`, an actual rigidified family
`L : RigidifiedFamily A P`, local finite type of `P.hom`, and the full
rigidified universal property of `L` over all test schemes.

The conclusion supplies an actual open `U : P.left.Opens`. For every
algebraically closed field `K : Type u` and actual
`s : Spec K ⟶ P.left`, it proves

```text
IsPicardZeroFamily A
  ((RigidifiedLineBundle.relativePullback A.X.hom
    (unitSection A) (unitSection_comp A)
    (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L)
  ↔ Set.range s ⊆ (U : Set P.left).
```

## Implemented proof

The proof composes two published Library results.

First, for every scheme `B`, abelian scheme `G` over `B`, and line bundle
`M` on `G.X.left`, the module
`Langlands.AbelianScheme.MumfordTrivialLocus` supplies the actual open
`mumfordTrivialLocus G M`. Its points are those where the Mumford class
of `M` is trivial on the residue-field fibre of `G.X ⨯ G.X`.
The theorem `isTranslationInvariant_fibreLineBundle_iff G M K t`
identifies containment of the range of a geometric point `t` in this open
with translation invariance of `fibreLineBundle G M t` on the base-changed
abelian scheme. This discharges
`HasOpenFibreTranslationInvarianceLocus G M` for every `B`, `G` and `M`.

Second, the theorem
`exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion` in
`Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyGeometricPointComparison`
applies that criterion to
`G = (baseChange P.hom).obj A` and `M = familyLineBundle A L`.
It constructs `U` from the supplied open, compares the actual relative
pullback with the restriction of `M` to the corresponding fibre, and
proves precisely the displayed equivalence.
For the reverse implication, that published comparison also applies the
criterion to the pulled-back family over `Spec K`: invariance at the
identity makes its locus contain every point of `Spec K`, so every
further geometric fibre is translation invariant. Thus the conclusion
retains the full geometric-fibre meaning of `IsPicardZeroFamily`.

The Lean proof introduces all hypotheses of the target and supplies the
first criterion to the second theorem. The construction works over any
base scheme, so local finite type and universality are unused in this
specialization. The theorem still has exactly the published target as
its type, with arbitrary `k` and universe `u`, and adds no hypotheses.

## Provenance and scope

This is a derived assembly of published Library mathematics. The
Mumford-class construction, its openness proof, field-extension descent,
and translation-invariance comparison remain in
`MumfordTrivialLocus`; the actual-family and iterated-base-change
comparisons remain in `PicardZeroFamilyGeometricPointComparison`.
Their paired Markdown describes those proofs and their provenance.

The proof uses the existing translation-invariance predicate on actual
pulled-back families. It constructs no ambient Picard parameter and makes
no identity-component comparison. Its conclusion concerns geometric
points; the all-test-scheme assembly belongs to the separate parent
statement. The target statement pair and every pair in its imported
dependency closure are unchanged.
