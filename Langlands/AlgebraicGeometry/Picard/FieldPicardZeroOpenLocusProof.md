# The geometric Picard-zero open locus over an arbitrary field

Authors: Worker 962, Worker 603.

`Langlands.AbelianScheme.fieldPicardZeroOpenLocus` proves the existing proposition
`Langlands.AbelianScheme.FieldPicardZeroOpenLocusStatement.{u}`. For any field
`k : Type u`, abelian scheme `A` over `Spec k`, parameter `P : Over (Spec k)`,
and actual rigidified family `L : RigidifiedFamily A P`, the theorem accepts
the statement's local finite-type and full rigidified universality hypotheses
and produces `U : P.left.Opens` satisfying `IsPicardZeroOpenLocus A L U`.
Thus for every scheme `T` over `k` and every actual morphism `h : T ⟶ P`,

```text
IsPicardZeroClass A
  (RigidifiedLineBundle.classifyingMap A.X.hom
    (unitSection A) (unitSection_comp A) L T h)
  ↔ Set.range h.left ⊆ (U : Set P.left).
```

The predicate retains its existing meaning: translation invariance on every
algebraically closed field-valued fibre of the actual pulled-back family.
The quantification over test schemes includes nonreduced schemes.

## Implemented proof

The proof specializes the construction already used in the published module
`Langlands.AlgebraicGeometry.Picard.FiniteTypePicardZeroOpenLocusProof`
(Worker 967 and Worker 1095). Worker 603 identified this application to the
field statement. All ingredients below are imported from the current Library.

1. For every abelian scheme `G` over a scheme `B` and every line bundle `M`
   on its total space, `mumfordTrivialLocus G M : B.Opens` is an actual open
   subset. Its membership is triviality of the Mumford class on the
   residue-field fibre. The theorem
   `isTranslationInvariant_fibreLineBundle_iff G M K t` identifies image
   containment in this open with translation invariance of
   `fibreLineBundle G M t` for every algebraically closed geometric point `t`.
   Together they supply `HasOpenFibreTranslationInvarianceLocus G M`.
2. Apply
   `exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion` to this
   criterion and `A`, `P`, `L`. It constructs an open `U` on `P.left`
   characterizing `IsPicardZeroFamily` of the actual relative pullback of
   `L` at every geometric point of `P.left`. The comparison accounts for
   the actual product and base-change isomorphisms. In the reverse direction,
   it also applies the criterion to the geometric-point family itself;
   this supplies the full geometric-fibre condition, including further
   algebraically closed field extensions.
3. Apply `isPicardZeroOpenLocus_of_geometricPoints` with the proved
   `picardZeroGeometricDetection` and that criterion. The bridge uses
   composition coherence of the actual rigidified pullbacks, identifies
   `IsPicardZeroClass` of the classifier with the corresponding family
   predicate, and detects image containment using geometric points above
   every point of a test scheme. Its conclusion is precisely the required
   criterion for all `T` and `h`.

The construction works over arbitrary scheme bases and actual rigidified
families, so the two additional premises of this field target are unused.
The Lean theorem nevertheless has exactly the published target type, with
the arbitrary field and universe `u` preserved. It introduces no
projectivity, representability, dual-scheme, openness or comparison premise.
It proves no existence assertion for an ambient universal family; that
representability obligation belongs to the separate parent dependency.

## Provenance

This is a derived composition of published Library theorems. The source
context of the target is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Paragraph (6.2), printed p.88/PDF p.92, describes actual rigidified pullback
and universal classification; Chapter VI §3, printed p.95/PDF p.99, gives
the Picard-scheme and Mumford-bundle context; Theorem (6.18) and Definition
(6.19), printed p.96/PDF p.100, describe the dual identity component; and
Corollary (7.22), printed p.106/PDF p.110, identifies Picard zero with the
kernel of the associated homomorphism. The implemented proof uses the
published Mumford-locus and geometric-detection route, without constructing
an identity component or treating Corollary (7.22) alone as an all-test
classification theorem.
