# Surjectivity of finite abelian endomorphisms over fields

`Langlands.GroupScheme.fieldFiniteEndomorphismSurjective.{u}` proves exactly
the published proposition
`Langlands.GroupScheme.FieldFiniteEndomorphismSurjectiveStatement.{u}`.
The statement pair and its import closure are unchanged.

For every field `K : Type u`, every group object
`G : Grp (Over (Spec (CommRingCat.of K)))` with `IsCommMonObj G.X`, and every
endomorphism `f : G ⟶ G`, the theorem takes the hypotheses
`Smooth G.X.hom`, `IsProper G.X.hom`, `GeometricallyConnected G.X.hom`,
and `IsFinite f.hom.hom.left`, and proves `Surjective f.hom.hom.left`.
The conclusion concerns all underlying scheme points. It does not claim
surjectivity on `K`-rational points.

## Implemented proof

The proof introduces exactly the variables and hypotheses of the statement,
and installs smoothness, properness, and geometric connectedness as local
instances. The imported theorem
`Langlands.AbelianScheme.smoothGeometricIntegrality`, applied to `K`,
`G.X.left`, and `G.X.hom`, gives `GeometricallyIntegral G.X.hom`.
This published theorem treats arbitrary fields and every field-valued
pullback; it adds no hypothesis to the present theorem.

The spectrum of a field has a subsingleton point space. Thus Mathlib's
`GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom` gives
`IsIntegral G.X.left`, which supplies irreducibility of the underlying
scheme and its point space. Nonemptiness is included in this integrality;
no separate nonemptiness assumption is needed.

The structure morphism is locally of finite type, as follows from its
smoothness or properness. The spectrum of the field is locally Noetherian,
so `LocallyOfFiniteType.isLocallyNoetherian G.X.hom` gives
`IsLocallyNoetherian G.X.left`. Properness also supplies quasi-compactness.
Since the field spectrum is compact,
`QuasiCompact.compactSpace_of_compactSpace G.X.hom` gives compactness of
`G.X.left`. Local Noetherianity and compactness construct
`IsNoetherian G.X.left`, hence `TopologicalSpace.NoetherianSpace G.X.left`.

The imported theorem
`Langlands.AlgebraicGeometry.finiteIrreducibleEndomorphismSurjective`
now applies to `G.X.left` and the actual underlying scheme endomorphism
`f.hom.hom.left`, with the given finite-morphism hypothesis. Its hypotheses
are exactly the irreducibility and Noetherian topology just derived.
It returns the required scheme-point surjectivity.

The imported generic theorem fixes the generic point using discrete fibres
and well-founded induction on closed singleton closures, then uses the
closed image of the finite morphism. Its paired documentation explains
that proof. The present assembly therefore requires no dimension theory
or comparison of image dimensions.

The universe parameter `u`, every field, and every characteristic are
retained. All geometric properties used in the final application are
derived inside the proof. The group operations and commutativity are
retained in the exact target, although the scheme argument does not
otherwise use them.

## Provenance and contributions

This is an internal assembly of published Library proofs and Mathlib
results. Worker 414 wrote the assembly and this documentation. The imported
geometric-integrality assembly is by Worker 416; the imported generic
finite-endomorphism proof is by Worker 419 with the generic-point argument
contributed by Worker 414. Their paired documentation records the
underlying scheme and topology proofs and their contributions.

The unchanged target's source correspondence is J. S. Milne,
*Abelian Varieties*, author revision January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, Proposition 8.1 on p.12 and
the opening of section 20 on p.42. These passages and the retained author
errata were read. Milne's criterion explains this derived endomorphism
statement, but the implemented proof follows the independent
generic-point route above. It neither assumes nor invokes
`Langlands.GroupScheme.FieldFiniteKernelIsogenyStatement`.
