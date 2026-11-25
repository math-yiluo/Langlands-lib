# Étale-local conjugacy of maximal tori in smooth affine group schemes

`Langlands.GroupScheme.etaleLocalMaximalTorusConjugacy` proves the unchanged
`Langlands.GroupScheme.EtaleLocalMaximalTorusConjugacyStatement.{u}`. The
statement and all its imported files are unchanged.

For every scheme `S` in universe `u`, every smooth affine group scheme `G`
over `S`, and two closed relative tori whose maps into `G` are maximal on every
residue-field fibre, it constructs an étale cover of `S`. On each member there
is an actual section of the pulled-back group conjugating the first torus image
onto the second on every test scheme. The base is arbitrary; neither reductivity
nor connectedness of the fibres is assumed. The tori can be nonsplit and can
have varying ranks on different parts of the base.

## Implemented proof

The proof first retains the stronger conclusion `SubgroupConjugate`: besides an
actual conjugating section it records an isomorphism between the two source
group schemes, and equality of the resulting homomorphisms. The internal
Prop-valued definition `EtaleLocallySubgroupConjugate` asserts this conclusion on
an étale cover. The final theorem forgets the source isomorphism by
`SubgroupFunctor.range_iso_comp`, giving exactly the target's equality of
subgroup functors.

### Field conjugacy inside the identity component

`maximalTorusConjugacy_in_identity` applies the published
`exists_isMaximalTorus_identityComponent` separately to the two maximal tori of a
smooth affine group over an algebraically closed field. This gives actual
factorizations through its actual identity component, retaining maximality.
The published `maximalTorusConjugacy` applies to that smooth affine connected
group. Its source isomorphism in commutative group schemes is converted to one
in group schemes by `CommGroupScheme.groupHom`. Naturality of inner conjugation
(`innerIso_hom_comp`) pushes the resulting conjugacy into the original ambient
group. The range formula for `identityComponentι` shows that the conjugating
point lies in its actual identity component. This step handles disconnected
ambient field groups without adding a connectedness hypothesis.

### Integral coordinates and the local transporter

For standard split tori indexed by possibly different finite types `I` and `J`,
`splitTorus.fieldIsoExtension` extends an isomorphism over a field to an
isomorphism over any base `S`. It uses the integral exponent homomorphisms
`characterMap` of the given map and its inverse. The published composition and
identity laws for `exponentHom` and `characterMap` prove the two inverse
identities. `fieldIsoExtension_hom` recovers the original field homomorphism.
`fieldIsoExtension_baseChange` gives exact recovery under the actual canonical
split-torus base-change comparisons. No equality of coordinate index types is
required, and no chosen isomorphism is assumed to have descended in advance.

`PointwiseSchemeAction.isTransporter_iff_innerIso` identifies the published
all-test transporter convention with the equation

```text
IsTransporter i₁ i₂ g ↔ i₂ ≫ (G.innerIso g).hom = i₁.
```

Its proof evaluates homomorphisms on points, uses the formula for inner
conjugation, and cancels the inverse of the conjugating point. In the reverse
direction the unique map from any test scheme to the terminal test identifies
the constant-point family with the supplied transporter refinement.

`splitTorus.exists_etale_subgroupConjugate` treats an affine base `Spec R` and a
chosen point `s`. It takes the specified geometric point with coefficient field
an algebraic closure of the residue field at `s`.
`IsFibrewiseMaximalTorus.fieldPoint` supplies maximality on this actual field
pullback. Source transport along the canonical split-torus comparisons and the
identity-component field conjugacy above produce a conjugator and an isomorphism
`c` of the two standard split tori over that field.

Extend `c` to an isomorphism `e` over `Spec R`. The exact coordinate recovery
proves that the field conjugator is a transporter between `e.hom ≫ i'` and `i`,
which now have the same standard split source. The published
`PointwiseSchemeAction.etaleIdentityTransporterOfSplitTorus` applies: the field
point maps to `s`, the all-test transporter equation holds, and the point lies in
the actual identity component. Its result is an affine étale neighbourhood
through `s` and an actual section after base change satisfying the transporter
equation. Converting that equation back to inner conjugation gives
`SubgroupConjugate` for the actual pulled-back maps, with source isomorphism the
base change of `e`. This construction need not recover the original field
point. The final proof uses no recovery assertion for that point.

### Arbitrary base changes and covers

The supporting transport lemmas are derived directly from published
isomorphism and base-change laws:

- `IsFibrewiseMaximalTorus.baseChange_forConjugacy` applies the field-point maximality theorem
  at the composite residue-field point and then
  `isMaximalTorus_baseChange_comp`. This preserves fibrewise maximality along an
  arbitrary base map for a smooth affine ambient group.
  Its proof-specific name allows importing this module together with the
  separate maximal-torus existence proof's transport helpers.
- `IsFibrewiseMaximalTorus.iso_comp` applies source-isomorphism transport in each
  residue-field fibre.
- `SubgroupConjugate.baseChange` uses `HomConjugate.baseChange` and the mapped
  source isomorphism. `precomp_isos` and `of_precomp_isos` transport both source
  coordinates by the existing reflexive source conjugacies and transitivity.
- `SubgroupConjugate.of_baseChange_comp` uses the naturality squares for
  `baseChangeCompIso`. Source-isomorphism transport and ambient-isomorphism
  cancellation carry conjugacy from successive actual pullbacks to the actual
  pullback along the composite map.
- `EtaleLocallySubgroupConjugate.of_etaleCover` chooses the supplied conjugacy
  covers, forms their `Cover.bind`, and applies the composite-pullback lemma on
  every member. Its source-isomorphism adapter applies the mapped isomorphisms
  on each member of the chosen cover.

`of_standardSplit_affine` collects the affine étale neighbourhoods through every
point into a cover using `Scheme.Cover.mkOfCovers`. `of_isSplitTorus_affine`
chooses coordinates for both split tori and then removes them using source
transport. `of_isSplitTorus` applies this affine result to the affine open cover
of an arbitrary base, promotes that open cover to an étale cover, and assembles
the refinements.

Finally, `of_relativeTori` takes a splitting cover for the first relative torus.
Over each member, it takes a splitting cover for the pullback of the second.
The first torus remains split after the second pullback, and both maps remain
fibrewise maximal by the arbitrary-base transport lemma. The split-torus result
then applies. Two applications of cover locality produce a single étale cover
of the original base, with actual conjugacy data on every member.

The target's two global closed-immersion hypotheses are retained in the final
theorem's type. This proof obtains the local conjugacies from the relative-torus
and residue-fibre maximality hypotheses; it does not separately use those two
global hypotheses.

## Provenance and scope

This file is an internal composition of the named published results. Its
coordinate extension, source transports, and cover bookkeeping are derived
helpers for this proof. The original target is the étale-local conjugacy
assertion in Brian Conrad, *Reductive group schemes* (2014), Theorem 3.2.6,
printed/PDF pp.94–95, in the smooth affine generality used after supplying the
maximal tori. The registered source is
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The target's published Markdown gives the source comparison in detail.

The implemented route uses the published smooth transporter lifting theorem,
identity-component reduction, integral split-torus coordinates and field
conjugacy. It does not reproduce the source's direct-limit and Artin
approximation argument. No unproved structural statement is an input. The exact
public target is proved in every universe, with its original hypotheses and
all-test subgroup-functor conclusion.

Shared declarations `IsFibrewiseMaximalTorus.iso_comp` are imported from `Langlands.GroupScheme.Torus.FibrewiseMaximalTransport`; their mathematical hypotheses, conclusions and data are unchanged.
