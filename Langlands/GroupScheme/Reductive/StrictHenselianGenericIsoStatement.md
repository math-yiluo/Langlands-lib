# Generic-fibre determination over strictly Henselian local domains

`Langlands.GroupScheme.StrictHenselianGenericIsoStatement` is a proposition
in every universe `u`. Let `R : Type u` be a commutative domain that is a
Henselian local ring with separably closed residue field. Let `K : Type u`
be any fraction field of `R`, with its given `R`-algebra structure. For two
actual reductive group schemes `G` and `H` over `Spec R`, the proposition
asserts that an isomorphism between their actual base changes along
`Spec K → Spec R` implies existence of an isomorphism `G ≅ H` over `R`.
The conclusion is `Nonempty (G ≅ H)` in the actual category of group schemes.
There is no Noetherian, valuation, completeness, rank, or characteristic
restriction. Smoothness and affineness belong to `IsReductive`.

This is an assertion about isomorphism classes. It does not extend a
prescribed generic-fibre isomorphism. In particular, the conclusion contains
no compatibility equation relating an integral isomorphism to the generic
isomorphism used in the premise. For an integral-model comparison, the
generic isomorphism induced by the resulting integral isomorphism must still
be compared to the supplied generic identifications. That difference can be
an automorphism of the generic group; its action on a chosen building is a
separate construction.

The proposition is a derived consequence of Brian Conrad, *Reductive group
schemes* (2014), registered as `conrad-2014-reductive-group-schemes`, source
SHA256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The source route is as follows:

- Lemma 5.1.3, PDF/internal pp.136–137, makes a reductive group split etale
  locally. A pointed etale neighbourhood of the closed point has a section
  over a strictly Henselian local ring. Pulling the split data back along
  that section makes each of `G` and `H` split over `R` itself.
- Definition 5.1.1 and Proposition 5.1.6, PDF/internal pp.136–138, describe
  split reductive groups and their reduced root data. Over the connected
  base `Spec R`, the character and cocharacter lattices and the root and
  coroot sets are constant and are unchanged on passing to a geometric
  generic fibre. The root lines are free as required by the source's split
  convention. They may alternatively be trivialized over the local ring.
- Apply the supplied generic isomorphism after passage to an algebraic
  closure of `K`. Theorem 3.2.6, PDF/internal p.94, gives conjugacy of
  maximal tori etale locally; over an algebraically closed field this
  identifies the two chosen maximal tori after an inner automorphism.
  The induced isomorphism of pairs preserves roots, coroots and their
  perfect pairing, giving an isomorphism of the two integral root data.
  This use of the generic isomorphism determines a root-datum isomorphism,
  rather than an extension of that generic map.
- Theorem 6.1.17, PDF/internal p.197, determines a split reductive group
  over any nonempty scheme up to isomorphism by its root datum and lifts
  any root-datum isomorphism to an isomorphism of the split groups.
  Applying it over `Spec R` yields the abstract integral isomorphism.
  Pinnings can be chosen because the root lines in the split data are
  free; their choices do not appear in this proposition.

The listed structural results justify this target; they are not imported
Lean proofs. The module states the proposition and proves none of those
results. It does not construct a canonical integral model, a compatible
isomorphism over a prescribed generic identity, a building automorphism,
a special point, or the supplied-model `BuildingComparisonStatement`.
