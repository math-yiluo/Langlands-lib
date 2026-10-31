# Strong inverse maps for upper-cofinal original subatlases

This pair constructs a reverse full strong map for a locally refining selection
of original charts when every original chart lies in a selected chart.
If the original charts are also directed under containment, the two canonical
maps are inverse as full strong maps and give an isomorphism in the category of
directed atlas presentations.

The coefficient field `K : Type u` is complete, normed and ultrametric.
The ambient space and chart indices occupy independent universes `v` and `w`.
All presentations in a strong map use this same universe triple. The chart
algebras remain the actual finite positive-polyradius Tate quotients by closed
ideals of the imported atlas construction; no strictness or reducedness is
assumed.

## Original source and derived provenance

The source is Vladimir G. Berkovich, *Étale cohomology for non-Archimedean
analytic spaces*, Publications Mathématiques de l'IHÉS **78** (1993), 5–161,
registered as `berkovich-1993-etale-cohomology`, source SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

Definition 1.2.3 and Remark 1.2.4(i), printed p.16 / PDF p.13, specify actual
affinoid chart algebras, their bounded domain restrictions and the composition
of those restrictions. Definition 1.2.7, printed p.18 / PDF p.15, specifies
strong maps at every admissible source/target chart pair.
Definition 1.2.9, printed p.19 / PDF p.16, specifies quasi-isomorphisms by an
ambient homeomorphism and local affinoid-domain identifications.

The cofinal-selection predicate and inverse construction here are derived
original-chart specializations of those conventions. Upper cofinality is an
additional hypothesis, and directedness is required for the inverse equations
using the published directed-composition construction. These hypotheses are
not attributed to the source's general quasi-isomorphism definition.

## Selection hypotheses

In namespace `IndexedAffinoidAtlas`, `IsUpperCofinalSelection P : Prop` means
that for every original chart index `i` there is a selected index
`j : {j // P j}` such that the image of chart `i` is contained in that of
chart `j.val`. It imposes no monotone choice of containing indices.

`IsLocallyRefiningSelection P` is a separate imported hypothesis. It supplies
the relative finite local witnesses that make `subatlas P hP` an actual atlas
on the original ambient space. The construction does not infer this local
net condition from upper cofinality.

`hasDirectedCharts_subatlas` assumes original directedness and upper
cofinality. For two selected charts, its proof first finds a common original
upper chart by directedness and then a selected chart containing that upper
chart by cofinality. Transitivity of containment gives selected directedness.

## Full strong maps to a selected target

In namespace `AffinoidAtlasPresentation.StrongHom`,
`restrictCofinalSubatlasTarget f P hP hc` constructs a map from `A` to
`B.subpresentation P hP`. Its continuous map is exactly `f.baseMap`.
For a source chart, it takes an original target witness of `f` and then a
selected chart containing that target witness. At every admissible selected
target index `j`, its bounded pullback is exactly `f.pullback i j.val h`.
Both the spectrum square and the compatibility equation in the two chart
variables are inherited at those original indices.

The corresponding `_baseMap` and `_pullback` lemmas state these exact
formulas. `IsQuasiIso.restrictCofinalSubatlasTarget` preserves the original
ambient homeomorphism and applies the original full affinoid-domain
representation property at each selected target. That property continues to
test unique bounded algebra factorization against all finite
positive-polyradius presented affinoid algebras.

`restrictSubatlasSource_restrictCofinalSubatlasTarget` proves that source
selection and upper-cofinal target selection commute as full strong maps.
The proof uses the same continuous map and equality of the entire bounded
pullback families, including their dependent admissibility proofs.

## The reverse map and the inverse equations

In namespace `AffinoidAtlasPresentation`,
`strongCofinalSubatlasMap A P hP hc` restricts the target of the original
strong identity. It is a full strong arrow from `A` to its selected
subpresentation. Its `_baseMap` lemma identifies its continuous map with the
original space identity, and its `_pullback` lemma identifies every admissible
bounded pullback with the original atlas restriction from the selected
containing chart to the source chart.

`isQuasiIso_strongCofinalSubatlasMap` follows from the proved identity
quasi-isomorphism and target-selection preservation. The opposite canonical
arrow, `strongSubatlasInclusion`, and its quasi-isomorphism theorem are
imported from `StrongAtlasQuasiIsomorphisms`; they require local refinement
but do not require cofinality or directedness.

Assuming original directedness, `strongSubatlasInclusion_comp_cofinal`
proves that inclusion followed by the reverse arrow is the full strong
identity of the selected presentation. `strongCofinalSubatlasMap_comp_inclusion`
proves the converse full identity of the original presentation.

Both proofs use `StrongHom.ext_of_directed`: the continuous maps are
identities, and it suffices to compare one admissible bounded pullback per
source chart. For the first equation, the intermediate original chart is
the selected source chart itself. The directed composite's exact pullback
formula reduces the result to the original restriction composition law.
For the second equation, upper cofinality supplies a selected chart containing
the original source chart. The exact composite pullback is the original
restriction composed with the identity restriction on that selected chart.
The identity and bounded-composition laws finish the proof.
Thus the equations compare the complete strong-map records, including all
admissible pullbacks.

## Directed-presentation isomorphism

In namespace `DirectedAtlasPresentation`,
`cofinalSubpresentation A P hP hc` equips the actual selected presentation
with the proved selected directedness.
`cofinalSubatlasIso A P hP hc` is an isomorphism from that object to `A`:
its forward arrow is the canonical inclusion and its inverse is the reverse
cofinal arrow. The two strong-map equations above prove its inverse laws.

`spaceFunctor_mapIso_cofinalSubatlasIso` proves that the underlying-space
functor sends this isomorphism to `Iso.refl A.presentation.space`.
This comparison is definitional: both spaces are the same original space,
and both continuous maps are its identity.

## Scope

This construction selects original charts on the same space and retains their
original algebras and restrictions. It does not construct extended atlases,
new representing algebras, general affinoid gluing, inverses of arbitrary
quasi-isomorphisms, unrestricted strong composition or a localization.
The calculus of fractions of Proposition 1.2.10, analytic structure sheaves,
étale and equivariant sites, and the Harris tower remain separate obligations.
