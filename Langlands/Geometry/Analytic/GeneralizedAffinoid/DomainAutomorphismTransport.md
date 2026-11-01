# Moving full domains and conjugating their section operators

Authors: Worker 56 and Worker 36.

This module moves a supplied full represented affinoid domain by an actual
bounded automorphism of its base and proves the conjugation formula for
its constructed section operators. It retains the domain's section
algebra exactly, so the comparison is an equality of bounded maps on
one actual quotient algebra.

`K : Type u` is a complete ultrametric normed field and
`A : PresentedAffinoidAlgebra K` is an actual closed quotient of a
finite positive-polyradius Tate algebra. A supplied `U : Domain K A`
has the full unique-factorization property against all presented
positive-radius affinoids in the same universe. Trivial valuations,
nilpotents, zero quotients and empty loci remain allowed.

`boundedEquiv g` packages the actual specified maps `g.hom` and `g.inv`
as a `BoundedAlgEquiv K A A`; evaluation of the two categorical inverse
equations proves the elementwise inverse equations. The two `hom` lemmas
expose these maps exactly. This small adapter follows the existing
strict rational automorphism adapter by Worker 36.

`movedDomain U g` uses the published `Domain.transportBase` construction
with this bounded equivalence. Its algebra, quotient norm and elements
are unchanged. Its structural map is `U.baseMap.comp g.inv`.
The published base transport proves the full representation property
for this new map, including closedness, exact spectrum image and unique
bounded factorization.

`mem_movedDomain_locus` identifies membership in the moved locus with
membership of `g⁻¹ • x` in the original locus.
`movedDomain_locus` consequently proves that the moved locus is
`(fun x => g • x) '' U.locus`. The forward implication uses the
preimage point `g⁻¹ • x`; the reverse implication cancels the two
point actions. The action is the existing inverse seminorm pullback
action, so the choice of `g.inv` in the new structural map has the
stated variance.

`conjugate_mem_locusStabilizer_iff` proves that `g * h * g⁻¹` preserves
the moved locus exactly when `h` preserves the original locus. After
substituting the proved image-locus identity, acting by `g⁻¹` on the
set equality gives one direction, and acting by `g` gives the other.
No equality of chosen quotient presentations is required.

`movedSectionMap` and `movedSectionAut` expose the existing moved-domain
operators with their types explicitly stated on `U.algebra`, which
transport retains exactly. They are typed views of the constructed
operators, with no additional maps or properties.

`conjugateSectionMap_comp_baseMap` starts with the defining base
equation of the section map on the moved domain for `g * h * g⁻¹`.
It evaluates this equation at `g.hom a` and cancels the inverse pairs
of base maps. This proves that the resulting section map, viewed on
the retained original algebra, has composite `U.baseMap.comp h.hom`
with the original base map.

`stabilizerSectionMap_conjugate` compares this equation with the defining
base equation of the section map on `U` for `h`. Full unique
factorization, through `boundedHom_ext`, identifies the entire bounded
maps. `stabilizerSectionAut_conjugate` uses isomorphism extensionality
to identify the complete bounded automorphisms, including their
constructed inverses. Equality is not inferred from spectrum points.

These declarations are internal derived content from the published
full-domain base transport, bounded algebra category and constructed
stabilizer section action. Worker 36 is included for the reused
strict adapter and the underlying group-law packaging in the supporting
section-action module. The general transported domains and the
conjugation proof are built directly from their full universal
properties.

The module supplies no topology on the automorphism group, continuity
in the group parameter, comparison with every compact analytic domain,
structure sheaf, general analytic-space category or analytic site.
