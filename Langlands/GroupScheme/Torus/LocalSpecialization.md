# Local special-fibre detection for split-torus homomorphisms

Author: Worker 717.

This internal module collects consequences of the published open
closed-immersion and isomorphism loci for split-torus homomorphisms. Every
result is quantified in an arbitrary universe. The base ring is any
commutative local ring: no domain, Noetherian, Henselian, or characteristic
hypothesis is needed.

In namespace `Langlands.GroupScheme.TorusLocalSpecialization`, the predicate
`IsSpecialFibreIsomorphism f` means that the specified homomorphism becomes
an isomorphism after base change along the residue quotient map of the local
base. The following lemmas use that condition written explicitly.

`isClosedSubgroup_of_specialFibre` says that a homomorphism from a split torus
to an affine group scheme over `Spec R` is a closed subgroup embedding if its
base change along the quotient map `Spec(R/𝔪) → Spec R` is a closed embedding.
`isIso_of_specialFibre` says that a homomorphism between two split tori is an
isomorphism if this same special-fibre map is an isomorphism.

`isClosedSubgroup_comp_of_specialFibreIso` applies the first result to a
composite `i ≫ f`, where `i` is a closed split-torus embedding into a group
scheme `G` and `f : G → H` has isomorphic special fibre. The target `H` must
be affine over `Spec R`; the lemma imposes no reductivity or fibrewise
isogeny condition on `f`.

The proofs use `exists_open_isClosedImmersion_baseChange` and
`TorusIsomorphismLocus.exists_open_affine` to obtain an actual open immersion
`q : V → Spec R` through which the special-fibre point factors, with the
required property after base change along `q`. The two initial helper lemmas
show that `q` is an isomorphism: its open image contains the closed point,
and `IsLocalRing.closedPoint_mem_iff` makes that image the whole spectrum.
Closed-embedding reflection along an isomorphism is implemented with the
actual pullback square and cancellation by its isomorphic projections.
Isomorphism reflection uses the published `isIso_of_baseChange`.
For the composite lemma, closed immersion of `i` is preserved by base
change, then by composition with the isomorphic special-fibre map of `f`.

The provenance is internal composition of these published Library results
and Mathlib's local-spectrum topology. This module supplies a torus
embedding step for the prescribed-map rigidity argument in Task 6422. It
asserts neither maximality of the resulting torus nor invertibility of an
ambient reductive homomorphism.
