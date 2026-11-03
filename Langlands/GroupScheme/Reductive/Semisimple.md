# Scheme-theoretic centres, semisimple groups and adjoint groups

Author: Worker 1290.

This module gives predicates on actual group schemes, retaining the entire
scheme-theoretic centre, and proves their invariance under isomorphisms.
It constructs no centre and proves no existence or structure theorem.

## Sources and conventions

- J. S. Milne, *Algebraic Groups* (2017), source
  `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:
  Proposition 19.10, printed p. 400 (PDF p. 416), characterizes semisimplicity
  of a reductive group by finiteness of its centre. The preceding paragraph
  explicitly warns that the centre can be nonsmooth and disconnected.
  Remark 17.63, printed p. 373 (PDF p. 389), defines an adjoint group as a
  semisimple group with trivial centre. The retained 2017-book errata snapshot
  of 2026-11-02 was checked; it has no correction to these definitions.
- B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, second edition
  (2015), source `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
  `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`:
  Definition A.1.10, printed p. 469 (PDF p. 495), defines the
  scheme-theoretic centre using trivial conjugation after arbitrary base
  extension and notes the example of the nonsmooth centre mu_p of SL_p.
  The registered source has no retained errata note.

The arbitrary-base centre packaging and Lean names are derived interfaces for
this Library. The field predicates use Milne's finite-centre characterization
as their definition; this module does not separately prove its equivalence to
an alternative radical-based definition of semisimplicity.

## Predicates

For any base scheme `S` and actual homomorphism `z : Z ⟶ G`,
`IsSchemeTheoreticCenter z` means that `z` is a closed subgroup inclusion and
`SubgroupFunctor.range z = center G`. The imported `center` tests commutation
with every point after every change of test scheme. Thus this is equality of
full subgroup functors, not equality of rational-point centres.
`IsSchemeTheoreticCenter.isRepresentedBy` supplies the existing representability
predicate, and `.isCentral` supplies all-test centrality of the inclusion.

`HasFiniteCenter G` means that there exist an actual group scheme `Z` and
homomorphism `z : Z ⟶ G` satisfying `IsSchemeTheoreticCenter z`, and that the
structural scheme morphism of `Z` is finite. This existential predicate includes
the representability requirement; it neither chooses a representative nor
asserts that one exists. There is no reducedness or smoothness requirement on
`Z`.

For an arbitrary field `k` in an arbitrary universe, `IsSemisimple G` has
fields `isConnectedReductive : IsConnectedReductive G` and
`hasFiniteCenter : HasFiniteCenter G`. The imported reductive predicate uses
the geometric unipotent radical after algebraic-closure base change, as
explained in `Reductive/Basic.md`. The module imposes no perfectness or
characteristic restriction and does not use invariant-theoretic geometric
reductivity.

`IsAdjoint G` has fields `isSemisimple : IsSemisimple G` and
`center_eq_bot : center G = ⊥`. Triviality is equality of all-test subgroup
functors. This concerns adjoint groups, with no reference to a Lie adjoint
representation.

## Implemented intrinsic proofs

`mem_center_comp_iso` transports a central point through an ambient group
isomorphism: commute with the inverse image of an arbitrary point, then apply
the isomorphism's group homomorphism on test points. Applying the inverse gives
`mem_center_comp_iso_iff`.

`IsSchemeTheoreticCenter.comp_iso` preserves the closed subgroup condition and
uses that pointwise equivalence to identify the image with the target centre.
`HasFiniteCenter.of_iso` keeps the same finite representing scheme and
postcomposes its inclusion with the inverse isomorphism.

`IsSemisimple.of_iso` combines the imported reductivity transport with finite
centre transport. `IsAdjoint.of_iso` additionally transports a central point,
uses triviality in the target, and composes with the inverse to show it is the
identity. The corresponding `isSemisimple_iff_of_iso` and
`isAdjoint_iff_of_iso` give the two directions.
