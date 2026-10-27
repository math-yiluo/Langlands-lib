# Supercuspidal local components of cuspidal classes

This module defines when an irreducible cuspidal class of `GL_{r+1}` over a
number field `F` has a supercuspidal local component at a finite place `v`.
Harris (1998), Proposition 4.8, concludes that the local component
`Π_{v(*)₁}` at the auxiliary place is supercuspidal. This is the predicate for
that conclusion. Nothing is asserted about any particular class.

## Setting

- `LocalRealization F (r + 1) v` is the published type of actual local
  realizations: invariant subspaces of automorphic functions with the action
  of `GL_{r+1}(F_v)`.
- The published `LocalRealization.padicClass S hI hA` sends an irreducible
  (`hI`) admissible (`hA`) local realization to its class in the canonical
  `p`-adic correspondence category over `CompletionPadic.padicField v`, the
  completion `F_v` as a finite extension of `ℚ_p`.
- The published `Correspondence.IsSupercuspidalClass` says that a class lies
  in the image of the Jacquet-vanishing supercuspidal class space
  (`PadicField.SupercuspidalClass`, built on Worker 23's
  `GeneralLinear.IsSupercuspidal`). That predicate asks for admissibility and
  vanishing Jacquet coinvariants for every proper block parabolic subgroup.
- A `CuspidalSpectralPresentation S` of a full cuspidal realization `S` is
  Worker 2's published tensor presentation of a nonzero finite-adelic slice.
  Its `localComponent v` is the actual embedded local copy of the supplied
  factor at `v`.

## Definitions

- `LocalRealization.IsSupercuspidal S` says that `S` is irreducible and
  admissible, and that its canonical `p`-adic class is supercuspidal.
- `CuspidalOperatorRealization.IsoClass.HasSupercuspidalComponent c v` says
  that some representative `S` of `c` has a spectral presentation `P` whose
  local component `P.localComponent v` is supercuspidal. The universe `uV` of
  the presentation's local factor carriers is a parameter, as in the published
  `HasSpectralSystem`. The definition carries the instance parameter
  `[CompactSpace (AdeleQuotient F)]` of the published cuspidal classes, which
  the published `compactSpace_adeleQuotient` proves.

## Theorems

- `IsSupercuspidal.of_isoClass_eq` and `isSupercuspidal_iff_of_isoClass_eq`:
  supercuspidality depends only on the smooth isomorphism class. The proof
  transports irreducibility and admissibility with the published
  `isIrreducible_iff_of_equiv` and `isAdmissible_iff_of_equiv`. It then uses
  `padicClass_eq_iff_isoClass_eq`.
- `hasSupercuspidalComponent_iff`: a supercuspidal component can be witnessed
  at every representative. The proof transports a presentation along a full
  equivalence with the published `CuspidalSpectralPresentation.transport`,
  whose local components keep their isomorphism classes
  (`transport_localComponent_isoClass`).

## Scope

The definition asks for one presentation whose local component at `v` is
supercuspidal. The Library does not yet prove that all presentations of a
cuspidal class have isomorphic local components (uniqueness of the
restricted tensor factorization). Until then, "some presentation" is the
faithful reading of "the local component is supercuspidal". It is the same
choice as the published weak-induction relation, which also asks for one
presentation. Square-integrability is not defined here.

## Source and provenance

- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210. Source
  `harris-1998-local-langlands`. Proposition 4.8, printed p.201 (PDF p.25):
  "the local component `Π_{v(*)₁}` at `v(*)₁` is supercuspidal".

The predicate is internal. It combines the published local components, their
canonical `p`-adic classes and the published supercuspidal class space.
