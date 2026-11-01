# Constant degree for ordinary polarized finite-level data

Worker 310.

This module supplies the degree convention and transport used in ordinary
polarized finite-level moduli. The source is Mumford, Fogarty and Kirwan,
*Geometric Invariant Theory*, third edition (1994), Chapter 7, Section 2,
Definition 7.2, printed p.129 / PDF p.142, registered as
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
The source calls for polarization degree `d²`.

`HasConstantDegree f r` means that the native scheme-morphism degree
`f.finrank` equals `r` at every point of the target. `HasDegreeSquare f d`
applies this condition to the underlying actual scheme map of an
abelian-scheme homomorphism, with `r = d ^ 2`.

For an actual relative polarization, the existing `IsPolarization` predicate
includes the finite-flat-surjective isogeny condition. Over a locally
noetherian base its target dual abelian scheme is locally noetherian, so
the finite morphism is locally of finite presentation. A finite flat morphism
of finite presentation is finite locally free, and its degree is the local
rank of its direct image structure algebra. Thus requiring this rank to
equal `d²` at every point is the source's locally free rank convention.
The Lean definition uses native finite-flat rank. The lemma
`hasConstantDegree_spec_iff` formally identifies it with the native
affine algebra rank on spectra; a separate equivalence with a sheaf-level
finite locally free predicate is not asserted.

The transport lemmas are derived infrastructure. The native rank theorem for
Cartesian squares proves arbitrary base-change preservation. For
postcomposition with an isomorphism, the Cartesian square with identity first
projection identifies the new rank with the old rank evaluated at the inverse
image of the target point. Precomposition invariance is Mathlib's native rank
invariance. These give invariance of the constant degree predicate, including
both implications for isomorphisms.

`hom_baseChange_isPullback` exhibits the Cartesian square for actual
abelian-scheme base change. It follows by cancellation of the target's
defining pullback square. `HasDegreeSquare.baseChange` applies native rank
base-change invariance using the finite and flat parts of the original
isogeny. No numerical multiplication-rank formula is used.

`hasDegreeSquare_iso_iff` gives both implications when source and target are
changed by actual abelian-scheme isomorphisms.
`isLocallyConstant_finrank_of_isIsogeny` proves local constancy over a locally
noetherian base: the target is locally noetherian since it is smooth over the
base, and finiteness gives local finite presentation.

`HasDegreeSquare.dualAbelianBaseChangeMap` combines arbitrary base change
with postcomposition by the existing canonical dual-abelian-scheme
comparison. It keeps the original and changed dual existence, geometry,
inverse line-bundle and evaluation witnesses explicit. The module proves
degree preservation for any supplied changed witnesses; construction of those
witnesses belongs to the actual datum pullback. Its named tensor, Picard and
dual-compatibility hypotheses are exactly those of the existing comparison,
and its finite-flat premise is the original `IsIsogeny` condition, available
as the first conjunct of `IsPolarization`.
