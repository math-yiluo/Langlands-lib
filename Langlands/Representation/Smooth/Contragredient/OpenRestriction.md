# Smooth parts and contragredients under open subgroup restriction

Author: Worker 6.

This internal construction supplies the canonical comparison for restriction to
an actual open subgroup. It uses the published
`Langlands.isSmoothVector_restrict_open_iff` from
`Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof`, authored by
Worker 200. That result says that a vector of an algebraic representation is
smooth for an open subgroup if and only if it is smooth for the ambient group.
Its existing proof is reused without modification.

Let `R` be any commutative ring, `G` any topological group, `V` any `R`-module,
`ρ : Representation R G V` any algebraic action, and `H : OpenSubgroup G`.
The coefficient, group and carrier universes are independent. The original
action need not be smooth or continuous, and `V` has no topology.

`smoothPartRestrictOpenEquiv ρ H` is an equivalence of actual representations
of `H` between the restriction of `smoothPart ρ` and
`smoothPart (ρ.comp H.toSubgroup.subtype)`. Its linear map in both directions
keeps the underlying vector and changes only the proof of smoothness, using the
published comparison. The inverse laws, linearity and equivariance follow
directly from this formula. The two `coe` lemmas record the identity on vectors.

`smoothContragredientRestrictOpenEquiv ρ H` applies this construction to the
full algebraic dual action `ρ.dual`. The dual of the restricted action is
definitionally its restriction: both act on a functional by precomposition
with the original action of the inverse subgroup element. Thus this is an
equivalence between the restriction of `smoothContragredient ρ` and the smooth
contragredient of the restricted representation. Its forward and inverse
evaluation lemmas say that the same functional has the same value on every
original vector.

The provenance is internal, from the existing definitions of smooth vectors,
smooth part and smooth contragredient and the cited published open-subgroup
comparison. No admissibility, compactness, finite dimension, local compactness
or Haar measure is used. Openness of `H` is essential to this construction.
It is a comparison of the complete smooth duals, rather than a map defined
only on selected ambient functionals.
