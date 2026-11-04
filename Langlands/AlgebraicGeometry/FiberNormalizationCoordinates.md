# Fibre normalization coordinates from the original algebra

This derived internal construction supports the relative-dimension
sublevel theorem needed for the pure-dimensional fibre property in
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed pp. 5–6, Theorem 3.4(2). The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The construction is an internal prerequisite, not a separately numbered
assertion of Conrad. Worker 105 is the author.

`FiberNormalizationCoordinates R S p` records an actual finite family
of elements of S. Evaluation at their images `1 tensor s_i` gives a
polynomial map over the actual residue field of p into the actual fibre
`p.Fiber S = p.ResidueField tensor[R] S`. The record includes proofs
that this map is injective and finite, and that the fibre's ring Krull
dimension is its natural-number rank, cast into `WithBot ENat`.

`fiberNormalizationCoordinates R S p` constructs such a record for every
finite-type commutative R-algebra S and every prime p whose fibre is
nonzero. The universes of R and S are independent. The construction
chooses from the proved existence theorem
`exists_finite_injective_fiber_aeval`; no normalization-existence
hypothesis is supplied by the caller.

The implemented proof starts with Mathlib
`exists_finite_inj_algHom_of_fg` applied to the actual finite-type
residue-field algebra. For each variable image, Mathlib
`Ideal.Fiber.exists_smul_eq_one_tmul` supplies a multiplier in R outside
p that turns that image into `1 tensor s` for some s in S. The residue of
each multiplier is nonzero. Scaling each polynomial variable by that
residue is an algebra automorphism: inverse scaling gives the inverse,
and polynomial extensionality verifies both compositions.

Composing the original normalization with this automorphism is still
finite and injective. Polynomial extensionality and the multiplier
identities identify the composite with evaluation at the images of
the chosen elements of S. The Library's integral injective
Krull-dimension comparison and polynomial dimension formula, imported
through `FiniteTypeDomainDimension`, then identify the fibre dimension
with the number of variables. The final definition chooses a record
from this proved nonempty collection.

S need not be a domain, R need not be Noetherian, and the structure map
R to S need not be injective. The nonzero-fibre assumption is necessary
for an injective polynomial normalization over a field. This result
concerns normalization of one actual fibre with coordinates from the
original algebra. It does not assert that the original R-polynomial
map is finite, nor varying-family dimension-sublevel openness,
retrocompactness, constructibility, or filtered descent. Those remain
separate obligations.
