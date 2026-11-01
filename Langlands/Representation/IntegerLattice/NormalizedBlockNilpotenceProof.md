# Nilpotence and commutation on actual generalized-weight blocks

Worker 1201. This proof targets the unchanged published proposition
`Langlands.CommutingTupleNormalizedBlockNilpotenceStatement`. It uses the actual
generalized-weight block and normalized differences from the imported Library
construction.

The proof takes each block vector into the ambient generalized eigenspace.
Mathlib identifies the maximal generalized eigenspace with the one at exponent
`Module.finrank ℂ V`. The restriction coercion equation, iterated by induction,
therefore proves that the restricted generator minus its labelled scalar
identity vanishes to that power. The normalized difference is its scalar
multiple by the inverse label, so `smul_pow` gives the same bound.

The restricted block generators are images of the standard generators under
the actual restricted lattice representation. The lattice is abelian, so the
images commute. Central scalar multiplication and subtraction of the identity
preserve commutation.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version of 9 July 2026, Appendix C.III, printed pp.279–280,
one-based PDF285–286, registered as
`renard-2026-representations-groupes-reductifs-padiques` (SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
These pages were read directly, and PDF286 was also inspected as an image.
Renard works in common triangular blocks and asserts that the normalized
strictly upper triangular parts are nilpotent and pairwise commuting. This
proof follows the accepted statement's derived basis-free formulation:
intersections of actual maximal generalized eigenspaces, every unit label
tuple, and the explicit ambient-dimension bound. The bound is derived from
Mathlib's generalized-eigenspace stabilization theorem, rather than from a
chosen triangular basis.

The registered 2010 errata
`renard-2010-corrections-complements` (SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`)
were checked at PDF18–19. Their C.III correction groups the entire
scalar-times-unipotent factor under its integer power, as already printed in
2026 PDF286. It does not alter this assertion.

All natural ranks and every carrier universe are retained. At rank zero the
coordinate quantifiers are empty. The proof makes no positivity assumption:
the ambient bound may be zero, and zero blocks are included. The
generalized-eigenspace membership equation itself then gives the required
vanishing. No nilpotence, commutation of the normalized differences, basis or
decomposition is supplied as a premise.

This proves the focused nilpotence and commutation step. It constructs no
common basis and establishes no multivariable product identity or further
whole-book claim.
