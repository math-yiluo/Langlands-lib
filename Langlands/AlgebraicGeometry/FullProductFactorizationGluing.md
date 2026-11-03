# Gluing full-product factorization loci

This internal helper derives a global full-product factorization criterion
from the published full-product sieve, its comparison with products in `Over S`,
and `ClosedSieveAffineTests.glue`. No literature statement is attributed to this
particular interface.

`FullProductFactorization.AffineTargetRepresentable` fixes an arbitrary scheme `S`
and an object `X` over it. It requires an actual closed representative for
each closed immersion into `X ⊗ Y` when `Y` is affine, with the factorization
criterion on every affine test scheme.
`FullProductFactorization.of_affine_targets` proves that this premise supplies a
representative and criterion for every target `Y` and every test scheme.
The premise remains an obligation of the caller; this helper does not construct
the affine representative or prove the final projectivity-based theorem.

The proof restricts `Y` to each affine open `U` and pulls the original closed
immersion back along `X ◁ U.ι`. The universal property of this pullback identifies
factorization of the full product through the restricted closed subscheme with
the original factorization after composition with `U.ι`. The affine premise
therefore represents the restricted full-product sieve on affine tests.

The full-product sieve is closed for the fpqc topology. Since that topology
contains the Zariski topology, the imported gluing theorem extends each
affine-test criterion to all tests and glues the local closed subschemes.
Giving the resulting scheme its induced structure map to `S` produces the
required object and closed immersion in `Over S`. The published
`exists_over_lift_iff` and `mem_iff_over` translate the resulting equivalence
to the exact equation `q ≫ d = X ◁ t`.

All schemes and test schemes retain arbitrary universe `u`. There is no
flatness, projectivity, finite-generation, or finiteness assumption in this
gluing step.
