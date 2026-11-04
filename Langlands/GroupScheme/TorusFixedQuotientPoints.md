# Actual fixed quotient points from fixed orbit lines

This is an internal application of the extreme-weight constructions in
`TorusFixedOrbitLines` and the published rational-point fixedness criterion
in `SchemeActionRationalPoints`. It introduces no external result.

Let an actual group scheme `G` over a field act through a matrix
representation `ρ` with a finite coordinate index type. A supplied
subgroup `b : B ⟶ G` is exactly the stabilizer of a coordinate line on
every test scheme. A supplied morphism `q : G.X ⟶ Q` has exactly its
right-coset fibers on every test.

`FlagCore.quotient_eq_iff_orbitVec_smul` proves that equality of the
quotient sections of rational points `g,h` is equivalent to
`ρ(h)e_j` being a scalar multiple of `ρ(g)e_j`. It specializes the
actual line-stabilizer identity to the base test, uses the published
comparison between point matrices and rational matrices, then multiplies
by `ρ(g)` or its inverse.

For the remaining constructions, the field is algebraically closed.
An actual smooth group `T` maps to `G` through `i`; `Q` is separated
over the field. A supplied action `a` of `G` on `Q` is compatible
with left multiplication under `q`. A finite-parameter family `τ`
parametrizes exactly the image of the rational points of `T`.

`FlagCore.isFixed_quotient_iff_isTorusFixed` identifies the
all-test fixedness of `g ≫ q` for `a.restrict i` with the rational
fixed-line predicate for `ρ(g)e_j` and `τ`. The proof first applies
`SchemeAction.isFixed_iff_rationalPoints`, which uses smoothness of
`T` and separatedness of `Q`. It then uses the parametrization and the
preceding exact quotient-fiber calculation. No reducedness hypothesis
on `Q` is needed.

`FlagCore.twoTorusFixedQuotientPoints` takes in addition the actual
closed-orbit condition `IsClosedOrbit` for the coordinate line, a
simultaneous integral-weight diagonalization for `τ`, and one rational
quotient section `g ≫ q` that is not fixed. It constructs an injection
from `Bool` into the actual rational sections of `Q` fixed on every
test and refinement. The fixedness comparison gives a nonfixed orbit
line. Two extreme-weight contractions yield nonproportional fixed
orbit lines. Their quotient sections are fixed by the same comparison,
and are distinct by the exact quotient-fiber calculation. The injection
selects these two sections.

The quotient, its exact fibers, the all-test line stabilizer, compatible
action, torus parametrization and diagonalization, closed-orbit property,
and a nonfixed rational quotient section remain explicit geometric
inputs. The construction does not establish their existence or a
normalizer representative, and does not prove positive-root uniqueness
or a fixed-point dimension bound.
