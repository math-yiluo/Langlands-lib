# Original counit evaluation under cartesian change of base

This internal unit compares the original counit evaluation with the actual
cartesian Weil base-change isomorphism on arbitrary compatible coefficient
algebras. It requires an original algebraic Weil restriction and a cartesian
square; it proves no representability theorem beyond the already published
cartesian base-change result, and makes no topological assertion.

Let `A`, `B`, `C`, `D`, `R`, and `E` be commutative rings. Supply algebra maps
`A → B`, `A → C`, `B → D`, `C → D` whose spectra form a cartesian square.
The coefficient ring `R` is a `C`-algebra and an `A`-algebra with the stated
scalar tower. The coefficient ring `E` is a `D`-algebra and a `B`-algebra with
its scalar tower. Let `f : R → E` be a ring homomorphism, retaining both
compatibility equations: its restriction to `A` is the original map through
`B`, and its restriction to `C` is the original map through `D`.

`weilRestrictionBaseChangeEvaluationTest` compares two actual test-scheme
morphisms over `Spec B`. The first evaluates over the new lower and upper
bases and then uses the published cartesian test isomorphism; the second
uses original-base evaluation and the restriction-of-scalars identification
of the lower test. The proof applies the pullback universal property. The
first projections agree by the published cartesian test-isomorphism and
evaluation projection formulas; the second agree since both maps lie over
the same original upper base. The proof keeps the specified coefficient
maps and both compatibility equations.

Let `X` be an algebraic space over `Spec B` whose actual Weil restriction to
`A` is algebraic. `baseChangedSpaceWeilEvaluation` is the composite that maps
an `R`-point of the scalar extension of this Weil space through the actual
cartesian Weil isomorphism, evaluates its counit along `f`, and then forgets
the upper base change to obtain an `E`-point of `X` over `B`.

`spaceWeilRestrictionEvaluation_baseChange` identifies that displayed
composite with original-base counit evaluation after the lower point
base-change identification. Its proof expands the three actual presheaf
pullbacks on the left and the two on the right, and applies the preceding
test-map equality through the presheaf functor. The coefficient rings are
arbitrary; this is not restricted to points over the new base ring itself.

The provenance is internal: the constructions and proof follow from the
published actual cartesian test isomorphism, original counit evaluation test,
base-change point equivalences, and presheaf functoriality. No finiteness,
separability, geometry, or topology hypothesis has been substituted for the
explicit cartesian-square and original algebraicity inputs.
