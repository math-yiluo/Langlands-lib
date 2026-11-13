# Semilinear generic comparison of actual integral descent solutions

This internal construction recovers the prescribed generic group from an actual
affine integral descent solution. All rings, fields, schemes and groups use
arbitrary common universe `u`. It derives its statements from the actual
pullback, solution, integral-model, fpqc affineness and Galois homomorphism
descent APIs; it asserts no new external existence theorem.

## Square transport

For a commuting square `c ≫ b = e ≫ d`, `squareSolutionComparison` is the inverse
square comparison followed by the pullback of a supplied integral isomorphism
`t` and a supplied generic identification `n`.

`squareSolutionComparison_semilinear` assumes `a ≫ b = b`, `v ≫ e = e` and
`v ≫ c = c ≫ a`. The integral isomorphism must intertwine a supplied semilinear
isomorphism `E` with canonical transport, and the generic identification must
intertwine the same `E` after pullback. Naturality moves `t` through the square,
its semilinear law replaces the resulting composite, and canonical square
coherence cancels the two inverse comparisons. Thus the actual comparison
intertwines canonical transport on both generic groups.

## Integral-model specialization

The integral coefficients are domains `R` and `A` with specified fraction
fields `K` and `L`, algebras forming both scalar towers from `R` to `L`, and a
flat surjective map `Spec A → Spec R`. The supplied `N` is an actual integral
model over `A` of the scalar extension of a group `G` over `K`. A supplied datum
`D` on `N.group` has an actual solution `s`, with affine underlying scheme.
The supplied `hN` asserts smoothness of the actual structure morphism of `N`.

`solutionCoefficientSquare` proves equality of the two scheme maps using the
scalar-tower identities. `solutionModel_baseChangeGenericIso` identifies the
existing coefficient comparison for `solutionModel` with `squareComparison`:
both preserve the projection to `s.obj`, and nested-pullback extensionality
therefore gives equality. `solutionGenericComparison_eq_square` identifies the
previously constructed generic comparison with `squareSolutionComparison`.

`solutionGenericComparison_semilinear` specializes square transport to these
coefficients. Its explicit inputs are the integral base map `a`, the generic
base map `v`, their commuting identities, an actual isomorphism `E : a*N ≅ N`,
and its two intertwining laws. The variant
`solutionGenericComparison_semilinear_of_component` derives the integral law
from a supplied normalized component of the actual datum using
`Solution.semilinear`; it still requires the generic intertwining law.

## Galois recovery

`genericGroup_isAffineHom` transfers affineness from an actual model's generic
fibre through its prescribed generic isomorphism.
`affine_of_baseChanged_integralModel` reflects this along the fpqc field
extension, proving affineness of `G` from `N` without an extra hypothesis.

`SolutionGenericGaloisCompatible` is the Prop-valued condition that the actual
comparison intertwines canonical transport for every `K`-automorphism of `L`.
`solutionGenericGaloisCompatible_of_semilinear` derives that condition from the
integral and generic intertwining laws above, supplied for each automorphism.

Assuming `IsGalois K L`, `solutionGaloisGenericIso` applies the published
`Descent.GaloisHom.iso` to that compatible comparison. The source is affine
because it is the generic fibre of the affine solution; affineness of the
target follows from `N` as above. No finite-degree hypothesis is required.
`baseChange_solutionGaloisGenericIso` uses exact recovery of the descended
homomorphism and isomorphism extensionality to recover the full original
comparison after scalar extension.

`ofGaloisCompatibleSolution` installs this descended generic isomorphism in
the actual smooth model of `s.obj`. Its smoothness theorem uses fpqc reflection
already proved for the actual solution.
`isoOfGaloisCompatibleSolution` applies the exact recovery equation to
`isoOfSolutionGenericRecovery`. It therefore identifies the coefficient
extension of the constructed model with `N` over the identity of the
prescribed generic group, retaining `s.iso` as its integral group isomorphism.

## Remaining obligations

The actual datum, its affine solution, its normalized components, and the
generic semilinear laws remain supplied inputs. This unit does not construct
the integral semilinear maps or a coherent datum from stable integral points.
Those inputs must still be derived to prove KP Fact 2.10.16 without added
hypotheses. This contribution is a prerequisite, not a proof of
`UnramifiedSmoothModelDescentStatement`.
