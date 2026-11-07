# Whole root-map transport and actual polynomial Steinberg factors

This internal prerequisite derives the actual polynomial factor law used by
`SteinbergOrbitImageDescent` from coefficient compatibility of entire supplied
normalized root homomorphisms. It then derives descent of the full image ideal
for the canonical Steinberg product under explicit compatible-root and orthogonal
block hypotheses. It does not construct compatible choices or orbit blocks.

## Whole root maps and their coefficient compatibility

Let `k` and `K` be arbitrary fields in universe `u`, with `Algebra k K`, and let
`G` be an affine group scheme over `k`. Fix a split pinning `p` of the actual
base change of `G` to `K`. For a supplied normalized simple-root parametrization
`x`, its `coefficientCurve k K G` is the entire morphism from the standard
additive line to the base-changed group, viewed as an
`MvPolynomial (Fin 1) K`-valued point of the original group through
`Lie.affineBaseChangeEquiv`.

`PolynomialGalois.lineConjugate` applies a `k`-algebra automorphism of `K` to
all coefficients of this one-variable algebra and fixes its variable.
`SplitPinning.RootMapsGaloisCompatible` is a Prop-valued definition: for every
automorphism and every simple root, this coefficient action on the entire curve
equals the curve indexed by the supplied permutation representation on the
simple-root support. This is a generic-morphism condition, including over finite
fields; no existence of such a representation or compatible family is asserted.

`VectorGroup.scalarPoint_eq_algSpec_aeval` identifies a scalar point on an
affine test with the spectrum of polynomial evaluation. Its proof uses the
standard vector coordinates and naturality of `Scheme.ΓSpecIso`.
`coefficientCurve_evaluate` consequently identifies substitution by any element
of any coefficient algebra over `K`, with compatible scalar tower over `k`,
with the actual root value on that affine test.
`coefficientCurve_evaluate_one` identifies substitution at one with
`GaloisPointComparison.baseChangeCoeffEquiv` of the canonical unit point.

The polynomial composition identity `aeval_one_comp_conjugate` says that
evaluation at one intertwines coefficient conjugation with the given field
automorphism. Applying this identity to the whole root curve proves
`RootMapsGaloisCompatible.unitPoints`: whole-map compatibility supplies the
actual `UnitPointsGaloisCompatible` premise of canonical opposite-pair and
reflection-point transport.

## Actual factors on the renamed polynomial test

Fix equivalences `d : Fin r ≃ I` and `e : Fin r ≃ p.base.support`, supplied
normalized root maps `x`, and supplied reflection representatives `n`.
`coordinateTestIso_coordinate` proves that the standard coordinate indexed by
`j` pulls back along the actual coordinate-test isomorphism to the polynomial
variable indexed by `d j`.

For `i : I`, `factor_eq_substitutedCurve` identifies the actual factor already
defined in `SteinbergOrbitImageDescent` with the product, in the same order, of
the whole curve for `x (e (d.symm i))` after substituting `X i`, and the
coefficient extension of the actual rational point
`(n (e (d.symm i))).point`. The proof uses naturality of root evaluation,
multiplicativity of the base-change comparison, and
`Lie.affineBaseChangeEquiv_constantPoint` for the constant representative.

`rootCoordinateAction` transports the supplied simple-root permutation
representation to `I` along `d.symm.trans e`. Its action is exactly
`(d.symm.trans e).symm` composed with the root permutation and
`d.symm.trans e`. `rootCoordinateAction_root` proves that it induces the
specified simple-root action.

`orbitAction_comp_aeval_X` proves that substituting `X i` and then conjugating
coefficients and permuting target variables equals conjugating the one-variable
coefficients and then substituting the permuted variable. This proves
`coefficientCurve_substitute_galois`. The companion identity
`orbitAction_comp_coefficients` handles constant representative points.
Together with the actual factor formula, these prove `factor_orbitAction`:
whole-root-map compatibility and rational coefficient compatibility of the
supplied reflection points imply the actual polynomial factor law. Compatibility
of arbitrary reflection representatives is not inferred.

## Image-ideal descent and remaining obligations

`definingIdealDescent_of_compatibleRootMaps` additionally assumes `IsGalois k K`.
It uses the canonical reflection representatives determined by `x`, an original
commutative acting group `T` and inclusion `j`, an actual identification of
`p.torus` with the base change of `T` commuting with the inclusions, and the
ordinary character-lattice Galois law for the supplied simple-root action.
Whole-map compatibility supplies unit-point compatibility; canonical
opposite-pair uniqueness then supplies rational coefficient transport of the
canonical reflection points.

The supplied list of coordinate blocks must flatten to `List.ofFn d`, each
block must be preserved up to list permutation by the transported coordinate
action, and distinct roots in each block must be pairwise orthogonal. The
canonical representatives are root-generated, so the published orthogonal-root
commutation theorem supplies within-block factor commutation. The proved factor
law and `definingIdealDescent_of_orthogonal` then give
`DefiningIdealDescent` of the full kernel ideal sheaf of the actual canonical
Steinberg morphism along the original scheme base change. There is no
finite-degree assumption.

The provenance is internal composition of the existing actual-root,
canonical-representative, affine-point, polynomial-action and image-descent
constructions; no new literature theorem is asserted. Existence of compatible
pinnings and root maps, availability of the required orthogonal invariant
blocks, the split immersion and quotient calculations, exceptional even-type-A
substitutes and rational lifting remain separate obligations. This unit neither
proves the parent quasi-split quotient statement nor asserts a global rational
section in exceptional even type A.
