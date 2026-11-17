# The two finite affinoid algebras of the counterexample

This module builds the two presented affinoid `F₂`-algebras of the counterexample
to base change for weak strong atlas maps. It also builds the bounded maps
between them and the points of their spectra that the construction uses. All
declarations are in the namespace
`Langlands.Analytic.GroundFieldExtensionCounterexample`. The fields `F₂` and
`F₄` with their trivial norms come from `GroundFieldExtensionCounterexample/Fields`.

## Provenance

This is internal supporting material for the counterexample that the project
operator asked for in Task 7100: "K = F2 with the trivial norm, L = F = F4, the
two incomparable triple charts, Frobenius on one of them". It has no source in
the literature. Each finite algebra is realized as the Library's unit-radius
polynomial-locus chart (`PolynomialLocus.chart`, module `PolynomialLocusCharts`)
of a chosen finite polynomial presentation. Maps are built with the lemmas of
`PolynomialLocusTrivialNorm`.

## The algebras

- `SourceRing := Fin 2 → F₄` is `F₄ × F₄`, and `TargetRing := Fin 4 → F₄` is
  `F₄⁴`. Both are finite `F₂`-algebras.
- `sourcePresentation` and `targetPresentation` are the finite polynomial
  presentations chosen by `FinitePolynomialPresentation.ofFiniteType`.
- `sourceAlgebra` and `targetAlgebra` are the unit-radius charts
  `PolynomialLocus.chart _ (PositivePolyradius.unit _)` of these presentations.
  They are presented affinoid `F₂`-algebras.
- `sourceInclusion` and `targetInclusion` (written `ι` below) are the Library's
  algebra maps `PolynomialLocus.algebraMap` from the finite rings to these
  algebras. `sourceInclusion_surjective` and `targetInclusion_surjective` show
  that they are surjective, because the norm of `F₂` is trivial
  (`norm_eq_one_of_ne_zero`). `norm_source_le_one` and `norm_target_le_one` show
  that every element has norm at most `1`.

The Lean development does not prove that `ι` is injective, and nothing here
needs it.

## Maps

- `restrict : TargetRing →ₐ[F₂] SourceRing` keeps the first two factors.
  `restrict_apply` says `restrict a i = a i` for `i : Fin 2`, with `i` viewed in
  `Fin 4`.
- `restrictMap : BoundedAlgHom F₂ targetAlgebra sourceAlgebra` is
  `PolynomialLocus.lift` of `sourceInclusion ∘ restrict`.
  `restrictMap_targetInclusion` gives `restrictMap (ι a) = ι (restrict a)`.
- `frobenius : BoundedAlgHom F₂ sourceAlgebra sourceAlgebra` is
  `PolynomialLocus.lift` of `sourceInclusion` composed with Mathlib's
  `FiniteField.frobeniusAlgHom F₂ SourceRing`. That map raises every element to
  the power `Fintype.card F₂`. `frobenius_sourceInclusion` computes it on
  `ι`-values, and `frobenius_apply` gives `frobenius s = s ^ Fintype.card F₂`
  for every `s`. So `frobenius` is the `F₂`-linear squaring map. On each factor
  `F₄` it is the nontrivial field automorphism, but no lemma here states this.
- `sourceEvaluation k` and `targetEvaluation k` are the bounded `F₂`-algebra
  maps to `F₄` that evaluate at the factor `k`. They are lifts of
  `Pi.evalAlgHom`. `sourceEvaluation_sourceInclusion` and
  `targetEvaluation_targetInclusion` compute them on `ι`-values.

## Points of the spectra

- `sourcePoint k` and `targetPoint k` are the points of the Banach spectra
  pulled back from the point `BanachSpectrum.fieldPoint F₄` (the given norm of
  `F₄`) along the evaluation at the factor `k`.
  `sourcePoint_sourceInclusion` and `targetPoint_targetInclusion` give
  `point k (ι a) = ‖a k‖`.
- `apply_eq_zero_or_one`: in any normed commutative ring, let `s` satisfy
  `s ^ n = s` for some `n ≥ 2`. Then every point of the Banach spectrum takes the
  value `0` or `1` at `s`.
- `source_pow_card` and `target_pow_card`: every element `s` of either algebra
  satisfies `s ^ Fintype.card F₄ = s`. This follows from the surjectivity of
  `ι` and `FiniteField.pow_card`. `two_le_card_F₄` gives
  `2 ≤ Fintype.card F₄`. Hence `source_apply_eq_zero_or_one` and
  `target_apply_eq_zero_or_one`: every point of either spectrum takes only the
  values `0` and `1`.
- `comap_frobenius`: the map of spectra induced by `frobenius` is the identity.
  For a point `x` and `q = Fintype.card F₂` we have `x (s ^ q) = x s ^ q`, and
  `x s` is `0` or `1`.

The last fact makes the Frobenius twist in `GroundFieldExtensionCounterexample/WeakMap`
invisible on spectra over `F₂`. After base change to `F₄`, the base-changed
Frobenius no longer acts trivially on spectra; that part of the argument is not
in this module.
