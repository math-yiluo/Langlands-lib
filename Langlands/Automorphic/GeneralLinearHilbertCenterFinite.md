# Centre finiteness on smooth vectors of an irreducible unitary representation

Module `Langlands.Automorphic.GeneralLinearHilbertCenterFinite`. It proves that, for a
topologically irreducible unitary representation of any group whose restriction to the
archimedean group of `GL_n` over a number field is jointly continuous and normalized by the
whole representation, the centre of the enveloping algebra acts on the genuine smooth vectors
through a quotient of finite complex dimension.

## Setting

`F` is a number field, `n` a rank and `A = ArchimedeanMatrix F n` the mixed archimedean matrix
algebra, so `Aˣ` is `GL_n(F ⊗ ℝ)`. `E` is a complex Hilbert space, `𝒢` an arbitrary group,
`ρ : 𝒢 →* (E →L[ℂ] E)` and `ι : Aˣ →* 𝒢`. `R : Aˣ →* (E →L[ℂ] E)` is an archimedean
representation with `ρ (ι b) = R b`. The hypotheses of the main theorems are:

- `μ` is a Haar measure on `Aˣ` for a Borel structure;
- `R` is jointly continuous (`IsContinuousRepresentation R`);
- normalization: for every `g : 𝒢` there is `b : Aˣ` with `ρ g * R a = R (b a b⁻¹) * ρ g`
  for all `a`;
- `ρ` preserves the inner product;
- `ρ` is topologically irreducible (`IsTopologicallyIrreducible ρ`).

`D` is the genuine smooth carrier `DerivativeSmoothVectors 𝓘(ℝ, A) R`, and
`hilbertCenterAction F n R hR` is the Library's genuine enveloping action
`hilbertEnvelopingAction` restricted along `centerInclusion` to the enveloping centre `Z`.

## Main results

- `finite_quotient_ker_hilbertCenterAction`: the quotient of `Z` by the kernel of
  `hilbertCenterAction F n R hR` is a finite-dimensional complex vector space.
- `exists_ideal_hilbertCenterAction`: there is an ideal `J` of `Z` of finite complex
  codimension with `hilbertCenterAction F n R hR z v = 0` for every `z ∈ J` and every smooth
  vector `v`.
- `exists_ideal_smoothingFamily_eq_zero`: the same conclusion for a closed invariant subspace
  `M` of a unitary representation `ρ` on a Hilbert space `E`, when `M` is nonzero and minimal
  among nonzero closed invariant subspaces. Here `R = ρ ∘ ι` must be jointly continuous and
  normalized by `ρ`. The conclusion concerns families rather than smooth vectors. Let `u ∈ M`,
  let `κ'` be a smooth compactly supported function on `Aˣ`, and let `y` send each enveloping
  element `a` to a vector of `M`, additively and complex-linearly. Suppose
  `y 1 = ∫ κ'(g⁻¹) ρ(ι g) u dμ(g)`, and suppose that for every real direction `X` the orbit
  of `y a` along the real exponential curve of `X` has derivative `y (X̃ a)` at zero, where
  `X̃` is the generator of `X`. Then `y z = 0` for every `z ∈ J`. The proof restricts `ρ` to
  `M` (`invariantSubmoduleRepresentation`), which is unitary and topologically irreducible
  by minimality. The integral `y 1` is a genuine smooth vector (`isSmoothVector_smoothedVector`).
  `eq_hilbertEnvelopingAction_of_hasDerivAt` identifies every `y a` with the genuine enveloping
  derivative of that vector. `exists_ideal_hilbertCenterAction` then applies.

## Supporting results

- `finite_range_centerConjugationHom`: the actual archimedean group acts on `Z` by
  conjugation through finitely many automorphisms. The kernel of `centerConjugationHom` is
  open (`isOpen_ker_centerConjugationHom`), hence clopen, so it contains the identity
  component. Every element lies in the component of an element of `standardInfiniteCompact`
  (`compactComponentCoverage`). So the image equals the image of that compact subgroup, which
  is finite because an open subgroup of a compact group has finite index.
- `hilbertEnvelopingAction_representation`: translating a smooth vector by `b` conjugates the
  enveloping element by `b`. The proof is induction on the enveloping algebra
  (`enveloping_real_left_induction`), using `operator_representation_units` for real
  generators.
- `hilbertEnvelopingAction_derivativeMapLinear`: the enveloping action commutes with the
  smooth map induced by a bounded operator commuting with `R`.
- `hasDerivAt_exponentialOrbit`: the orbit of a genuine smooth vector along the real
  exponential curve `realLieExponentialCurve F n X` has derivative at zero equal to the genuine
  derivative in the matrix direction of `X`. In coordinates the curve is
  `t ↦ exp (t X)` (`coordinates_realLieExponentialCurve_val`), which is smooth with tangent
  `X` at zero.
- `eq_hilbertEnvelopingAction_of_hasDerivAt`: an additive, complex-linear family `y` of vectors
  indexed by the enveloping algebra, with `y 1` the value of a smooth vector `v` and with the
  exponential-curve derivatives `y (X̃ a)`, equals the family of genuine enveloping derivatives
  of `v`. The proof is induction on the enveloping algebra, using uniqueness of derivatives.
- `HasDerivAt.of_isometry`: a curve in a subspace has a derivative there once its image under
  an isometric linear inclusion has the image derivative.
- `exists_eq_mul_commute`: under normalization, each `ρ g` is `R b` followed by an operator
  commuting with `R`.
- `exists_hilbertEnvelopingAction_eq_smul`: an enveloping element fixed by every archimedean
  conjugation acts by a scalar on `D`. Its action commutes with `ρ` on `D`, and the Library's
  formal adjoint (`exists_hilbertEnvelopingAction_formalAdjoint`) supplies the pairing. The
  graph lemma `exists_unitaryIntertwiner_of_regularization_pairing` gives a bounded intertwiner
  extending it, and the Hilbert commutant lemma `exists_eq_scalar_of_unitary_commute` makes it
  scalar. The smooth vectors are dense by `dense_smoothVectors_units`.
- `centerOrbitPolynomial z` is the product of `X - γ z` over the finite set
  `centerConjugationFinset` of conjugations of `Z`. It is monic, vanishes at `z`, has degree
  at most the number of conjugations, and its coefficients are fixed by every conjugation.
- `exists_monic_aeval_hilbertCenterAction_eq_zero`: the coefficients of
  `centerOrbitPolynomial z` act by scalars, so every central operator is a root of a monic
  complex polynomial of degree at most the number of conjugations.
- `hilbertCenterAction_eq_zero_of_mul_self_eq_zero`: a central operator with square zero is
  zero. Among the finite products of conjugates of `w` that act by a nonzero operator, take
  the maximal ones; conjugation permutes them. The closure of the span of their images is
  closed and invariant and nonzero, hence everything. Multiplying a maximal product by `w`
  gives zero, so the formal adjoint of `w` has image orthogonal to that span. Hence the
  adjoint is zero, and so is `w`.
- In `Langlands.Algebra.UniformIntegral`, `finiteDimensional_of_isReduced_of_uniform`: a
  reduced commutative complex algebra whose elements are all roots of monic polynomials of
  degree at most `m` is finite-dimensional. Finitely many elements generate a
  finite-dimensional reduced subalgebra (`Algebra.finite_adjoin_of_finite_of_isIntegral`).
  This subalgebra is a product of copies of `ℂ` (`IsArtinianRing.equivPi`, with
  `IsAlgClosed.algebraMap_bijective_of_isIntegral`). Its primitive idempotents number at most
  `m` (`card_le_of_orthogonal_idempotents`), and they span it
  (`finrank_le_of_isReduced_of_finiteDimensional`). `rank_le` then bounds the rank of the
  whole algebra.

The main theorem applies the algebra lemma to `Z` modulo the kernel of the centre action.

## Provenance

This is a derived route to the centre finiteness needed for the comparison (9.40) in the proof
of Theorem 9.7.3 of Getz and Hahn, *An Introduction to Automorphic Representations* (2024),
printed pp. 265–266 (PDF pp. 277–278). There the `K`-finite vectors are placed in the
automorphic forms through the proof of Theorem 6.6.4, printed p. 172 (PDF p. 186). Their
`Z(g)`-finiteness comes from admissibility: an irreducible admissible `(g, K∞)`-module has an
infinitesimal character (Corollary 4.6.3, printed p. 125, PDF p. 140). Here it comes
from the unitary graph argument and Schur's lemma, which the Library proves in
`Langlands.Representation.Archimedean.UnitaryRegularizationGraph` and `UnitaryCommutant`. The
trace Casimir case, for a single matrix group, is
`Langlands.Representation.Archimedean.UnitaryMatrixCasimir`. The finite group of centre
conjugations stands in for the possibly disconnected archimedean group. No admissibility,
compactness of convolution operators or finite generation of the enveloping centre is used.
The module does not identify the centre action with any pointwise differential operator.
