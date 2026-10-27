# Unitarizability from square-integrable coefficients on a central quotient

Authors: Worker 380, with Worker 438. Worker 438 designed the nonvanishing and
zero-integral helpers in their shared draft (task
d67e4611-c5fe-44b8-8420-08d63b607cc6, draft revision 2). Worker 380 reviewed
and adapted them here and added the integral form and the main theorem.

`Langlands.squareIntegrableUnimodularUnitarity.{uG,uV}` proves the published
closed proposition
`Langlands.SquareIntegrableUnimodularUnitarityStatement.{uG,uV}` from
`Langlands.Representation.Unitary.SquareIntegrableStatement`. Its type is
exactly that proposition. The group and carrier universes stay independent.
The proof keeps the original algebraic carrier `V`, the actual quotient
`G ⧸ Subgroup.center G`, the given measurable space and Borel instance on it,
the given Haar measure `μ`, the compact-open cofinality hypothesis, and the
explicit right invariance `IsMulRightInvariant μ`. It adds no hypothesis. It
puts no norm, topology, completeness, or dimension bound on `V`. It also
supplies no functional, form, or unitary representation from outside.

## Implemented route

The main proof introduces the statement's binders and destructs
`IsSquareIntegrableModCenter ρ μ` into admissibility `hadm`, a unitary central
character datum `c`, and the `L²` hypothesis `hL2`. Smoothness is `hadm.1`.

### 1. A nonzero smooth functional

`exists_smoothDual_apply_ne_zero_of_compact_cofinal` takes a smooth `ρ`
and a vector `v ≠ 0`. Assuming compact-open cofinality, it gives
`ℓ : SmoothDual ρ` with `ℓ.1 v ≠ 0`. The proof is by contradiction. If every
smooth functional killed `v`, then `v` and `0` would have the same image in
the smooth bidual. The published `smoothBidual_injective_of_compact_cofinal`
then forces `v = 0`.

`exists_nonzero_smoothDual_of_irreducible_compact_cofinal` adds
irreducibility. `Representation.IsIrreducible ρ` makes `ρ.asModule` a simple
`MonoidAlgebra ℂ G`-module, so `V` is nontrivial (`IsSimpleModule.nontrivial`).
A nonzero vector and the previous lemma then give `ℓ : SmoothDual ρ` with
`ℓ.1 ≠ 0`.

### 2. Coefficients detect vectors

For any algebraic functional `ℓ`, `matrixCoefficientKernel ρ ℓ` is the
subrepresentation of vectors `v` with `matrixCoefficient ρ ℓ v g = 0` for all
`g`. Invariance uses `ρ (g * h) = ρ g * ρ h`. In
`eq_zero_of_matrixCoefficient_vanishes`, assume `ℓ ≠ 0`. The kernel is not
`⊤`: if it were, evaluating coefficients at `1` would give `ℓ = 0`.
Irreducibility (`eq_bot_or_eq_top`) then makes the kernel `⊥`. So a vector
whose coefficients all vanish is zero.

### 3. Zero diagonal integral

`UnitaryCentralCharacter.eq_zero_of_integral_coefficientNorm_sq_eq_zero` needs
only `μ.IsOpenPosMeasure`, which follows from `IsHaarMeasure μ`. Suppose
`c.coefficientNorm ℓ v` is in `L²` and `∫ (c.coefficientNorm ℓ v)^2 dμ = 0`.
`MemLp.integrable_sq` gives integrability of the square, and
`integral_eq_zero_iff_of_nonneg` gives vanishing almost everywhere. The square
is continuous by the published `continuous_coefficientNorm`, so
`Continuous.ae_eq_iff_eq` gives vanishing everywhere. At the class of each
`g`, this says `‖matrixCoefficient ρ ℓ v g‖ ^ 2 = 0`. Step 2 then gives
`v = 0`.

### 4. Integrability

The integrand is the published
`UnitaryCentralCharacter.coefficientProduct c ℓ u v` from
`Langlands.Representation.MatrixCoefficient.HermitianProduct`. Its value at
the class of `g` is `conj (ℓ (ρ g u)) * ℓ (ρ g v)`. For smooth `u` and `v`,
`integrable_coefficientProduct` applies `MemLp.integrable_mul` at exponents
`2, 2` (Hölder) to the two `L²` hypotheses, so the product of the two
coefficient norms is integrable. `Integrable.mono'` then uses the published
`aestronglyMeasurable_coefficientProduct` and the norm identity
`norm_coefficientProduct`.

### 5. The form and its laws

`coefficientProductIntegral c ℓ μ u v` is
`∫ q, c.coefficientProduct ℓ u v q ∂μ`. The published pointwise laws pass
through the integral:

- `coefficientProductIntegral_conj`: conjugate symmetry, from
  `integral_conj` and `coefficientProduct_conj`.
- `coefficientProductIntegral_self`: the diagonal is the real integral of
  `(c.coefficientNorm ℓ v)^2`, coerced to `ℂ`, from `coefficientProduct_self`
  and `integral_ofReal`.
- `coefficientProductIntegral_add_left`: additivity in the first argument,
  from `coefficientProduct_add_left` and `integral_add`. The integrability
  comes from step 4, with smoothness of every vector and the `L²` hypothesis
  for every vector.
- `coefficientProductIntegral_smul_left`: `(a • u, v) ↦ conj a * (u, v)`,
  from `coefficientProduct_smul_left` and `integral_const_mul`.
- `coefficientProductIntegral_translate`: invariance under acting by `ρ g` on
  both vectors. `coefficientProduct_translate` rewrites the integrand as a
  right translate by the class of `g`. `integral_mul_right_eq_self` then uses
  the supplied `IsMulRightInvariant μ`.

`coefficientProductForm` packages these as an `InvariantPositiveForm ρ` on
the original carrier. Its `inner` is `coefficientProductIntegral`, and
`coefficientProductForm_inner` records this definitionally. Mathlib's
`InnerProductSpace.Core` is conjugate-linear in the first argument, so its
`smul_left` field is exactly the conjugate-first law above. Nonnegativity of
the real part comes from `coefficientProductIntegral_self` and
`integral_nonneg`. Definiteness comes from the same identity,
`Complex.ofReal_eq_zero`, and step 3.

### 6. Conclusion

With `ℓ` from step 1 and the `L²` hypothesis `hL2 ℓ` for that functional,
the main theorem returns `⟨c.coefficientProductForm hadm.1 hirr ℓ.1 hℓ μ (hL2 ℓ)⟩`.
This is the existing `IsUnitarizable ρ`, namely
`Nonempty (InvariantPositiveForm ρ)`.

## Dependencies

Project imports: the target statement module;
`MatrixCoefficient.HermitianProduct` for `coefficientProduct` and its laws
(Worker 577, task 31021398-8156-4616-9e01-6f47821d43aa);
`MatrixCoefficient.NormRegularityProof` for `continuous_coefficientNorm`; and
`Smooth.Contragredient.AdmissibleDualityProof` for
`smoothBidual_injective_of_compact_cofinal`. Mathlib imports: `L2Space`,
`Group.Integral`, `Measure.OpenPos`, and `SimpleModule.Basic`. The Library's
separate `coefficientL2Form` in `MatrixCoefficient.CoefficientL2` is not used.
No tempered-unitarity, tempered-exhaustion, induction, or
equal-exponent-grouping result is used. No existing Lean/Markdown pair is
changed. The axioms used are `propext`, `Classical.choice`, and `Quot.sound`.

## Provenance

This proof implements an internal, derived generalization. It is not a
verbatim theorem of the source. The source for the argument is
W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995, §2.5, printed/PDF pp.28–29,
Proposition 2.5.4 (literature ID `casselman-1995-admissible-representations`,
SHA-256 `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`).
Its proof likewise chooses a nonzero smooth functional and integrates
products of its coefficients over `G/Z`. It gets convergence from the Schwarz
inequality. Casselman's form conjugates the second factor. Here the first
factor is conjugated to match Mathlib, as in the target statement's Markdown.
This reverses the arguments and leaves the diagonal unchanged. Worker 380 read
the text of pp.28–29. Worker 438 read both pages and visually checked the
displayed form on p.29. The proof route above is the Lean
implementation, which makes the algebraic, measure-theoretic and
irreducibility steps explicit.
