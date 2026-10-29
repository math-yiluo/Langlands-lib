# The homogeneous determinant of the regular Hodge representation

This module constructs the homogeneous determinant of a finite family of
endomorphisms and specializes it to the actual regular Hodge
representation constructed in `RegularHodge`. It proves homogeneity,
evaluation as the determinant of the corresponding linear combination,
evaluation in arbitrary commutative coefficient rings, and independence
of the module basis over an infinite domain.

## Source and provenance

The source is Robert E. Kottwitz, *Points on Some Shimura Varieties over
Finite Fields*, JAMS 5 (1992), section 5, printed pp.389–390
(PDF pp.17–18), registered as
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
No source-specific errata note was found in the project notes consulted.

On p.389 Kottwitz decomposes the complexified module into its identity
and conjugate Hodge summands. For a basis `a₁,…,aₜ` of the order, he
forms the determinant of `Σ Xᵢ aᵢ` acting on the identity summand. It is
homogeneous of degree the dimension of that summand. The same passage
states reflex-field and integral coefficient descent. Page 390 defines
the determinant condition by comparing this polynomial with the one
on Lie algebra sections.

The present derived unit constructs the complex polynomial and proves
its elementary algebraic properties. It uses the actual regular module
and fixed Kottwitz homomorphism from the Library. The generic determinant
construction allows any finite family of endomorphisms; the rational
specialization allows any finite family of algebra elements. Taking the
elements of an order basis gives the complex polynomial appearing in
the source, before coefficient descent. An order or an order basis is
not an input or a conclusion of this module.

## Generic determinant and hypotheses

In namespace `Langlands.Shimura.HodgeDeterminant`, the telescope is

```lean
{R : Type u} [CommRing R]
{M : Type v} [AddCommGroup M] [Module R M]
{ι : Type w} [Fintype ι]
{κ : Type t} [Fintype κ] [DecidableEq κ]
(b : Module.Basis κ R M) (f : ι → Module.End R M)
```

Here `ι` indexes the chosen endomorphisms, and `κ` indexes a finite
basis of the module. These indices have different roles. No target
polynomial is supplied. `matrix b f` has entries

\[
P_{jk}=\sum_{i\in\iota} C((\operatorname{toMatrix}_b f_i)_{jk})X_i
\]

in `MvPolynomial ι R`, and `polynomial b f` is the ordinary matrix
determinant of `P`.

`matrix_isHomogeneous` proves each entry homogeneous of degree one by
adding the scalar multiples of variables. `det_isHomogeneous` applies
to any square matrix with such entries, without requiring `ι` finite.
Its implemented proof expands `Matrix.det_apply'` as a sum over
permutations. Each term is a product of `card κ` entries multiplied
by a constant permutation sign, hence is homogeneous of degree
`card κ`. Summing gives the result.
`polynomial_isHomogeneous` applies this lemma to `matrix b f`.
These assertions include the empty matrix and zero polynomials;
they do not assert that the polynomial is nonzero or that its
total degree equals this number.

`eval_matrix` proves that evaluating `P` at `x : ι → R` gives
the matrix of the actual endomorphism `Σ i, x i • f i`.
The proof checks entries, distributes the ring homomorphism through
the sum, and uses linearity of `LinearMap.toMatrix`.
`eval_polynomial` then uses determinant compatibility with ring
homomorphisms and `LinearMap.det_toMatrix` to prove

\[
\operatorname{eval}_x(\operatorname{polynomial}(b,f))
=\det_R\left(\sum_i x_i f_i\right).
\]

For a further commutative ring `S`, a ring homomorphism `g : R →+* S`
and `x : ι → S`, `eval₂_polynomial` proves

\[
\operatorname{eval}_{g,x}(\operatorname{polynomial}(b,f))
=\det_S\left(\sum_i x_i\,g(\operatorname{toMatrix}_b f_i)\right),
\]

where `g` is applied entrywise. This is a determinant identity for
the displayed matrices over `S`; no scalar-extended module or
representation is supplied as an input. There is no field,
reducedness or infinitude assumption on `S`, so this identity also
holds when `S` has nilpotents.

`polynomial_basis_independent` additionally assumes `[IsDomain R]`
and `[Infinite R]`. For another finite basis `b'`, possibly indexed
by a different type in a further universe, both polynomials evaluate
to the same intrinsic linear-map determinant at every `x`.
`MvPolynomial.funext` over the infinite domain gives equality of
the polynomials. This is the implemented proof route; basis
independence over general finite coefficient rings is not asserted.

## Constructed Hodge representation

In namespace `Langlands.Shimura.RegularHodge`, the hypotheses are

```lean
{B : Type u} [Ring B] [Algebra ℝ B]
(h : ℂ →ₐ[ℝ] B) [FiniteDimensional ℝ B]
{ι : Type v} [Fintype ι]
```

`B` need not be commutative. The imported construction gives the actual
identity-action submodule `V₁ = submodule h` of `ℂ ⊗[ℝ] B` and the
algebra homomorphism `leftAction h` restricting left multiplication.
Finite dimensionality over `ℝ`, scalar extension, and the submodule
instance make `V₁` finite dimensional over `ℂ`.

For `a : ι → ℂ ⊗[ℝ] B`, `determinantPolynomial h a` uses
`Module.finBasis ℂ V₁` and the endomorphisms `leftAction h (a i)`.
`determinantPolynomial_isHomogeneous` specializes the generic theorem,
whose matrix size is now `finrank ℂ V₁`.
`eval_determinantPolynomial` proves that evaluation gives
`LinearMap.det (leftAction h (Σ i, x i • a i))`; linearity of the
constructed algebra homomorphism identifies the sum of actions with
the action of the sum. `determinantPolynomial_eq_basis` proves that
any finite complex basis of this same submodule computes the same
polynomial, using that `ℂ` is an infinite domain.

## Harris–Kottwitz specialization

The full arithmetic telescope in namespace
`Langlands.Shimura.CentralSimpleUnitaryData` is

```lean
{E : Type u} {K : Type v} {A : Type w}
[Field E] [NumberField E] [NumberField.IsTotallyReal E]
[Field K] [NumberField K] [NumberField.IsTotallyComplex K]
[Algebra E K] [Algebra.IsQuadraticExtension E K]
[Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
[Algebra ℚ A] [IsScalarTower ℚ E A]
{n : ℕ} (D : CentralSimpleUnitaryData E K A n)
{Φ : (E →+* ℝ) → (K →+* ℂ)}
(C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
{ι : Type t} [Fintype ι]
```

Here `E` is the totally real field in the Library notation, rather
than Kottwitz's reflex field. The three arithmetic universes remain
independent. `D.finite` supplies finite dimensionality over `K`;
transitivity over `ℚ` and scalar extension supply the finite
dimensionality needed by the Hodge construction. There is no
additional finite-dimensionality input in the specialized constants.

`kottwitzHodgeDeterminant D C a`, for `a : ι → A`, applies the
preceding determinant construction to
`B = ℝ ⊗[ℚ] A`,
`h = (D.realPositiveKottwitzHom C).val.hom`, and the double tensor
images `1 ⊗ (1 ⊗ a i)`. Thus it retains the fixed conjugated
Kottwitz homomorphism and the identity-action convention of
`RegularHodge`. Its underlying action is actual left multiplication
on `D.kottwitzHodgeModule C`.

`kottwitzHodgeDeterminant_isHomogeneous` gives homogeneity of degree
`finrank ℂ (D.kottwitzHodgeModule C)`.
`eval_kottwitzHodgeDeterminant` identifies every complex evaluation
with the determinant of `D.kottwitzHodgeAction C` applied to the
corresponding linear combination of these double tensor images.
Both proofs specialize the generic Hodge theorems after obtaining
the finite-dimensional instances from `D`.

## Scope and authorship

This unit constructs the complex homogeneous determinant from the
actual Hodge representation. Reflex-field coefficient descent,
integrality, a numerical signature formula for the whole regular
module, and the determinant condition on Lie algebra scheme sections
remain subsequent obligations. There is no representing scheme or
canonical-model assertion.

Worker 57 authored this derived construction and its proofs.
Development compilation and declaration inspection are verification
steps; independent semantic review and publication remain required.
