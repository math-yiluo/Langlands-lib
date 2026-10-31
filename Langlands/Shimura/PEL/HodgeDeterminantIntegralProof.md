# Integral coefficients of the actual Harris order Hodge determinant: proof

Authors: Worker 1096 wrote the Lean proof and this documentation and checked
them. No code from other drafts is used.

`Langlands.Shimura.CentralSimpleUnitaryData.kottwitzIntegralHodgeDeterminantCoefficients`
proves the exact proposition `D.KottwitzIntegralHodgeDeterminantCoefficients C`
from `Langlands.Shimura.PEL.HodgeDeterminantIntegralStatement`. The theorem's
type is exactly the statement constant applied to its own binders, in the same
order. Those binders are the arithmetic types `E K A : Type`, their field,
number-field and algebra instances, the scalar towers `IsScalarTower E K A` and
`IsScalarTower ℚ E A`, and the implicit `n` and `Φ`. The statement file also
declares `[IsScalarTower ℚ K A]`, but its definition does not use that
instance, so Lean drops it from the statement. The proof file omits it as well,
so the theorem has no extra hypothesis.
The proof introduces the premise `IsCMSection E K Φ` and does not use it. Fix a
finite `ι : Type`, a family `a : ι → D.harrisHodgePELIntegralOrder C` and an
exponent `d : ι →₀ ℕ`. The theorem proves that
`(D.kottwitzHodgeDeterminant C (fun i => (a i : A))).coeff d` is integral over
`ℤ`.

The proof assumes no integral lattice on the Hodge summand and no basis in
which the order acts integrally. It builds the needed finitely generated
`ℤ`-module from the actual order. Every auxiliary lemma below is proved in
this file. The only result taken from Mathlib for the integrality step is
`isIntegral_of_smul_mem_submodule`. Let `A` be an `R`-algebra that is a domain
and `M` a torsion-free `A`-module. That lemma says `x ∈ A` is integral over `R`
if `x • N ⊆ N` for some finitely generated nonzero `R`-submodule `N` of `M`.
Here `R = ℤ` and `A = M = F` is a field.

## Notation

Write `h₀ = (D.realPositiveKottwitzHom C).val.hom`. Its identity Hodge summand
is `V₁ = RegularHodge.submodule h₀` inside `W = ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)`.
`D.kottwitzHodgeDeterminant C a` is, by definition,
`RegularHodge.determinantPolynomial h₀ (fun i => 1 ⊗ₜ (1 ⊗ₜ a i))`. That is
`HodgeDeterminant.polynomial` of the left actions on `V₁`, computed in
`Module.finBasis ℂ V₁`. For a basis `b` indexed by `κ` and endomorphisms
`f i`, `HodgeDeterminant.polynomial b f` is the determinant of the matrix with
entries `∑ i, C (toMatrix b b (f i) r j) * X i`.

## Determinant expansion (`Langlands.Shimura.HodgeDeterminant`)

These lemmas hold over any commutative ring `R`.

**`assignmentDegree`.** For a column assignment `s : κ → ι`, this is the
exponent `∑ j, Finsupp.single (s j) 1`. It counts how often each index occurs
in `s`.

**`det_linearForms`.** Let `B : ι → Matrix κ κ R`. The determinant of the
matrix with entries `∑ i, C (B i r j) * X i` equals

    ∑ s : κ → ι, monomial (assignmentDegree s) (det (r, j ↦ B (s j) r j)).

The proof expands the Leibniz formula (`Matrix.det_apply`). It turns each
product of sums into a sum over assignments (`Fintype.prod_sum`) and exchanges
the sums over permutations and assignments. Each term
`∏ j, C (B (s j) (σ j) j) * X (s j)` is a monomial of exponent
`assignmentDegree s` (`C_mul_X_eq_monomial`, `monomial_sum_prod`).

**`coeff_det_linearForms`.** Taking the coefficient at `d` gives the sum of the
mixed determinants `det (r, j ↦ B (s j) r j)` over the assignments with
`assignmentDegree s = d`.

**`coeff_polynomial_mul_det`.** Let `b` be a basis of `M`, `f : ι → End R M`
and `w : κ → M`. Then

    (polynomial b f).coeff d * b.det w
      = ∑ over s with assignmentDegree s = d of b.det (j ↦ f (s j) (w j)).

Put `T = b.toMatrix w`. Then `matrix b f * T.map C` is the linear-form matrix
of the family `B i = toMatrix b b (f i) * T`. Column `j` of `B i` is
`b.repr (f i (w j))` (`LinearMap.toMatrix_mulVec_repr`). Multiplicativity of
the determinant gives `C (b.det w) * polynomial b f = det (matrix b f * T.map C)`.
The previous lemma expands the right side, and each mixed determinant
`det (r, j ↦ B (s j) r j)` equals `b.det (j ↦ f (s j) (w j))`.

## Integrality from a spanning family

**`multilinear_mem_span`.** Let `φ` be multilinear over a commutative semiring
`S`, `G` a finite family and `w j ∈ span S (range G)` for every `j`. Then
`φ w` lies in the `S`-span of the values `φ (G ∘ r)` for `r : κ → γ`. The proof
writes each `w j` as a combination of the `G k` and uses
`MultilinearMap.map_sum` and `MultilinearMap.map_smul_univ`.

**`isIntegral_coeff_polynomial`.** Let `F` be a field, `b` a finite basis of
an `F`-vector space `V` and `f : ι → End F V`. Suppose a finite family
`G : γ → V` spans `V` over `F` and `f i (G k) ∈ span ℤ (range G)` for all `i`
and `k`. Then every coefficient of `polynomial b f` is integral over `ℤ`.

Let `N ⊆ F` be the `ℤ`-span of the finitely many values `b.det (G ∘ r)`,
`r : κ → γ`. Then:

- `N` is finitely generated, being spanned by a finite set.
- `N` is nonzero. Otherwise every `b.det (G ∘ r)` would be zero. Every vector
  of `b` lies in the `F`-span of `G`, so `multilinear_mem_span` over `F` would
  give `b.det b = 0`, contradicting `b.det b = 1` (`Module.Basis.det_self`).
- `c = (polynomial b f).coeff d` maps `N` into `N`. It suffices to check
  `c * b.det (G ∘ r)` for a generator. By `coeff_polynomial_mul_det` it is a
  sum of values `b.det (j ↦ f (s j) (G (r j)))`. All their arguments lie in
  `span ℤ (range G)` by hypothesis, so by `multilinear_mem_span` over `ℤ` (with
  `b.det` restricted to `ℤ`) they lie in `N`.

`isIntegral_of_smul_mem_submodule` then makes `c` integral over `ℤ`.

## Hodge projection (`Langlands.Shimura.RegularHodge`)

Let `B` be a real algebra and `h : ℂ →ₐ[ℝ] B`.

**`hodgeProjection h`.** This is the `ℂ`-linear projection
`Submodule.projectionOnto` from `ℂ ⊗[ℝ] B` onto `submodule h` along
`conjugateSubmodule h`. The two summands are complementary by the published
`RegularHodge.isCompl`.

**`hodgeProjection_mul`.** The projection commutes with left multiplication:
`hodgeProjection h (b * x) = leftAction h b (hodgeProjection h x)`. Write
`x = p + q` with `p ∈ submodule h` and `q ∈ conjugateSubmodule h`. Then
`b * p ∈ submodule h` by the published `RegularHodge.mul_mem`. Also
`b * q ∈ conjugateSubmodule h`, because `conjugateSubmodule h` is by definition
`submodule (h.comp conjAe)` and `mul_mem` applies to that homomorphism too.
Hence the projection of `b * x` is `b * p`.

**`isIntegral_coeff_determinantPolynomial`.** Let `B` be finite-dimensional,
`G : γ → ℂ ⊗[ℝ] B` a finite family spanning over `ℂ`, and
`a : ι → ℂ ⊗[ℝ] B` with `a i * G k ∈ span ℤ (range G)`. Then every coefficient
of `determinantPolynomial h a` is integral over `ℤ`. This is
`isIntegral_coeff_polynomial` for the basis `Module.finBasis ℂ (submodule h)`,
the left actions `leftAction h (a i)` and the projected family
`k ↦ hodgeProjection h (G k)`:

- the projected family spans `submodule h`, being the image of a spanning
  family under a surjective map (`Submodule.range_projectionOnto`);
- by `hodgeProjection_mul`, `leftAction h (a i)` sends `hodgeProjection h (G k)`
  to `hodgeProjection h (a i * G k)`. That lies in the image of
  `span ℤ (range G)`, which is the `ℤ`-span of the projected family.

The `ℤ`-span of the projected family need not be a lattice in `submodule h`
(it need not be discrete or free of full rank), and the proof does not claim
that it is. `isIntegral_coeff_polynomial` only uses that it is preserved by
the left actions and spans over `ℂ`.

## Specialization to the Harris order (`Langlands.Shimura.CentralSimpleUnitaryData`)

The order `D.harrisHodgePELIntegralOrder C` is a finite `ℤ`-module by the
published instance `harrisHodgePELIntegralOrder_finite`.
`Module.Finite.exists_fin` gives generators `g : Fin N → order` with
`span ℤ (range g) = ⊤`. Let `φ : A →+* W` be `x ↦ 1 ⊗ₜ (1 ⊗ₜ x)`, the
composite of the two `includeRight` algebra maps, and put `G k = φ (g k)`.

- **Order image.** If `x` lies in the order, then `φ x ∈ span ℤ (range G)`:
  write `x = ∑ k, c k • g k` with integers `c k` and apply the additive map `φ`.
- **Spanning.** Let `e = Module.finBasis ℚ A` and let `eW` be the `ℂ`-basis of
  `W` obtained from `e` by base change twice (`TensorProduct.basis`). Then
  `eW j = 1 ⊗ₜ (1 ⊗ₜ e j) = φ (e j)`. The published
  `exists_int_multiple_mem_harrisHodgePELIntegralOrder` gives an integer
  `m ≠ 0` with `m • e j` in the order. Then
  `eW j = (m : ℂ)⁻¹ • φ (m • e j)` lies in the `ℂ`-span of `G`. So `G` spans
  `W` over `ℂ`.
- **Stability.** `a i * g k` lies in the order because the order is a
  subalgebra. Hence `φ (a i) * G k = φ (a i * g k) ∈ span ℤ (range G)`.

`isIntegral_coeff_determinantPolynomial` for `h₀`, the family `G` and
`i ↦ φ (a i)` proves the target. Its polynomial is the target's polynomial by
definition. The proof gets `FiniteDimensional ℚ A` without `IsScalarTower ℚ K A`:
`A` is finite over `E` through the basis `D.totallyRealBasis`, and
`FiniteDimensional.trans ℚ E A` uses the tower `IsScalarTower ℚ E A`.

The proof covers constant and zero coefficients and the empty family. All
results are proved without `sorry` or new axioms. The theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The target is the integer-order specialization of Robert E. Kottwitz, *Points
on Some Shimura Varieties over Finite Fields* (1992), section 5, printed
pp.389–390, registered as `kottwitz-1992-points-shimura-finite-fields`. There
integrality is explained by passing to a finite field of definition and a
basis in which the order acts integrally. The implemented proof takes a
different route. It never chooses an integral lattice in the Hodge summand.
Instead it shows that each coefficient preserves the finitely generated
nonzero `ℤ`-module of mixed volumes of projected order generators. The
determinant-expansion, mixed-volume and Hodge-projection lemmas are internal
auxiliary results proved here by standard linear algebra.
