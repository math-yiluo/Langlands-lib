# Matrix-coefficient integrals of the model as sums of Whittaker integrals

Module `Langlands.Representation.GodementJacquet.WhittakerModelInclusion`.

This module proves the inclusion `I₂ ⊆ I₃` for the actual coefficient model,
assuming convergence and rationality of every Whittaker integral on that model.
It then combines that inclusion with the unconditional `I₃ ⊆ I₂` of the
Library module `Langlands.Representation.GodementJacquet.WhittakerAveraging`.
This gives the target equality of
`Langlands.GodementJacquet.WhittakerModelComparisonStatement` under the same
assumption. The assumption is the separate proposition
`Langlands.GodementJacquet.ModelWhittakerRationalityStatement`. Nothing here
proves that proposition.

## Source and provenance

Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer. J.
Math. 105 (1983), Section (5.2), printed 420–421. The source writes each smooth
functional on an admissible function model as a finite combination of compact
averages of evaluations. It then uses the substitution
`Φ₁(x) = ∫_Ω Φ(ω h⁻¹ x h) dω` to turn each resulting integral into a full-matrix
Whittaker integral. The source also takes for granted that the individual
integrals `Z(Φ, s, W)` "converge for Re(s) large, define rational functions of
`X = q^-s`". Here that fact is an explicit hypothesis.

The Lean route differs from the source in two ways.

* The conjugation is a plain change of variables `g ↦ h g h⁻¹` for the
  normalized Haar measure, which is both left and right invariant. Left
  invariance of `Φ` under a small compact open subgroup is used directly, so the
  source's averaged test function `Φ₁` never appears.
* The reduction to point averages works for every admissible model. It uses only
  the Library's finite orbit averages, applied to the vectors fixed by a compact
  open subgroup. There is no irreducibility assumption.

Every statement in this module is internal or derived. None is a published
theorem in this form.

The integrals use the canonical normalizations of
`Langlands.Representation.GodementJacquet.Zeta`:

* the normalized absolute value;
* the normalized Haar measure `μ = generalLinearHaar F.Carrier n` on
  `GL_{n+1}(F)`, with its Borel structure;
* the complex shift `jpssShift n = n/2`;
* the spectral point `q^(-s)`, where `q` is the residue cardinality.

`Z(Φ, s, f)` denotes `Padic.matrixIntegral F Φ s f`, that is
`∫ Φ(g) f(g) |det g|^s dμ(g)`. "Converges" means `Padic.MatrixConverges`, that
is, integrability of this integrand.

## Generic invariance lemmas

Let `G` be a topological group, `ρ` a smooth complex representation of `G` on
`V`, and `K` a compact open subgroup.

### `Langlands.GodementJacquet.apply_averageMap_of_invariant`

Let `Λ` be a linear functional with `Λ(ρ(k)v) = Λ(v)` for every `k ∈ K`. Then `Λ`
takes the same value at `v` and at the Library average
`Compact.averageMap ρ hρ K hK v`.

Proof: the average is the mean over the finite `K`-orbit of `v`
(`Compact.orbitMean_eq_finiteMean`). `Λ` is constant on that orbit, and the
number of orbit points is nonzero.

### `Langlands.GodementJacquet.eq_of_invariant_of_eqOn_fixedVectors`

Suppose two `K`-invariant functionals agree on the vectors fixed by `K`. Then they
are equal.

Proof: each functional takes the same value at `v` and at the average of `v`
(previous lemma). The average lies among the fixed vectors
(`Compact.averageMap_mem_fixedVectors`).

### `Langlands.GodementJacquet.exists_finsupp_eqOn_of_ker`

Let `E` be a finite-dimensional subspace, `ev i` a family of functionals, and `Λ` a
functional. Suppose `Λ` vanishes at every `e ∈ E` on which all `ev i` vanish.
Then there is a finitely supported `c` with `Λ e = ∑_{i ∈ supp c} c i · ev i e` for
all `e ∈ E`.

Proof: restrict all functionals to `E`, then apply
`FiniteDimensional.mem_span_of_iInf_ker_le_ker` and
`Finsupp.mem_span_range_iff_exists_finsupp`.

### `Langlands.GodementJacquet.apply_of_mem_fixedVectors_dual`

Let `Λ` be fixed by a subgroup `K` in the algebraic dual representation. Then
`Λ(ρ(k)v) = Λ(v)` for `k ∈ K`. This holds because `(ρ.dual k Λ)(x) = Λ(ρ(k⁻¹)x)`
by definition.

### `Langlands.GodementJacquet.exists_eq_sum_of_invariant`

Suppose the following hold:

* the vectors fixed by `K` form a finite-dimensional space;
* the family `ev i` and the functional `Λ` are all `K`-invariant;
* `Λ` vanishes at every `K`-fixed vector on which all `ev i` vanish.

Then there is a finitely supported `c` with `Λ v = ∑_{i ∈ supp c} c i · ev i v`
for every `v`.

Proof: the previous lemma gives `c` on the fixed vectors. The combination
`∑ c i • ev i` is `K`-invariant, so `eq_of_invariant_of_eqOn_fixedVectors`
extends the equality to all vectors.

### `Langlands.GodementJacquet.biSmoothCoefficient_apply`

`biSmoothCoefficient ρ Λ v g = Λ(ρ(g)v)`. This holds by `rfl`.

## Algebra of shifted rational values

The linear closure of shifted rational values is imported from the published
module `GodementJacquet.ZetaLinear`: `hasShiftedRationalValue_zero`,
`HasShiftedRationalValue.add` and `HasShiftedRationalValue.smul` (for any field
`F`, absolute value, measure and `q`). This module adds one lemma.

* `const_mul_mem_zetaSpan`: a Laurent span `zetaSpan values` is closed under
  multiplication by complex constants `C c`, since `C c` is the image of a
  constant Laurent polynomial.

## Conjugation change of variables

From here on, `F` is a canonical p-adic field with its canonical topology,
valuative and local-field structure, and the Borel structure on `GL_{n+1}(F)`.

### `Langlands.GodementJacquet.Padic.conjTest`, `conjTest_apply`

For a full-matrix Schwartz–Bruhat function `Φ` and `h ∈ GL_{n+1}(F)`, the function
`conjTest F Φ h` is `M ↦ Φ(h⁻¹ M h)` on all square matrices. It is locally
constant with compact support because `M ↦ h⁻¹ M h` is a homeomorphism of the
matrix space.

### `Langlands.GodementJacquet.Padic.matrixIntegrand_conj`

For every `u : GL_{n+1}(F) → ℂ`, the matrix integrand of `conjTest F Φ h` against
`y ↦ u(y h)`, evaluated at `h g h⁻¹`, equals `Φ(g) |det g|^s u(h g)`. The proof
is pointwise group algebra plus `det(h g h⁻¹) = det g`.

### `measurePreserving_conj`, `measurableEmbedding_conj`

Conjugation `g ↦ h g h⁻¹` preserves `μ`. This is right multiplication after left
multiplication, and `μ` is both left and right invariant (the Library unimodularity
instance). Conjugation is also a measurable embedding.

### `integrable_conj_iff`, `integral_conj`

The function `g ↦ Φ(g) |det g|^s u(h g)` is `μ`-integrable exactly when
`Z(conjTest F Φ h, s, y ↦ u(y h))` converges, and the two integrals are equal.
Proof: transport along the measure-preserving embedding above, then use the
pointwise identity.

## Point averages on the model

Let `σ` be smooth and `ℓ` a standard functional, and let `L` be a compact open
subgroup.

### `Langlands.GodementJacquet.Padic.glModelFunction_injective`

A vector of the coefficient model is determined by its model function.

### `Langlands.GodementJacquet.Padic.modelPointAverage`, `modelPointAverage_apply`

For `h ∈ GL_{n+1}(F)`, the point average is the linear functional on the model
`W ↦ ∫_{k ∈ L} W(h k) dμ(k)`. It is linear because model functions are continuous
(`glModelFunction_continuous`), hence integrable on the compact set `L`.

### `modelPointAverage_invariant`

The point average is invariant under the model action of `k ∈ L`. The model
action is right translation (`glModelFunction_translate`), and
`setIntegral_mul_right_of_mem` from `WhittakerAveraging` applies.

### `modelPointAverage_of_mem_fixedVectors`

On an `L`-fixed vector `W`, the point average at `h` is `μ(L) · W(h)`, where
`μ(L)` is the real mass `μ.real L`.

### `measureReal_openSubgroup_ne_zero`, `eq_zero_of_modelPointAverage_eq_zero`

The mass `μ(L)` is nonzero: `L` is open and nonempty, and it is compact, so its
measure is finite. Hence an `L`-fixed vector on which every point average
vanishes is zero.

### `Langlands.GodementJacquet.Padic.exists_eq_sum_modelPointAverage`

Assume the model is admissible. Let `Λ` be a smooth functional on the model and
`U` an open subgroup. Then there are:

* a compact open `L ≤ U`;
* a finite set `t ⊆ GL_{n+1}(F)`;
* coefficients `c`;

such that `Λ(W) = ∑_{h ∈ t} c(h) · A_{L,h}(W)` for every `W`. Here `A_{L,h}` is
the point average.

Proof: `Λ` is fixed by some open subgroup `K₀`. Choose a compact open
`L ≤ K₀ ⊓ U` (`exists_compactOpenSubgroup_le`). By admissibility the `L`-fixed
vectors form a finite-dimensional space. Apply `exists_eq_sum_of_invariant` to
the family of all point averages. Its kernel hypothesis is the previous lemma.

## The inclusion

### `Langlands.GodementJacquet.Padic.modelPointAverage_matrixIntegral`

Hypotheses:

* every `k ∈ L` satisfies `Φ(k M) = Φ(M)` for all matrices `M`;
* every `k ∈ L` satisfies `|det k| = 1`;
* `Z(conjTest F Φ h, s, ρ(h)w)` converges, where `ρ(h)w` is the right translate.

Conclusion: `g ↦ Φ(g) |det g|^s A_{L,h}(ρ(g)w)` is integrable, and its integral
is `μ(L) · Z(conjTest F Φ h, s, ρ(h)w)`.

Proof: `a(g) = Φ(g)|det g|^s` is invariant under left multiplication by `L`.
`integrable_conj_iff` gives integrability of `a(g) W(h g)`. Apply
`leftAverage_integral` (module `LeftAveraging`) with `Ω = L` to the function
`x ↦ W(h x)`. Note that `A_{L,h}(ρ(g)w) = ∫_{x ∈ L} W(h x g) dx`. Finish with
`integral_conj`.

### `Langlands.GodementJacquet.Padic.glModel_isAdmissible`

If `σ` is admissible, so is its coefficient model. The model map is a surjective
intertwiner (`modelMap_surjective`), and
`Unramified.SphericalExistence.isAdmissible_of_surjective` applies.

### `ModelRationality`, `exists_whittakerRationalValue`

`ModelRationality F ψ σ ℓ` is the conclusion of
`ModelWhittakerRationalityStatement` for fixed `F, ψ, σ, ℓ`. Every
`Z(Φ, s + n/2, W)` on the model converges for `Re s > a` and has a rational
continuation `R`. `exists_whittakerRationalValue` repackages this. It returns
`a` and `R` and records `R ∈ whittakerRationalValues F ψ σ ℓ`.

### `matrixIntegral_sum_modelPointAverage`

Let `f(g) = ∑_{h ∈ t} c(h) · A_{L,h}(ρ(g)w)` with `L` as above. Suppose every
`Z(conjTest F Φ h, s, ρ(h)w)` with `h ∈ t` converges. Then `Z(Φ, s, f)` converges
and equals `∑_{h ∈ t} c(h) · μ(L) · Z(conjTest F Φ h, s, ρ(h)w)`.

Proof: split the integrand into the finite sum, then apply
`modelPointAverage_matrixIntegral` to each term.

### `Langlands.GodementJacquet.Padic.exists_mem_jpssI3_of_coefficient`

Assume:

* `σ` is smooth;
* the model is admissible;
* `ModelRationality` holds;
* `Λ` is a smooth functional and `w` a model vector;
* `f(g) = Λ(ρ(g)w)` for all `g`.

Then for every `Φ` there is `R ∈ I₃` such that `f` has shifted rational value
`R` against `Φ`.

Proof:

1. Choose a compact open `K` fixing `Φ` on the left and inside the kernel of
   `|det|` (`exists_compactOpen_matrixTest_invariant`).
2. Write `Λ` as `∑ c(h) A_{L,h}` with `L ≤ K`.
3. For each `h`, the rationality hypothesis gives a half-plane `Re s > a(h)` and
   a value `R(h) ∈ whittakerRationalValues` for `Z(conjTest F Φ h, ·, ρ(h)w)`.
4. On `Re s > ∑_{h ∈ t} |a(h)|`, the previous lemma gives convergence and the
   identity `Z(Φ, s + n/2, f) = ∑ c(h) μ(L) Z(conjTest F Φ h, s + n/2, ρ(h)w)`.
5. Take `R = ∑_{h ∈ t} C(c(h) μ(L)) R(h)`.
   * `R` lies in `I₃` by `RationalContinuationLinear.linear_combination_mem_span`.
   * `R` continues the integral by `continuation_linear_combination` and
     `continuation_of_eq_on_right`.

### `matrixRationalValues_subset_jpssI3`

Assume `σ` is smooth, the model is admissible, and `ModelRationality` holds. Then
every element of `matrixRationalValues` of the model lies in `I₃`.

Proof: first show, by span induction, that every `f` in
`biSmoothMatrixCoefficients` of the model has, for each `Φ`, a shifted rational
value in `I₃`.

* Generators are bi-smooth coefficients. They are handled by the previous lemma
  through `biSmoothCoefficient_apply`.
* Zero, sums and scalar multiples are handled by the algebra lemmas above.

A given value `R` of `f` then equals the value found in `I₃`. This is the
uniqueness of rational continuation (`HasRationalContinuation.unique`, since
`q > 1`).

### `jpssI2_le_jpssI3_of_rationality`

Under the same hypotheses, `jpssI2` of the model is contained in `I₃`. This
follows from `Submodule.span_le`, since `I₂` is the Laurent span of
`matrixRationalValues`.

### `Langlands.GodementJacquet.whittakerModelComparison_of_rationality`

`ModelWhittakerRationalityStatement.{uF,uV}` implies
`WhittakerModelComparisonStatement.{uF,uV}`. The full original
`IsOfWhittakerType` hypothesis supplies:

* smoothness of `σ`;
* admissibility of `σ`, hence of the model by `glModel_isAdmissible`;
* the hypotheses of the rationality statement, which gives `ModelRationality`.

The equality is `le_antisymm` of `jpssI2_le_jpssI3_of_rationality` and the
Library theorem `Padic.jpssI3_le_jpssI2` of `WhittakerAveraging`. No other
premise is added. The proof uses only the standard axioms.
