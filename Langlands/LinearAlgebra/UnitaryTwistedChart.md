# Charts of the special unitary group of a twisted matrix algebra

Module `Langlands.LinearAlgebra.UnitaryTwistedChart`, namespace
`Langlands.LinearAlgebra.UnitaryTwistedChart`.

## Setting

`K` and `M` are fields in one universe `u` with `Algebra K M`. `F` is an intermediate field
of `M/K`, `H = F.fixingSubgroup` and `m` is a finite index type. Write `N^σ` for the
entrywise image `N.map σ` and `Nᵀ` for the transpose.

`Cocycle F m` (structure) bundles

- `x : Gal(M/K) → GL m M`;
- `index_eq : H.index = 2`;
- `inner` and `outer`: the twisted projective cocycle law of the Library module
  `Langlands.LinearAlgebra.UnitaryTwistedDescent`, in exactly the form of the hypotheses
  `hin` and `hout` there: for `σ ∈ H` there is `c ∈ Mˣ` with `x(στ) = c · x(σ) x(τ)^σ`, and
  for `σ ∉ H` there is `c` with `x(στ) = c · x(σ) ((x(τ)⁻¹)^σ)ᵀ`;
- `r : Gal(M/K)` with `r_not_mem : r ∉ H`.

For `c : Cocycle F m`:

- `c.action` (abbrev) is `UnitaryTwistedDescent.galoisAction F …`, the action of
  `Gal(M/F)` on `Matrix m m M` by `N ↦ x(σ) N^σ x(σ)⁻¹`.
- `c.Alg` (abbrev) is its fixed `F`-subalgebra `c.action.fixed` of `Matrix m m M`. It is
  written `B` below.

## The involution

- `twistedAct_alg_of_mem`: every `σ ∈ H` fixes `B` under `twistedAct`.
- `twistedAct_of_not_mem_eq`: for `σ ∉ H` and `b ∈ B`, `twistedAct σ b = twistedAct r b`.
  The proof writes `σ = r (r⁻¹σ)` with `r⁻¹σ ∈ H` and uses `twistedAct_mul`.
- Assuming `[Normal K F]`: `isUnitary` restates the Library's
  `isUnitaryInvolution_outerInvolution`. `involution : FirstKindInvolution K B` (def) is
  `outerInvolution F … r` (the restriction of `twistedAct r`), with `K`-linearity from
  `outerInvolution_algebraMap`. `involution_val`: `τ(b) = x(r) (b^r)ᵀ x(r)⁻¹`.
- `restrictNormal_ne_one`: `r` restricts to a nontrivial automorphism of `F`.
- With `[Algebra.IsQuadraticExtension K F] [Algebra.IsSeparable K F]`: `restrictNormal_eq`
  identifies that restriction with `SU3Root.conjugation K F` (by the Library's
  `conjugation_unique`); `r_algebraMap` states `r(ℓ) = conjugation(ℓ)` on `F`; and
  `involution_algebraMap` states
  `τ (algebraMap F B ℓ) = algebraMap F B (SU3Root.conjugation K F ℓ)`.

## Charts

Let `S` be a commutative `K`-algebra and `ψ : M →ₐ[K] S`.

- `entryHom ψ : B →ₐ[K] Matrix m m S`, `b ↦ b^ψ`, and
  `chart ψ : S ⊗[K] B →ₐ[S] Matrix m m S`, the `S`-linear extension
  (`Algebra.TensorProduct.lift`); `chart_tmul`: `chart ψ (s ⊗ b) = s • b^ψ`.
- `chart_naturality`: for `g : S →ₐ[K] S'`,
  `chart (g ∘ ψ) ((g ⊗ id) y) = (chart ψ y)^g`.
- `outerMatrix ψ = GL.map ψ (x r)` (abbrev), written `X`. `chart_involution`:
  `chart ψ (τ_S y) = X (chart (ψ ∘ r) y)ᵀ X⁻¹`, where `τ_S = τ.baseChange S`.
  `chart_comp_involution`: `chart (ψ ∘ r) (τ_S y) = (X⁻¹ (chart ψ y) X)ᵀ`, obtained from the
  previous formula applied to `τ_S y` and `τ_S² = id`.
- `cocycleMatrix ψ σ = GL.map ψ (x σ)` (abbrev), written `Y_σ`. `map_of_mem`: for `σ ∈ H`,
  `b^σ = x(σ)⁻¹ b x(σ)`; `chart_comp_of_mem`: `chart (ψ ∘ σ) y = Y_σ⁻¹ (chart ψ y) Y_σ`.
  `map_of_not_mem`: for `σ ∉ H`, `b^σ = (x(σ)⁻¹ τ(b) x(σ))ᵀ`; `chart_comp_of_not_mem`:
  `chart (ψ ∘ σ) y = (Y_σ⁻¹ (chart ψ (τ_S y)) Y_σ)ᵀ`. The matrix identities `eq_conj_of_conj_eq`,
  `map_comp_eq`, `map_conj`, `map_conj_transpose` and `coe_glMap` are used here.

## Descent facts

Assume `[FiniteDimensional K M] [IsGalois K M]`.

- Instances: `FiniteDimensional F B`, and for nonempty `m`, `Algebra.IsCentral F B` and
  `IsSimpleRing B` (from the Library's `finiteDimensional_fixed`, `isCentral_fixed`,
  `isSimpleRing_fixed`), and `FiniteDimensional K B`.
- `finrank_alg`: `finrank F B = card m * card m`, from the descent isomorphism
  `c.action.descentEquiv : M ⊗[F] B ≃ₐ[M] Matrix m m M`.
- `exists_chart_eq` and `chart_surjective`: every `(descentEquiv z)^ψ` is a value of
  `chart ψ` (induction on `z`, using `descentEquiv (ℓ ⊗ b) = ℓ b`); hence the matrix units
  of `Matrix m m S` are values and `chart ψ` is surjective.
- `fieldPoint ψ = ψ|_F` (abbrev) and `scalarMap : F ⊗[K] S →ₐ[K] S ⊗[K] B`
  (`ℓ ⊗ s ↦ s ⊗ ℓ`). `chart_scalarMap`: `chart ψ (scalarMap z)` is the scalar matrix of
  `HermitianMatrix.tensorProj K F (ψ|_F) z`.

Now assume also that `F/K` is separable quadratic.

- `fieldPoint_comp_r`: `(ψ ∘ r)|_F = ψ|_F ∘ conjugation`.
- `exists_scalar` and `chart_pair_surjective`: the pair `(chart ψ, chart (ψ ∘ r))` is
  surjective onto `Matrix m m S × Matrix m m S`. The Library's `tensorProj_surjective₂`
  gives scalars with charts `(1, 0)` and `(0, 1)`; multiply them by preimages under each chart.
- `finrank_alg_base`: `finrank K B = 2 * (card m * card m)`.
- `chart_pair_injective`: the pair of charts is injective. The pair is an `S`-linear
  surjection between free `S`-modules with bases of the same cardinality
  (`Algebra.TensorProduct.basis` of a `K`-basis of `B`, and `Matrix.stdBasis` twice).
  Mathlib's `OrzechProperty.injective_of_surjective_of_injective` for commutative rings
  then gives injectivity.
- `conj_mul_conj`, `transpose_conj_mul` (matrix identities) and `eq_one_of_chart_eq_one`:
  if `y τ_S(y) = 1` and `chart ψ y = 1` then `y = 1`, because then also
  `chart (ψ ∘ r) y = 1` by `chart_involution`.

Assume finally that `m` is nonempty.

- `tensorProj_relativeNorm`: for `u ∈ (S ⊗[K] B)ˣ`,
  `tensorProj K F (ψ|_F) (relativeNorm K F B S u) = det (chart ψ u)`, where `relativeNorm` is
  the relative reduced norm of `Langlands.Algebra.CentralSimple.UnitaryPoints`. The proof
  regards `S` as an `F`-algebra through `ψ|_F`, applies `reducedNorm_naturality` along the
  `F`-algebra map `F ⊗[K] S → S`, `ℓ ⊗ s ↦ ψ(ℓ) s`, and then
  `SpecialLinearInnerForm.reducedNorm_eq_det_chartAlong` for the chart `descentEquiv`.
- `suChartHom ψ : specialUnitaryPoints F τ S →* SL m S` (def), `u ↦ chart ψ u`, with
  determinant one by the previous item. `suChartHom_injective` uses
  `eq_one_of_chart_eq_one` on the kernel. `suChartHom_surjective`: for `g ∈ SL m S`, take
  `y` with charts `(g, (X⁻¹ g⁻¹ X)ᵀ)` and `y'` with charts `(g⁻¹, (X⁻¹ g X)ᵀ)`. Joint
  injectivity gives `y y' = y' y = 1` and `y τ_S(y) = 1`. The relative norm of `y` is `1`
  because its two projections `tensorProj (ψ|_F)` and `tensorProj (ψ|_F ∘ conjugation)` are
  `det g = 1` and `det (X⁻¹ g⁻¹ X)ᵀ = 1`, and these projections are jointly injective
  (`tensorProj_injective₂`).
- `suChart ψ : specialUnitaryPoints F τ S ≃* SL m S` (def), with `suChart_val`.
- `suChart_naturality`: for `g : S →ₐ[K] S'`, the chart along `g ∘ ψ` of
  `specialUnitaryMap F τ g u` is the chart along `ψ` of `u` with `g` applied entrywise.
- `suChart_comp_of_mem`: for `σ ∈ H`, `suChart (ψ ∘ σ) u = Y_σ⁻¹ (suChart ψ u) Y_σ`.
- `involution_eq_inv`: `τ_S(u) = u⁻¹` for unitary `u`; and `suChart_comp_of_not_mem`: for
  `σ ∉ H`, `suChart (ψ ∘ σ) u = (Y_σ⁻¹ (suChart ψ u)⁻¹ Y_σ)ᵀ`.

## Provenance

Internal. The algebra `B` with the involution `τ` is the classical Galois-descent
description of the central simple algebra with unitary involution attached to an outer
form of `SL_m` (compare Knus, Merkurjev, Rost and Tignol, *The Book of Involutions*, §26.A).
The charts are the standard splitting `B ⊗_F M ≅ M_m(M)` together with the identification
`S ⊗_K F ≅ S × S` given by the two embeddings of `F`. The Lean proofs are self-contained
computations with the Library's Galois descent, reduced norm and tensor projection
results, and Mathlib's Orzech property; no statement of the module is taken from a source.
