# The Hilbert spaces of the spectral transform

Module `Langlands.Global.AdelicSpectralTransformSpaces` defines the spaces
on which Langlands' unitary spectral transform (Arthur 2005, Theorem 7.2 (b);
Getz–Hahn (10.22)–(10.24)) is defined: the Hilbert space `H_P` of the
induced representation `Ind_{P(𝔸)}^{G(𝔸)}(L²_disc)`, a characterization of
the operators `M(w, λ) : H_P → H_{P'}` at imaginary `λ`, the Hilbert space of
square-integrable families `(F_P)_P` with the weighted norm, Arthur's
subspace `L̂` of families with `F_{P'}(wλ) = M(w, λ)F_P(λ)`, and the smooth
compactly supported families. It is a definition module; besides the
`Submodule` structure of `L̂` it proves only the helper lemmas listed below.
The statement about these spaces is `SpectralTransformStatement` (module
`Langlands.Global.AdelicSpectralTransformStatement`).

## Sources

- J. Arthur, *An introduction to the trace formula*, in: Harmonic Analysis,
  the Trace Formula, and Shimura Varieties, Clay Math. Proc. 4 (2005),
  registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`
  (PDF page = printed page + 12 in Arthur's article), §7:
  - p.32 (PDF page 44): the compatible Haar measures
    `dx = dn dm da dk` (with `vol(K) = vol(N_P(F) \ N_P(𝔸)) = 1`), the
    measure `dλ` on `i𝔞_P^*` dual to the measure `dH` on `𝔞_P`, and the
    Hilbert space `H_P` of functions
    `φ : N_P(𝔸) M_P(F) A_P(ℝ)⁰ \ G(𝔸) → ℂ` with `φ_x ∈ L²_disc` and
    `‖φ‖² = ∫_K ∫_{M_P(F) \ M_P(𝔸)¹} |φ(mk)|² dm dk`;
  - p.34 (PDF page 46): the intertwining operators `M(s, λ) : H_P → H_{P'}`,
    `s ∈ W(𝔞_P, 𝔞_{P'})`, (7.2), and the dense subspace `H_P^0` of `K`-finite
    vectors lying in a finite sum of irreducible subspaces;
  - Theorem 7.2, p.35 (PDF page 47): (a) for `λ ∈ i𝔞_P^*`, `M(s, λ)` is
    analytic and extends to a unitary operator from `H_P` to `H_{P'}`;
    (b) the Hilbert space `L̂_𝒫` of families of measurable functions
    `F_P : i𝔞_P^* → H_P`, `P ∈ 𝒫`, with `F_{P'}(sλ) = M(s, λ)F_P(λ)` and
    `‖F‖² = ∑_P n_P⁻¹ ∫_{i𝔞_P^*} ‖F_P(λ)‖² dλ < ∞`, and the smooth compactly
    supported `F_P` with values in a finite-dimensional subspace of `H_P^0`.
- J. Getz and H. Hahn, *An introduction to automorphic representations*
  (2024), registered as `getz-hahn-2024-automorphic-representations`, §10.5,
  p.281 (PDF page 293), (10.22)–(10.23): the same families with values in
  `Ind_P^G(L²_disc([M]))`, the Weyl invariance condition and the inner
  product with weights `n_P`.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, §2, pp.311–312
  (PDF pages 320–321): `A^2_P`, the inner product `(·,·)_P`, and the
  extension of `M(w, λ)`, `λ ∈ i𝔞_P^*`, to a unitary operator on
  `Ind_{P(𝔸)}^{G(𝔸)} L²_disc(A_M M(F) \ M(𝔸))`.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series* (1995), registered as
  `moeglin-waldspurger-1995-spectral-decomposition`, IV.1.11 (b) (p.141,
  cuspidal data) and VI.2.1 (i) (p.260, forms in the discrete spectrum of
  `M`): `M(w, λ)` continues meromorphically and is holomorphic on the
  imaginary axis, where it is unitary.

## Existing objects used

- `IsSquareIntegrableInducedForm` (Lapid's `A^2_P`), `inducedInnerProduct`
  (`(·,·)_P`), `IsIwasawaCompatibleMeasure`, `compactHaarProbability`,
  `parameterCoordinates`, `spectralMeasure n` (the measure `(2π)^{-n} dx`),
  `realWeylParameter`, `imaginaryParameter`, `ParabolicRootPresentation`,
  `IsRegularParameter` and `IsIwasawaCompact.intertwiningOperator` (the
  convergent integral `M(w, λ)` for `Re λ` sufficiently regular), as in the
  published `WavePacketInnerProductStatement` and
  `IntertwiningMeromorphicContinuationStatement`;
- `IsMeromorphicInCoordinatesOn` (module
  `Langlands.Analysis.Meromorphic.LinearCoordinates`);
- Mathlib's `Lp`, `PiLp`, `Measure.withDensity` and `Submodule`.

## Definitions

### `inducedL2Measure K hKc l μM e β`

The measure `β(y(m)) δ_P(m)⁻¹ dk dm` on `K × M(F) \ M(𝔸)`: the product of
the Haar probability measure on `K` and the quotient of `μM` by counting
measure on `M(F)`, with density `β(y(m)) δ_P(m)⁻¹`, where `y(m)` are the
coordinates of `H_P(m)` dual to `e` and `δ_P(m) = |m^{2ρ_P}|`, both read at
the chosen representative `m` of the coset. The density is
`ENNReal.ofReal` of a real number, so negative values of `β` are read as
`0`; all uses take `β ≥ 0`. For `β ≥ 0` and `φ, ψ ∈ A^2_P` with
restrictions `f_φ`, `f_ψ` (next definition), the `L²` inner product
`⟪f_ψ, f_φ⟫` for this measure (Mathlib's inner product is conjugate-linear
in the first variable) has the integrand of
`inducedInnerProduct K hKc p l μM e β φ ψ`, written as an iterated
integral there, so by Fubini it is `(φ, ψ)_P`, since `δ_P(m)⁻¹ =
‖m^{-2ρ_P}‖` is the positive real number `m^{-2ρ_P}`. This is explanatory
and not proved here.

### `inducedRestriction K p l φ`

The function `(k, m) ↦ φ(mk)` on `K × M(F) \ M(𝔸)`, read at the chosen
representative `m` of the coset (`Quotient.out`), as in
`inducedInnerProduct`. For `φ ∈ A^2_P`, which is left invariant under
`U(𝔸)M(F)`, the value does not depend on the representative, and
`δ_P` and `H_P` are trivial on `M(F)` by the product formula; so the
function is the descent of the continuous function `(k, m) ↦ φ(mk)` and is
measurable.

### `inducedHilbertSpace K hKc rho hsmooth hcalc p iU l μM e β`

The closure, in `L²(K × M(F) \ M(𝔸), β δ_P⁻¹ dk dm)`, of the span of the
classes of the restrictions `inducedRestriction K p l φ` of all
`φ ∈ A^2_P`. A function `φ` contributes only if its restriction is square
integrable, which holds for every `φ ∈ A^2_P` when `β ≥ 0` is integrable
(see below).

Relation to Arthur's `H_P` (explanatory, not proved here). Lapid's `A^2_P`
uses functions with `φ(ag) = δ_P(a)^{1/2} φ(g)` for `a ∈ A_M`; Arthur's
`H_P` uses `A_P(ℝ)⁰`-invariant functions and puts `e^{ρ_P(H_P(·))}` into the
Eisenstein series. The two are related by `φ = e^{ρ_P(H_P(·))} φ_A`, and
then `δ_P(m)⁻¹ |φ(mk)|² = |φ_A(mk)|²` is invariant under `A_M`. Integrating
it against `β(y(m))` over the `A_M`-direction of `M(F) \ M(𝔸)` gives
`∫ β = 1` times the integral over `A_M M(F) \ M(𝔸) = M(F) \ M(𝔸)¹`, which is
Arthur's norm for the compatible measures (`IsIwasawaCompatibleMeasure` and
Lebesgue measure `dH` in the coordinates dual to `e`); in particular the
norm of a restriction does not depend on `β` (the ambient `L²` space does).
Under this twist, the restrictions of `A^2_P` are those of Arthur's dense
subspace `H_P^0` of smooth, `K`-finite, `𝔷`-finite vectors with
`φ_x ∈ L²_disc`. Restriction to `M(𝔸)K` loses nothing, since
`G(𝔸) = U(𝔸)M(𝔸)K` and the functions are left `U(𝔸)`-invariant; and an
`A_M`-equivariant function is determined by its values where `β(y(m)) > 0`,
a nonempty open set. So `inducedHilbertSpace` is a concrete model of
Arthur's `H_P` (Getz–Hahn's `Ind_P^G(L²_disc)`): the completion of `H_P^0`
in Iwasawa coordinates for the chosen `K`.

### `IsImaginaryIntertwiningOperator hK hK' rho hsmooth hcalc iU l a r hA hT iU' l' π' w cw μM μM' e e' β β' Mop`

For a pair `(w, cw)` (in the statement module, an element of `Ω(P, P')`,
`IsWeylConjugation`), `Mop : ℝⁿ → (H_P →L[ℂ] H_{P'})` is the family of
operators `M(w, λ)` at `λ = i e(x)`: for every `v ∈ A^2_P`, every expansion
`M(w, λ)v = ∑ q, coeff q λ • ψ q` for `Re λ` sufficiently regular, with
`ψ q ∈ A^2_{P'}` and coefficients meromorphic with a domain of holomorphy
`DM ⊇ i(X^*(P) ⊗ ℝ)`, every `h ∈ H_P` that is the class of the restriction
of `v`, and every `x`, the vector `Mop x h` is the class of the restriction
of `∑ q, coeff q (i e(x)) • ψ q`.

Why a characterization. The Library has `M(w, λ)` only as the convergent
integral `IsIwasawaCompact.intertwiningOperator` for `Re λ` sufficiently
regular, not its continuation to `i𝔞_P^*`. Following the published
`IntertwiningImaginaryUnitarityStatement` and `WavePacketIsometryStatement`,
the continuation enters through finite expansions with meromorphic
coefficients: by Lapid's Working hypothesis (p.312) and
Mœglin–Waldspurger VI.2.1 (i), `M(w, λ)v` is meromorphic with values in a
finite-dimensional subspace of `A^2_{P'}`, holomorphic on `i𝔞_P^*`
(Arthur Theorem 7.2 (a)).

Consistency (explanatory, not proved here). The value prescribed at `x`
does not depend on the expansion. Two expansions agree for `Re λ`
sufficiently regular, an open set meeting the open dense set `DM ∩ DM'`.
`IsMeromorphicOn` gives local representations `h / g` on connected
neighbourhoods with `g` not identically zero, so the difference of the two
sums vanishes on a set that is open, closed and nonempty in the connected
space `X^*(P) ⊗ ℂ`, hence on `DM ∩ DM'`, which contains `i(X^*(P) ⊗ ℝ)`. The
prescription also does not depend on `v` given `h`: by the discussion of
`inducedHilbertSpace`, two forms in `A^2_P` with almost everywhere equal
restrictions are equal.

Existence and uniqueness (explanatory, not proved here). Every `v ∈ A^2_P`
has such an expansion, and the classes of the restrictions span a dense
subspace of `H_P` by definition, so a continuous `Mop x` is unique. It
exists because `M(w, iμ)` preserves `(·,·)_P` on `A^2_P`
(`IntertwiningImaginaryUnitarityStatement`) and so extends from the span of
the restrictions to its closure; this is Arthur's Theorem 7.2 (a). The
existence for the operators of `Ω(P, P')` is the first part of
`SpectralTransformStatement`.

### `ae_spectralMeasure_eq`, `ae_smul_spectralMeasure_eq` (lemmas)

`spectralMeasure n`, and every nonzero multiple of it, has the null sets of
Lebesgue measure on `ℝⁿ`.

### `ae_intertwined_zero`, `ae_intertwined_add`, `ae_intertwined_smul` (lemmas)

For `L^q` classes `f` (on `α`) and `f'` (on `β`), a map `τ : α → β` that
pulls null sets back to null sets, and continuous linear maps `A x`, the
relation `f'(τ x) = A x (f x)` for almost every `x` holds for `f = f' = 0`
and is preserved by sums and scalar multiples. They are generic helpers for
the `Submodule` structure of `symmetricFamilySpace`.

### `spectralFamilySpace hK rho hsmooth hcalc iU l μM n e β nP`

For a finite family `(P i)_{i ∈ I}`, the Hilbert space of families
`(F_i)_i` of square-integrable `F_i : ℝ^{n i} → H_{P i}`, where `x` stands
for `λ = i e_i(x) ∈ i𝔞_{P i}^*`, with
`‖F‖² = ∑ i, (nP i)⁻¹ ∫ ‖F_i(x)‖² d(spectralMeasure (n i))(x)`: the `ℓ²`
product (`PiLp 2`) of the spaces `L²(ℝ^{n i}, (nP i)⁻¹ • spectralMeasure (n i); H_{P i})`.
The measure `spectralMeasure (n i) = (2π)^{-n i} dx` is the measure on
`i𝔞_{P i}^*` dual to Lebesgue measure in the coordinates of `𝔞_{P i}` dual
to `e i`, as Arthur's `dλ` is dual to `dH`. If `nP i = 0` the weight is
`⊤` and the `i`-th factor is `0`; in the statement module `nP i ≥ 1`.

### `IsSmoothCompactFamily … k v c Φ`

`Φ` is a smooth compactly supported family with values in a
finite-dimensional space of `K`-finite vectors: there are `v i j ∈ A^2_{P i}`
(`j < k i`) and smooth compactly supported `c i j : ℝ^{n i} → ℂ` with
`Φ_i(x)` the class of the restriction of `∑ j, c i j x • v i j` for almost
every `x`. These are Arthur's `F_P`, smooth and compactly supported with
values in a finite-dimensional subspace of `H_P^0`: such an `F_P` is
`∑ j, c_j(λ) v_j` for a basis `v_j` of that subspace, with smooth compactly
supported coordinates `c_j`.

### `symmetricFamilySpace … T cw π hw Mop`

Arthur's `L̂` as a `Submodule` of `spectralFamilySpace`: the families `Φ`
with `Φ_{i'}(τ x) = Mop i i' t x (Φ_i x)` for almost every `x` and every
`i, i'` and `t : T i i'`, where `τ x = (e i')⁻¹ (realWeylParameter (l i) (cw i i' t) (π i') (e i x))`
is `λ ↦ wλ` in the coordinates, and `Mop i i' t x` stands for
`M(w, i e_i(x))`. This is Arthur's symmetry condition
`F_{P'}(sλ) = M(s, λ)F_P(λ)`, `s ∈ W(𝔞_P, 𝔞_{P'})`, almost everywhere (the
`F_P` are classes of measurable functions). The hypothesis `hw` that each
`τ` preserves Lebesgue measure makes the condition well defined on classes
and is used in the `Submodule` proofs. In Arthur's setting the measures on
the spaces `𝔞_P` come from one Weyl-invariant measure on `𝔞_0`, so it holds
automatically; here the coordinates `e i` are arbitrary, and `hw` is the
same hypothesis as in `WavePacketIsometryStatement`. `L̂` is closed in
`spectralFamilySpace` when the `Mop i i' t x` are continuous (a subsequence
of a convergent sequence converges almost everywhere); this is not stated.

## Conventions

- `F : Type`, as for `A^2_P`, which uses the canonical split component.
- Parameters are `i𝔞_P^* = i(X^*(P) ⊗ ℝ)`, as in Arthur and Lapid on
  `G(F) \ G(𝔸)`; Getz–Hahn work on `[G] = A_G G(F) \ G(𝔸)` with
  `i(𝔞_M^G)^*`.
