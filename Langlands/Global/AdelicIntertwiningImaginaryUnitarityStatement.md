# Unitarity of intertwining operators on the imaginary axis

Module `Langlands.Global.AdelicIntertwiningImaginaryUnitarityStatement`
states `Langlands.Global.IntertwiningImaginaryUnitarityStatement` as a
proposition definition. It supplies no proof.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
  page = printed page + 9). §2, p.312, after the Working hypothesis: "The
  functional equations of the intertwining operators immediately imply that
  for `λ ∈ i𝔞_P^*`, `M(w, λ)` is unitary, hence holomorphic, and therefore
  extends to a unitary operator on `Ind_{P(𝔸)}^{G(𝔸)} L²_disc(A_M M \ M(𝔸))`.
  (Cf. [MW95, IV.3.12].)" Here `w ∈ Ω(P, Q)` and `M(w, λ) : A_P → A_Q`.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series*, Cambridge Tracts in Math. 113 (1995), registered as
  `moeglin-waldspurger-1995-spectral-decomposition`:
  - II.1.8 (pp.93–94), the adjunction formula
    `(M(w, λ)φ, φ') = (φ, M(w⁻¹, -w λ̄)φ')`;
  - IV.1.11 (b) (p.141), for cuspidal data: if `Re π = 0`, then `E` and
    `M(w, ·)` are holomorphic at `π`; its proof, IV.3.12 (p.161), combines the
    adjunction formula with the functional equation to get
    `(M(w, λ)φ, M(w, λ)φ) = (φ, φ)` for imaginary `λ` where `M(w, ·)` is
    holomorphic, and deduces holomorphy from this bound;
  - VI.2.1 (i) (p.260) and its proof VI.2.3 (p.264), for forms in the
    discrete spectrum of `M`: the intertwining operators continue
    meromorphically and "are holomorphic on the unitary axis since these
    operators are unitary there, and defined on an open dense set".

## Statement

The data, for a number field `F : Type`:

- `G` connected reductive; `P = MU` with presentation
  `r : ParabolicRootPresentation p l a` (which makes `P` a parabolic with
  rational Levi `l`; it also gives the region "`Re λ` sufficiently
  regular"), and a parabolic `P' = M'U'` (`IsParabolicSubgroup p'`) with
  rational Levi subgroup `l'` (`IsRationalLeviSubgroup l'`), Levi
  decomposition `M' ⋉ U' ≅ P'` (`IsIso (subgroupMultiplication l' iU')`) and
  Levi projection `π' : P' → M'`, `l' ≫ π' = 𝟙`; these are the target-side
  hypotheses of the published `IntertwiningMeromorphicContinuationStatement`.
  `p`, `p'`, `iU ≫ p` and `iU' ≫ p'` are closed immersions, `iU`, `iU'`
  geometric unipotent radicals, all groups affine, `M` and `M'` locally of
  finite type (`P` and `P'` are locally of finite type as closed subgroups,
  supplied by `haveI`);
- `(w, cw)` with `IsWeylConjugation p l p' l' w cw`, that is, a rational
  point `w` of `G` and an isomorphism `cw : M' → M` presenting an element of
  `W(P, P')`;
- `K` maximal compact with `P(𝔸)K = P'(𝔸)K = G(𝔸)`, a closed matrix
  embedding `rho`, and the smooth-structure data `hsmooth`, `hcalc`;
- Haar measures `μM` on `M(𝔸)` and `μM'` on `M'(𝔸)`, both compatible with
  Mathlib's Haar measure on `G(𝔸)` and with `K`
  (`IsIwasawaCompatibleMeasure`, module
  `Langlands.Global.AdelicInducedInnerProduct`);
- a linear isomorphism `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and
  `e' : ℝⁿ ≃ X^*(P') ⊗ ℝ` with `e' x = w (e x)` for all `x`, where
  `μ ↦ wμ` is `realWeylParameter l cw π'`;
- continuous compactly supported weights `β, β' : ℝⁿ → ℝ` with
  `∫ β = ∫ β' = 1`; they define the inner products
  `(·,·)_P = inducedInnerProduct K hK.isCompact p l μM e β` and
  `(·,·)_{P'} = inducedInnerProduct K hK'.isCompact p' l' μM' e' β'`;
- `v : Fin k → (G(𝔸) → ℂ)` with every `v j` in `A^2_P`, functions
  `ψ j i` (`i < m`) in `A^2_{P'}` (`IsSquareIntegrableInducedForm`), and
  coefficients `coeff j i`, meromorphic with one domain of holomorphy `DM`,
  such that for every `j`, for `Re λ` sufficiently regular and every `g`,
  `M(w, λ)(v j)(g) = ∑ i, coeff j i λ · ψ j i g`, where `M(w, λ)` is
  `hK.intertwiningOperator hK' iU l iU' cw π' w`.

The conclusion: there are coefficients `coeff' j i` and a set `DM'` with

1. `i(X^*(P) ⊗ ℝ) ⊆ DM'` (the range of `imaginaryParameter F P`);
2. every `coeff' j i` meromorphic with domain of holomorphy `DM'`;
3. `∑ i, coeff' j i λ · ψ j i g = ∑ i, coeff j i λ · ψ j i g` for all `j`,
   `λ ∈ DM ∩ DM'` and `g`;
4. for every `μ ∈ X^*(P) ⊗ ℝ`, `λ = iμ`, and all `j`, `j'`:
   `∑ i, ∑ i', coeff' j i λ · conj (coeff' j' i' λ) · (ψ j i, ψ j' i')_{P'} = (v j, v j')_P`.

## Correspondence with the source

- Finite-dimensional form. Lapid's Working hypothesis (p.312) and
  Bernstein–Lapid (`IntertwiningMeromorphicContinuationStatement`) say that
  `M(w, λ)φ` is meromorphic with values in a finite-dimensional subspace of
  `A^2_{P'}` determined by the `K`- and `𝔷`-types of `φ`. Such a function is
  `∑ i, coeff j i λ · ψ j i` for a spanning family `ψ j i` and meromorphic
  coefficients, which is how `M(w, λ)(v j)` enters. Conclusions 1–3 say that
  `λ ↦ M(w, λ)(v j)` is holomorphic near `i𝔞_P^*`: `∑ i, coeff' j i λ · ψ j i`
  is holomorphic on `DM'` and agrees with the given continuation on
  `DM ∩ DM'`, which is open and dense. Its value at imaginary `λ` is therefore
  the value of the continuation of `M(w, λ)(v j)` there. The statement does
  not ask `coeff'` to equal `coeff`: when the `ψ j i` are linearly dependent
  the coefficients are not determined by the function, and a representation
  with poles near `i𝔞_P^*` can represent a function holomorphic there.
- Unitarity. Since `(·,·)_{P'}` is linear in the first and conjugate-linear
  in the second variable, conclusion 4 is
  `(M(w, λ)(v j), M(w, λ)(v j'))_{P'} = (v j, v j')_P` for `λ ∈ i𝔞_P^*`.
  Every finite family in `A^2_P` can be taken as `v`, so this says that
  `M(w, λ)` preserves inner products on `A^2_P`, that is, extends to an
  isometry `Ind L²_disc(A_M M \ M(𝔸)) → Ind L²_disc(A_{M'} M' \ M'(𝔸))`.
  Surjectivity of the extension, the remaining part of "unitary", follows
  from the functional equation `M(w⁻¹, wλ) ∘ M(w, λ) = M(1, λ) = 1`
  (`IntertwiningCocycleStatement`) and is not stated here.
- Holomorphy is not formal. Lapid's example on p.329,
  `f(z) = e^{-(z₁² + ⋯ + zₙ²)} / (z₁² + ⋯ + zₙ²)` with `n ≥ 5`, is
  meromorphic on `ℂⁿ` and square integrable on `ℝⁿ` (it grows like `r⁻²` at
  `0`), but not holomorphic at `0`: square integrability on a real form does
  not force holomorphy for general meromorphic functions. Boundedness does not
  force it either; for instance (an example added here, not Lapid's)
  `z₁ / (z₁ + i z₂)` on `ℂ²` has absolute value at most `1` on `iℝ²` and is
  not continuous at `0` there. Lapid (pp.328–329) notes that square
  integrability on `ℝⁿ` does force holomorphy near `ℝⁿ` when the
  singularities lie along hyperplanes `⟨λ, v - v₀⟩ = 0` with `λ ∈ ℝⁿ`.
  Mœglin–Waldspurger's argument uses that the singularities of `M(w, ·)` lie
  along root hyperplanes (IV.1.11 (a)): at a pole on `i𝔞_P^*`, `M(w, λ)φ` is
  unbounded for `λ ∈ i𝔞_P^*` near it, against the norm identity from
  unitarity. This is explanatory and not proved here.
- Measures. Lapid fixes Haar measures on `G(𝔸)`, `M(𝔸)`, `U(𝔸)`, `K` and
  `𝔞_P` compatibly with the Iwasawa decomposition. Here `dg` is Mathlib's
  Haar measure on `G(𝔸)`, `dk` the probability measure on `K`, `du` the Haar
  measure on `U(𝔸)` with `vol(U(F) \ U(𝔸)) = 1` (also used for the
  intertwining integral), `μM` and `μM'` are the compatible measures, and
  `𝔞_P`, `𝔞_{P'}` carry Lebesgue measure in the coordinates dual to `e` and
  `e'`. For `φ, ψ ∈ A^n_P` and `∫ β = 1`, `inducedInnerProduct` is Lapid's
  `(φ, ψ)_P` for these measures (Markdown of `AdelicInducedInnerProduct`).
  Since `H_{P'}(w a w⁻¹) = w H_P(a)` for `a ∈ A_M`, the hypothesis
  `e' = w ∘ e` makes the measures on `𝔞_P` and `𝔞_{P'}` correspond under `w`.
  The identity is not invariant under rescaling `e'` alone: replacing `e'`
  by `e' ∘ T` replaces the dual coordinates `y` of `H_{P'}(m)` by `Tᵀ y`, so
  the weighted integral defining `(·,·)_{P'}` is multiplied by `|det T|⁻¹`
  (for `n = 1`, `T = 2`: `∫ β(2y) dy = 1/2`). Hence some such compatibility
  is necessary. This is explanatory.
- The compact subgroup. Lapid fixes `K` in good position. Here `K` is any
  maximal compact subgroup with `P(𝔸)K = P'(𝔸)K = G(𝔸)`, the same for both
  inner products and for `M(w, λ)`; this reduces to his case as in the
  Markdown of `EisensteinAbsoluteConvergenceStatement`. For
  Iwasawa-compatible `μM`, the inner product `(·,·)_P` is the integral over
  `A_M U(𝔸) M(F) \ G(𝔸)` for the quotient of `dg`, so it does not depend on
  `K`, although `μM` does. The height functions `H_P` for two choices of `K`
  differ by a bounded left `P(𝔸)`-invariant function, so for `λ ∈ i𝔞_P^*`
  the two operators `M(w, λ)` differ by multiplication, before and after, by
  left `P(𝔸)`-invariant, resp. `P'(𝔸)`-invariant, functions of absolute
  value `1`, which preserve the inner products. This is explanatory and not
  proved here.
- Parabolics and regions. "`Re λ` sufficiently regular" is
  `r.IsRegularParameter hA hT R λ` for some `R`, as in the published
  Bernstein–Lapid statements. Lapid's `P` and `Q` are standard; here they
  need not be, as in the Markdown of `WavePacketInnerProductStatement`.
- Universe. `A^2_P` uses the canonical split component `A_M`, defined for
  `F : Type`.

## Scope

The statement asserts holomorphy near `i𝔞_P^*` and preservation of inner
products on `A^2_P`; it does not assert surjectivity of the extension to
`Ind L²_disc`, the adjunction formula, or holomorphy of Eisenstein series
(Lapid's Proposition 6 is `EisensteinImaginaryAxisHolomorphyStatement`).
