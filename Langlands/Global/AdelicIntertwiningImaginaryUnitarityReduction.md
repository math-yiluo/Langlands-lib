# Reduction of holomorphy and unitarity of intertwining operators on the imaginary axis

Module `Langlands.Global.AdelicIntertwiningImaginaryUnitarityReduction`
states and proves a reduction of the Library's
`Langlands.Global.IntertwiningImaginaryUnitarityStatement` (Lapid 2011,
p.312; Mœglin–Waldspurger IV.1.11 (b), VI.2.1 (i); module
`Langlands.Global.AdelicIntertwiningImaginaryUnitarityStatement`) to three
statements. Worker 106 wrote it for Task 5682, whose target is that
statement. The module does not prove the unitarity statement outright: the
three statements remain premises.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series* (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`,
  IV.3.12, p.161 (chapter file `08.3_pp_149_164_The_case_of_relative_rank_1.pdf`):
  the proof of IV.1.11 (b) in two steps, (1) the isometry
  `⟨M(w, λ)φ, M(w, λ)φ⟩ = ⟨φ, φ⟩` for imaginary `λ` where `M(w, .)` is
  holomorphic, (2) if `M(w, .)` were not holomorphic at an imaginary `λ`, then
  `⟨M(w, λ_n)φ, M(w, λ_n)φ⟩ → ∞` for imaginary `λ_n → λ`, a contradiction.
  VI.2.3, p.264, for the discrete spectrum of `M`.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series* (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page =
  printed page + 9): p.312 ("for `λ ∈ i𝔞_P^*`, `M(w, λ)` is unitary, hence
  holomorphic"), and pp.328–329, holomorphy near the real subspace for
  functions with singularities along real hyperplanes.

The reduction implements step (2) (provenance: source, MW IV.3.12 and Lapid
pp.328–329; the formal details are derived and described below). Step (1) is
the premise `IntertwiningImaginaryIsometryStatement`.

## Declarations

In the namespace `Langlands.Global`:

- `IntertwiningImaginaryUnitarityReductionStatement : Prop` is the implication
  `IntertwiningImaginaryIsometryStatement → InducedInnerProductGramStatement →
  IntertwiningRootHyperplaneStatement.{0} → IntertwiningImaginaryUnitarityStatement`.
- `intertwiningImaginaryUnitarity_of_inputs (hU) (hG) (hRH) :
  IntertwiningImaginaryUnitarityStatement` is the proof, with the three
  premises as hypotheses.
- `intertwiningImaginaryUnitarityReduction :
  IntertwiningImaginaryUnitarityReductionStatement` restates it in the form of
  the proposition.

The premises:

- `IntertwiningImaginaryIsometryStatement` (module
  `Langlands.Global.AdelicIntertwiningImaginaryIsometryStatement`, Task 5682
  statement candidate `ea2169ff-d905-44aa-ac9f-5afd7b162047`): MW IV.3.12,
  step (1). In the data of the unitarity statement, every family `coeff'`,
  meromorphic with one domain `DM'` and agreeing with the given expansion on
  `DM ∩ DM'`, satisfies the Gram identity of the unitarity statement at every
  imaginary point of `DM'`.
- `InducedInnerProductGramStatement` (module
  `Langlands.Global.AdelicInducedInnerProductGramStatement`, Task 5682
  statement candidate `02b483e7-f6c3-4a0e-9709-3e8c26fcd2ed`): Lapid §2
  (p.311). The Gram sum `∑ i, ∑ i', x i * conj (x i') * (φ i, φ i')_P` of
  forms `φ i ∈ A^2_P` is a nonnegative real number, and it is `0` exactly when
  `∑ i, x i • φ i = 0`.
- `IntertwiningRootHyperplaneStatement` (Library, module
  `Langlands.Global.AdelicRootHyperplaneStatement`, at universe `0`, the first
  conjunct of `RootHyperplaneSingularitiesStatement`): Bernstein–Lapid,
  Theorem 2.3 (6). Near every point `λ₀`, a power of `∏ β, B(λ − λ₀, β)`
  (`β` roots of the split component in the unipotent radical) times the
  expansion is holomorphic.

The module does not use the adjunction formula, the functional equation, the
cocycle relation or the meromorphic continuation of intertwining operators,
which the source uses to prove the isometry premise; nor does it prove the
three premises.

## The complexified real chart

Section `Chart` (namespace `Langlands.Global.AdelicGroupPoints`):

- `realToComplexParameter P : X^*(P) ⊗ ℝ →ₗ[ℝ] X^*(P) ⊗ ℂ`, `t ⊗ χ ↦ t ⊗ χ`.
- `imaginaryParameter_eq_I_smul`: `imaginaryParameter F P μ = i • realToComplexParameter P μ`.
- `realChart e : ℂⁿ ≃ₗ[ℂ] X^*(P) ⊗ ℂ` for real coordinates
  `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` (the `e` of the unitarity statement): the coordinate
  isomorphism of the basis `t ↦ e (Pi.single t 1)` base-changed to `ℂ`
  (`Module.Basis.baseChange` and `AlgebraTensorModule.cancelBaseChange`, with
  `cancelBaseChange_one_tmul`). `realChart_apply`:
  `realChart e z = ∑ t, z t • realToComplexParameter P (e (Pi.single t 1))`.
- `realChart_ofReal`, `realChart_I_mul`: real points of `ℂⁿ` go to
  `realToComplexParameter P (e x)` and imaginary points `x · i` to
  `imaginaryParameter F P (e x)`. Hence `realChart_mem_range_imaginary` and
  `realChart_symm_imaginary_re`: the imaginary points of `ℂⁿ` correspond
  exactly to the range of `imaginaryParameter F P`.

Section `Roots`:

- `rootFunctional_realToComplexParameter`: `r.rootFunctional hA hT β` is the
  complexification of `r.realRootFunctional hA hT β`, so in the chart
  `realChart e` the root forms have real coefficients.
- `exists_realRootFunctional_ne_zero`: for `α ∈ r.unipotentRoots`,
  `r.realRootFunctional hA hT α` is not zero on `e (ℝⁿ)`. A parameter `λ` with
  `B(Re λ|_A, α) > 0` for all such `α` exists (`exists_regularParameter`), and
  `realRootFunctional α (Re λ)` is that pairing.

The private lemmas `characterRestrict_injective_of_levi`,
`characterRestrict_rightInverse`, `characterRestrict_bijective_of_levi`,
`parameterRealPart_surjective`, `realParameterRestriction_surjective` and
`exists_regularParameter` are copies of helper lemmas written by Worker 587
(Task 5502 draft) and reproduced by Worker 86 in the staged cocycle reduction
of Task 5503; they are private so that a later publication of the originals
causes no name clash.

## Proof of `intertwiningImaginaryUnitarity_of_inputs`

Take the data of the unitarity statement (see its Markdown) and the chart
`e₀ = realChart e`. The instances `LocallyOfFiniteType P.X.hom` and
`LocallyOfFiniteType P'.X.hom` are supplied as in the statement.

1. *For each `j`, a representation holomorphic near the imaginary axis.*
   Apply `exists_holomorphic_on_imaginary_of_isometry` (module
   `Langlands.Analysis.Meromorphic.ImaginaryHolomorphicExtension`) to
   `ψ j`, the coefficients `coeff j i ∘ e₀` with domain `e₀ ⁻¹' DM`, the
   matrix `Gm i i' = (ψ j i, ψ j i')_{P'}` and `K₀ = (v j, v j)_P`:
   - `hgram` is `InducedInnerProductGramStatement` for `P'`, `K`, `hK'`,
     `μM'`, `e'`, `β'` and the forms `ψ j i ∈ A^2_{P'}`;
   - `hiso`: for a family `c` meromorphic in the chart with domain `D'`, the
     family `c i ∘ e₀.symm` is meromorphic in linear coordinates with domain
     `e₀.symm ⁻¹' D'` (`isMeromorphicInCoordinatesOn_of_chart`) and agrees
     with `coeff j` on `DM ∩ e₀.symm ⁻¹' D'`; an imaginary point `s ∈ D'` is
     `e₀ s = imaginaryParameter F P μ` for some `μ`. The isometry statement,
     applied with `k = 1` to `v j`, `ψ j`, `coeff j`, gives
     `gramForm Gm (c s) = (v j, v j)_P`;
   - `hRH`: at an imaginary `s₀`, `IntertwiningRootHyperplaneStatement`
     applied to `v j` (automorphic by the first conjunct of
     `IsSquareIntegrableInducedForm`), the expansion of `M(w, λ)(v j)`, the
     chart `e₀` and `s₀` gives a finite set `S ⊆ r.unipotentRoots`, an
     exponent `mm` and `W`. The linear forms indexed by `S × Fin mm`,
     `s ↦ r.rootFunctional hA hT β (e₀ s)`, are real and nonzero on `ℝⁿ` by
     the two facts above, and their product at `s − s₀` is
     `(∏ β ∈ S, r.rootFunctional hA hT β (e₀ s − e₀ s₀))^mm`.
2. *A common domain.* Let `c j`, `D' j` be these representations. Put
   `DM' = e₀.symm ⁻¹' ⋂ j, D' j` and `coeff' j i = c j i ∘ e₀.symm`. Each
   `D' j` contains the imaginary points, so `DM'` contains the range of
   `imaginaryParameter F P`. The intersection is open and dense (Baire), so
   each `c j i` stays meromorphic on it, and `coeff' j i` is meromorphic in
   linear coordinates with domain `DM'`. Agreement with `coeff` on `DM ∩ DM'`
   follows from the agreement of each `c j`.
3. *Unitarity.* The isometry statement, applied to `coeff'` and `DM'`, gives
   the Gram identity at `imaginaryParameter F P μ` for all `μ`, `j`, `j'`.

## Scope

The reduction proves holomorphy near the imaginary axis (conclusions 1–3 of
the unitarity statement) and passes conclusion 4 from the isometry premise. It
does not assert any of the three premises.
