# Discrete-series isotypic projectors from exponents below two

`Langlands.glTemperedDiscreteSeriesIsotypicReduction` proves the Library
proposition
`Langlands.GLTemperedDiscreteSeriesIsotypicReductionStatement.{uF,uV,uW}` of
[TemperedDiscreteSeriesIsotypicReductionStatement](TemperedDiscreteSeriesIsotypicReductionStatement.md).
That proposition is the implication

`GLProductLeviSquareIntegrableLpStatement.{uF,uW} →
GLTemperedDiscreteSeriesIsotypicStatement.{uF,uV,uW}`.

So this module proves the tempered discrete-series isotypic projector statement
assuming the lower-exponent statement
[ProductLeviSquareIntegrableLpStatement](ProductLeviSquareIntegrableLpStatement.md):
every coefficient of an irreducible square-integrable representation of a
product Levi lies in `L^r(Q, μ)` for some `1 < r < 2`. It does not prove that
lower-exponent statement, and it does not prove the unconditional isotypic
statement.

The proof is a generic theorem for a topological group `G`, followed by a short
specialization to product Levis.

## Generic setting

In the section `Generic`, `G` is a topological group, `ρ : Representation ℂ G V`
and `σ : Representation ℂ G W`, and `G ⧸ Subgroup.center G` carries a Borel
measurable structure. The integrals are the coefficient pairings of
[TemperedCoefficientPairing](TemperedCoefficientPairing.md).

### Integrability of every coefficient product

`pairingIntegrable_of_lt_two` assumes unitary central characters `cρ`, `cσ` with
`hχ : cρ.character = cσ.character`, a Haar measure `μ` invariant under
inversion, `IsTemperedModCenter ρ μ`, smooth `σ`, and

`hlt`: for every `ℓ : SmoothDual σ` and `w : W` there is `r` with `1 < r < 2`
and `MemLp (cσ.coefficientNorm ℓ w) (ENNReal.ofReal r) μ`.

It concludes `cρ.PairingIntegrable cσ hχ μ`. For given `ℓ`, `w`, `η`, `v`, take
`r` from `hlt`. Its conjugate exponent `r' = r/(r-1)` satisfies `r' > 2`
because `r < 2`. Temperedness of `ρ`, applied with `ε = r' - 2 > 0`, gives
`MemLp (c.coefficientNorm η v) (ENNReal.ofReal r') μ` for the witnessing
central-character datum `c`; `coefficientNorm_eq` rewrites this for `cρ`.
Then `integrable_pairingKernel` (Hölder) gives integrability.

This is the only place where `r < 2` is used. With only `L²` for `σ` and
`L^(2+ε)` for `ρ`, the exponents are not Hölder conjugate.

### Detecting nonzero intertwiners `σ → ρ`

`exists_intertwiningMap_rightFunctional_ne_zero` assumes compact open subgroups
cofinal (`hcof`), `μ` right invariant and positive on nonempty open sets, `ρ`
smooth, `σ` admissible and irreducible, `PairingIntegrable`, an invariant
positive form `b` on `σ`, a vector `u ≠ 0` whose coefficient
`cσ.coefficientNorm (b.rightFunctional u) u` is in `L²(μ)`, and a nonzero
`f : σ.IntertwiningMap ρ`. It produces `r : ρ.IntertwiningMap σ` with
`b.rightFunctional u (r (f u)) ≠ 0`.

Since `σ` is irreducible and `f ≠ 0`, `f` is injective. The Library theorem
`contragredientMap_surjective_of_injective_of_compact_cofinal` extends the
smooth functional `b(u, -)` along `f` to `ξ : SmoothDual ρ` with
`ξ ∘ f = b(u, -)`. The pairing with fixed `σ`-vector `u` and `ρ`-functional `ξ`
gives `S : ρ.IntertwiningMap σ` with
`b(u, S v) = coefficientPairing (b(u, -)) u ξ v`. Because `f` intertwines,
`ξ(ρ(g)(f u)) = b(u, σ(g)u)` for every `g`, so `coefficientPairing_ne_zero`
shows that `b(u, S (f u)) ≠ 0`. Take `r = S`.

### The generic projector theorem

`temperedDiscreteSeriesIsotypic_of_lt_two` assumes `hcof`, a Haar measure `μ`
that is right invariant and invariant under inversion, `cρ`, `cσ`,
`IsTemperedModCenter ρ μ`, irreducible `σ`, `IsSquareIntegrableModCenter σ μ`,
`hχ`, and `hlt`. Its conclusion is the body of the target statement: there is
`P : ρ.IntertwiningMap ρ` with `P.comp P = P`,
`P.range = ⨆ f : σ.IntertwiningMap ρ, f.range`, and no subrepresentation of
`P.ker` admits a surjective intertwiner onto `σ`.

The proof has four steps.

1. **Finiteness and integrability.** `pairingIntegrable_of_lt_two` gives
   `PairingIntegrable`. `Hom(σ, ρ)` is finite-dimensional by the Library's
   `finite_intertwiningMap_of_finiteType`, since `σ` is smooth and finitely
   generated (`moduleFinite_asModule_of_isIrreducible`) and `ρ` is admissible.
2. **A positive form and a test functional.** Square integrability of `σ`,
   transported to `cσ` by `coefficientNorm_eq`, puts every coefficient in `L²`.
   A nonzero smooth functional `ℓ₁` exists by
   `exists_nonzero_smoothDual_of_irreducible_compact_cofinal`, and the Library's
   `cσ.coefficientProductForm` integrates the coefficients of `ℓ₁` to an
   invariant positive form `b` on `σ`. Choose `u ≠ 0` in `W`, and put
   `m = b(u, -)`, so `m u ≠ 0` by definiteness.
3. **The projector.** The previous lemma is exactly the nondegeneracy hypothesis
   of `exists_isotypicProjector_of_nondegenerate`
   ([IsotypicProjector](../Smooth/IsotypicProjector.md)) for `m` and `u`. It
   gives `P` fixing every intertwiner `σ → ρ` with values in the isotypic
   subrepresentation, and `isotypicProjector_of_fixes` gives idempotence and the
   range equality.
4. **The kernel has no quotient isomorphic to `σ`.** Suppose `K` is a
   subrepresentation of `P.ker` and `q : K → σ` is a surjective intertwiner. Let
   `ι : K → ρ` be the composite inclusion, injective with `P ∘ ι = 0`; `K` is
   smooth by `isSmooth_of_injective`. Choose `k₀ ∈ K` with `q k₀ = u`.
   - Extend the smooth functional `k ↦ b(u, q k)` on `K` along `ι` to
     `ξ : SmoothDual ρ`. Then `ξ(ρ(g)(ι k₀)) = b(u, σ(g)u)` for all `g`.
   - The pairing with fixed `σ`-functional `b(u, -)` and `ρ`-vector `ι k₀`
     gives `R : σ.IntertwiningMap ρ` with
     `η(R w) = coefficientPairing (b(u, -)) w η (ι k₀)` for every smooth `η`.
   - For each smooth functional `η` on `ρ`, test with `η ∘ P`, the image of `η`
     under `contragredientMap P`. Its kernel is
     `b(u, σ(g⁻¹)w) · η(P(ρ(g)(ι k₀))) = b(u, σ(g⁻¹)w) · η(ρ(g)(P(ι k₀))) = 0`,
     so `η(P(R w)) = 0`. The smooth dual separates vectors of smooth `ρ`
     (`exists_smoothDual_apply_ne_zero_of_compact_cofinal`), hence `P ∘ R = 0`.
     Since `P` fixes every intertwiner `σ → ρ`, `R = P ∘ R = 0`.
   - But `ξ(R u) = coefficientPairing (b(u, -)) u ξ (ι k₀)`, which is nonzero
     by `coefficientPairing_ne_zero` and the identity for `ξ` above. This
     contradicts `R = 0`.

No Schur orthogonality relation or formal degree is used. The only analytic
facts are Hölder's inequality, invariance of `μ` under right translation and
inversion, and `∫ |b(u, σ(g)u)|² dġ > 0` for `u ≠ 0`.

## Product-Levi specialization

`glTemperedDiscreteSeriesIsotypicReduction` introduces the lower-exponent
hypothesis `hP1` and then the binders of the target statement in order: the
prime `p`, `F`, `T` with `T.topology`, `n > 0`, the block shape `B` with
`T.leviTopologicalGroup B`, the measurable structure on
`Q = M ⧸ Subgroup.center M`, the Haar measure `μ`, `V`, `W`, `ρ`, `σ`, `cρ`,
`cσ`, and the four hypotheses. It applies
`temperedDiscreteSeriesIsotypic_of_lt_two` with

- cofinality of compact open subgroups from
  `UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B`;
- right invariance and inversion invariance of `μ` from
  `T.leviCentralQuotientHaar_unimodular B μ`
  ([LeviCentralQuotientMeasure](../../Group/GL/LeviCentralQuotientMeasure.md));
- `hlt` from `hP1 p F T n hn B μ W σ hirr hσ cσ`.

## Provenance and scope

The target statement is extracted from Silberger 1979, Theorem 4.5.18 and the
proof of Theorem 3.3.1, as documented in
[TemperedDiscreteSeriesIsotypicStatement](TemperedDiscreteSeriesIsotypicStatement.md).
The lower-exponent input is the statement documented in
[ProductLeviSquareIntegrableLpStatement](ProductLeviSquareIntegrableLpStatement.md),
which records its source in Waldspurger 2003, Section III.1. The Lean route
above is an internal derived argument: it replaces Silberger's coefficient
convolution algebra by weak-integral intertwiners, a dual basis of
`Hom(σ, ρ)` and Schur's lemma, and it uses the lower exponent only through
Hölder's inequality.

The theorem is conditional: it is a proof of the reduction statement only.
The unconditional statement follows once
`GLProductLeviSquareIntegrableLpStatement` is proved.
