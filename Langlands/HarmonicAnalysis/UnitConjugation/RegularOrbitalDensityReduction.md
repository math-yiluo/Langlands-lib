# Harish-Chandra's Theorem 3.1 from Lemmas 3.2, 3.3, 3.12 and 3.16

The module `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalDensityReduction` states,
as `Langlands.HarmonicAnalysis.LieAlgebraRegularOrbitalDensityReductionStatement.{u', v'}`, the
implication

`LieAlgebraRegularOrbitalFourierStabilityStatement → LieAlgebraNilpotentInvariantSpanStatement →
  LieAlgebraNilpotentOrbitalHomogeneityStatement → LieAlgebraCentralNilpotentDensityStatement →
  LieAlgebraRegularOrbitalDensityStatement`

(all at the universes `{u', v'}` of the field and the algebra), and proves it:
`Langlands.HarmonicAnalysis.lieAlgebraRegularOrbitalDensityReduction`. The conclusion is
Harish-Chandra's Theorem 3.1 for the Lie algebra `A` of the unit group of a finite-dimensional
semisimple algebra over a nonarchimedean local field of characteristic zero (module
`Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalDensityStatement`). The four premises
are, in this order, Harish-Chandra's Lemma 3.16 (Fourier transforms), Lemma 3.3 (`J(N)` is
finite-dimensional and spanned by nilpotent orbital integrals), Lemma 3.2 (homogeneity of
nilpotent orbital integrals) and Lemma 3.12 with central translates under the induction
hypothesis; their statements and sources are in the modules
`RegularOrbitalFourierStabilityStatement`, `NilpotentInvariantSpanStatement`,
`NilpotentOrbitalHomogeneityStatement` and `CentralNilpotentDensityStatement` of the same
directory. The module does not prove the premises.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15), §3,
printed pp. 17–30: Theorem 3.1 is proved by induction on the dimension; Lemma 3.11 reduces to
semisimple groups; Lemma 3.15 shows `J = J₀ + J(N)` (`J₀` the invariant distributions vanishing
on `D₀`); the final argument (printed pp. 29–30) compares the homogeneity degrees of the
nilpotent orbital integrals and of their Fourier transforms. Kottwitz, *Harmonic analysis on
reductive p-adic groups and Lie algebras*, in *Harmonic Analysis, the Trace Formula, and
Shimura Varieties*, Clay Math. Proc. 4, 2005, source ID
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12),
proof of Theorem 27.5, printed pp. 516–517, presents the same final argument with the spaces
`C₂ ⊂ C₁` of test functions. The implementation follows these arguments, with the center kept
by working on the orthogonal `V = z^⊥` of the center for the trace form.

## Proof

Write `V = z^⊥` (`centerOrthogonal`), `D₀(V)` for `CenterOrthogonalVanishing F A`, `J^V` for
the invariant distributions on `V` and `J^V(N)` for the nilpotent invariant ones (modules
`CenterDecomposition`, `CenterOrthogonalDistributions`). In the namespace
`Langlands.HarmonicAnalysis.RegularOrbitalDensityReduction`:

1. **Lemma 3.12 on `V`** (`centerOrthogonalInvariant_apply_eq_zero`). Let `S ∈ J^V` and
   `β ∈ D₀(V)` be annihilated by `J^V(N)`. Apply the Lemma 3.12 premise, with the induction
   hypothesis, to `T = S ∘ restrict` and `f = extendTest α β ∈ D₀` (`α` the bump of
   `exists_centerBump`, `α(0) = 1`). For central `Z` and `S''` supported on `Z + N`,
   `exists_centerOrthogonalNilpotentInvariant_of_translate` writes
   `S'' g = S₂((g(· + Z))|_V)` with `S₂ ∈ J^V(N)`: `S'' ∘ translate(-Z)` is invariant
   (`translateTest_pullback_conjugation`) and supported on the closure of `N`, since the
   saturation of `Z + N` is the translate of `N`, and `apply_eq_comp_extendTest_restrict`
   applies. As `(extendTest α β)(· + Z)|_V = α(Z) β`, `S'' f = α(Z) S₂ β = 0`. So
   `S β = T f = 0`.

2. **Fourier transform of a generator** (in
   `centerOrthogonalNilpotentInvariant_apply_eq_zero_of_ne_top`, for `A` not commutative).
   Fix Borel σ-algebras, Haar measures on `z` and `V`, a character `ψ`
   (`nonempty_unitaryAdditiveCharacter`) and the Fourier transform `F_V` of `V`. By the
   Lemma 3.16 premise, `F_V` maps `D₀(V)` into itself (`CenterOrthogonalVanishing.fourier`); by
   Fourier inversion (`exists_pos_bicharacterFourier_bicharacterFourier`) and the dilation
   `β ↦ β(-·)` it maps `D₀(V)` onto itself. For `μ ∈ nilpotentOrbitals A`, put
   `R = μ ∘ extendTest α`, a nilpotent invariant distribution on `V`
   (`comp_extendTest_mem_centerOrthogonalNilpotentInvariant`), and `R̂ = R ∘ F_V`, invariant by
   `fourier_pullback_centerOrthogonalConj`.

3. **Lemma 3.15.** Let `W` be the span of the restrictions to `D₀(V)` of the generators
   `μ' ∘ extendTest α`; it is finite-dimensional, being contained in the image of the
   finite-dimensional `J^V(N)` (Lemma 3.3 premise). By step 1 and the spanning half of
   Lemma 3.3 (`centerOrthogonalNilpotentInvariant_le_span`), `R̂` vanishes on the common kernel
   of `W` in `D₀(V)`, so its restriction lies in `W` (Mathlib's
   `Subspace.dualCoannihilator_dualAnnihilator_eq`): on `D₀(V)`,
   `R̂ = Σᵢ cᵢ Rᵢ` with finitely many generators `Rᵢ`.

4. **Homogeneity.** By the Lemma 3.2 premise (`exists_homogeneity_degree`) `R` and the `Rᵢ`
   are homogeneous: `R(β_{t²}) = |t|^d R(β)`, `Rᵢ(β_{t²}) = |t|^{dᵢ} Rᵢ(β)`, with
   `d, dᵢ < dim V`. By `fourier_scalarDilation`,
   `R̂(β_{t²}) = |t|^{2 dim V} |t|^{-d} R̂(β)`. Take `t` with `|t| = x > 1`
   (`exists_one_lt_distribHaarChar`, `t` the inverse of a uniformizer) and evaluate the
   identity of step 3 at `β_{(t^m)²}` for `β ∈ D₀(V)` (stable under dilation): for all `m`,
   `x^{2m dim V} x^{-md} R̂(β) = Σᵢ cᵢ x^{m dᵢ} Rᵢ(β)`. Since `d + dᵢ < 2 dim V`, dividing gives
   `R̂(β)` as a combination of `m`-th powers of numbers in `(0, 1)`, and letting `m → ∞`
   gives `R̂(β) = 0` (`eq_zero_of_forall_scaling`). Hence `R(F_V γ) = 0` for all
   `γ ∈ D₀(V)`, and since `F_V` maps `D₀(V)` onto itself, `R` vanishes on `D₀(V)`; by
   linearity, so does every element of the span of the generators, which contains `J^V(N)`.

5. **The commutative case** (`centerOrthogonalVanishing_eq_zero_of_center_eq_top`). If `A` is
   commutative, `V = 0`. The Dirac distribution at `0` lies in `J(N)` and is nonzero, so by the
   Lemma 3.3 premise `nilpotentOrbitals A` is nonempty: there is a compatible quotient measure
   `ν` with convergent orbital integrals at a nilpotent, hence zero, element. The coset space of
   its centralizer `Aˣ` is a point, `ν` is nonzero and finite, and `0` is regular
   (`zero_mem_regularSet_of_center_eq_top`), so for `β ∈ D₀(V)` the orbital integral of
   `extendTest α β` at `0`, `ν(pt) β(0)`, vanishes and `β = 0`. Thus in both cases `J^V(N)`
   annihilates `D₀(V)` (`centerOrthogonalNilpotentInvariant_apply_eq_zero`).

6. **Theorem 3.1 for `A`** (`regularOrbitalDensityFor_of_inputs`), given Theorem 3.1 for all
   semisimple algebras of smaller dimension. For `T` invariant and `f ∈ D₀`, apply the
   Lemma 3.12 premise: for central `Z` and `S` supported on `Z + N`,
   `S f = S₂((f(· + Z))|_V)` with `S₂ ∈ J^V(N)` as in step 1, and `(f(· + Z))|_V ∈ D₀(V)`
   (`RegularOrbitalVanishing.translate_central`,
   `RegularOrbitalVanishing.centerOrthogonalVanishing_restrict`), so `S f = 0` by step 5. Hence
   `T f = 0`.

7. **Induction** (`regularOrbitalDensityFor_of_finrank_eq`): strong induction on
   `finrank F A`, over all semisimple algebras in the universe of `A`, gives Theorem 3.1 for
   every `A`, and `lieAlgebraRegularOrbitalDensityStatement_iff` turns this into
   `LieAlgebraRegularOrbitalDensityStatement` (`lieAlgebraRegularOrbitalDensityReduction`).

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
