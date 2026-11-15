# Proof of Stacks Lemma 16.11.2 (07FH) from its ingredients

`SmoothApprox.artinianSmoothApproximation_of` proves
`Langlands.CommutativeAlgebra.Popescu.ArtinianSmoothApproximationStatement.{u}`. It takes six
statements as hypotheses:

- `GeometricRegularityH1FiniteStatement` (`ha`);
- `GeometricRegularityFlatStatement` (`hb`, Stacks 07E6);
- `RegularParameterExtensionStatement` (`hb2`);
- `ArtinianFlatSubalgebraStatement` (`hc`, Stacks 07FG);
- `ArtinianUnitEnlargementStatement` (`he`);
- `ArtinianEtaleCriterionStatement` (`hf`).

It uses only the standard axioms. Auxiliary lemmas are in `SmoothApproxTools`.

## The gap in the source and its repair

Stacks' proof picks `A ⊂ Λ̄ = Λ_q/qⁿΛ_q` by Lemma 16.11.1. It then picks "`λ_1, …, λ_t ∈ Λ` which
map to elements of `A` in `Λ̄`" with `dλ_j` a basis of `Ω_{F/k}`, `F = κ_A`. Since `Λ → Λ̄` need not
be surjective, such `λ_j` need not exist for this `A`. For example, `Λ = k[x]`, `q = 0`, `n = 1`
and `A = k(x² + 1/x)` contains no element of `k[x]` outside `k`.

The proof repairs this as follows.

1. A finite family `ν` generating `q` is put into `E` before applying Lemma 16.11.1. The later
   regular system of parameters is then chosen among the `ν`, which lie in `Λ` and map into `A`.
2. Elements `a_j = b_j ∈ A` with `d(ā_j)` a basis of `Ω_{F/k}` are written `λ_j/s` with one common
   `s ∉ q`. One application of `ArtinianUnitEnlargementStatement` to the unit `s̄` gives
   `ι : A → D'` and `ψ' : D' → Λ̄` together with:
   - `u ∈ D'` with `ψ'(u) = s̄^Q` and `dū = 0`;
   - `v_j` with `ψ'(v_j) = s̄`, such that the residue differentials of `ι(b_j)` and `v_j` form a
     basis of `Ω_{κ_{D'}/k}`.

   The elements `μ_j = λ_j s^{Q-1} ∈ Λ` then map to `ι(b_j)u ∈ D'`. Their residue differentials
   are `ū · d(ι(b_j))`, so the `μ_j` together with `s` (once for each `v_j`) give a basis.

## Structure of the proof

`artinianSmoothApproximation_of` does the following.

- Gets `Λ_q/qⁿΛ_q` local and Artinian, and the isomorphism `κ(Λ̄) ≅ κ(q)`
  (`exists_residueField_equiv`). This turns the hypothesis `ha` into the finiteness hypothesis of
  `hc` (`h1_finite_of_algEquiv`).
- Chooses `ν : Fin d → Λ` generating `q` (Noetherian), and gets `A` from `hc` with
  `E ∪ {ν̄_j} ⊆ A`.
- Chooses the differential basis `b` of `κ_A` (`exists_kaehler_basis`). It lifts `b_i` to `Λ_q`,
  and a common denominator `s` gives `λ_i ∈ Λ` with `λ̄_i = s̄ · b_i`.
- Applies `he` to `ψ = A.val`, `ℓ = s̄`. It sets
  `G' = (λ_i s^{Q-1})_i ⊔ (s)_j` in `Λ` and `gD = (ι(b_i)u)_i ⊔ (v_j)_j` in `D'`, indexed by
  `Fin (t + r)` via `finSumFinEquiv`. Then `ψ'(gD) = Ḡ'`, and the residue differentials of `gD`
  form a basis (`basis_smul`, Leibniz rule and `dū = 0`).
- Calls `final_step` with this data.

`final_step` does the following.

1. **07E6.** It takes `F = θ(κ_{D'}) ⊂ κ(q)`, where `θ : κ_{D'} → κ(Λ̄) ≅ κ(q)` is induced by
   `ψ'`. `F` is finitely generated (`IntermediateField.essFiniteType_iff`). The residue differentials
   of `G'` form a basis of `Ω_{F/k}` (`kaehler_basis_of_algEquiv` along `θ.equivFieldRange`). So
   `hb` applies to any `φ₁` with `φ₁(X_i) = G'_i`: `k[y]_{𝔭₀} → Λ_q` is flat and `Λ_q/𝔭₀Λ_q` is
   regular.
2. **Regular parameters.** The images of `ν` generate the maximal ideal of `Λ_q/𝔭₀Λ_q`.
   `exists_select_maximalIdeal` selects `σ : Fin d₁ → Fin d` with `d₁` the minimal number of
   generators. Then `φ = aeval (Fin.append G' (ν ∘ σ))`.
3. **Property (1).** `hb2` gives that `k[y]_𝔭 → Λ_q` is flat and `𝔭Λ_q = qΛ_q` for `𝔭 = φ⁻¹(q)`.
   It is applied to `φ ∘ rename (Fin.castAdd d₁)`, which equals `aeval G'`. Its hypotheses are
   transported along the equality of ideals with `span_mk_transport` and `spanFinrank_transport`.
4. **The map `P = k[y]_𝔭/𝔪ⁿ → D'`.**
   - `χ₀ = aeval (Fin.append gD (aν ∘ σ))`, where `aν_j = ι(ν̄_j)`. It satisfies
     `ψ' ∘ χ₀ = (Λ → Λ̄) ∘ φ`.
   - `χ₀` extends to `k[y]_𝔭` (`IsLocalization.lift`): elements outside `𝔭` map to units, since
     `ψ'` is local.
   - It kills `𝔪ⁿ` because `ψ'` is injective (`injective_of_flat_of_isLocalHom`).
   - The resulting `χ` makes `D'` a `P`-algebra with `ψ' ∘ χ = χ_P`, the truncated map of
     `exists_flat_truncation_map`.
5. **Hypotheses of `hf`.**
   - `P` is local and Artinian.
   - `χ` is local, because `χ_P` maps `𝔪_P` onto `𝔪_{Λ̄}`.
   - `D'` is essentially of finite type over `P` (`EssFiniteType.of_comp`, since
     `k → P → D'` is a scalar tower).
   - `D'` is flat over `P` by the imported
     `Langlands.CommutativeAlgebra.flat_of_flat_of_faithfullyFlat`, as `D' → Λ̄` is
     faithfully flat and `P → Λ̄` is flat.
   - `𝔪_P D' = 𝔪_{D'}` by contraction along `ψ'` (`comap_map_of_flat_of_isLocalHom`,
     `maximalIdeal_comap`).
   - `κ_{D'}/κ_P` is separable. The residue classes of the `gD` lie in `κ_P`. Hence
     `Ω_{κ_{D'}/κ_P}`, which is spanned by the images of their differentials
     (`KaehlerDifferential.map_surjective`), vanishes. So the extension is formally unramified, and
     it is separable by `Algebra.FormallyUnramified.isSeparable`.
6. **Conclusion.** `hf` gives `EssentiallySmooth P D'`. With `ψ = ψ'`, the remaining conditions
   are the compatibility `ψ(χ(ȳ)) = φ(y) mod qⁿ` and `E ⊆ ψ'(D')` (as `E ⊆ A`).

## Use

The six hypotheses are published Library statements. The module
`ArtinianSmoothApproximationProof` applies `artinianSmoothApproximation_of` to their published
proofs and obtains the unconditional theorem `artinianSmoothApproximation`.
