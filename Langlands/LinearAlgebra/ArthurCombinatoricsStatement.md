# Statements of Arthur's combinatorial lemmas

Module `Langlands.LinearAlgebra.ArthurCombinatoricsStatement` states six
combinatorial results of Arthur 1978 and Arthur 2005 as proposition
definitions. Their conjunction is `ArthurCombinatoricsStatement`, the entry
declaration. It supplies no proofs. The objects (`tau`, `tauHat`, `sigma`,
`levelProjection`, `weightCoordinate`, `corootValue`, `epsilon`, `phi`,
`rootAnnihilator`, `corootSpan`) and the dictionary with Arthur's notation
are those of `Langlands.LinearAlgebra.ArthurCombinatorics` (see its
Markdown). A standard parabolic subgroup is a subset `Θ` of the base
`b.support`, `P_1 ⊆ P_2` is `Θ₁ ⊆ Θ₂`, and `G` is `b.support`.

## Sources

- J. Arthur, *A trace formula for reductive groups I* (1978), registered as
  `arthur-1978-trace-formula-reductive-groups-I` (PDF page = printed page
  − 910; pages read as rendered images):
  - Proposition 1.1, p.916 (PDF page 6);
  - §6, pp.938–940 (PDF pages 28–30): the definition of `σ_1^2`, Lemma 6.1,
    Corollary 6.2 and the remark after it, the definitions of `ε_Q^P(Λ)` and
    `φ_Q^P(Λ, H)`, and Lemma 6.3 with its proof.
- J. Arthur, *An introduction to the trace formula* (2005), registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page =
  printed page + 12):
  - Identity 6.2, p.31 (PDF page 43);
  - §8, pp.40–42 (PDF pages 52–54): (8.2) and Lemma 8.3.

## Common hypotheses

Every root-system statement quantifies over the following data, all in one
universe `u`:

- types `ι M N` with `[DecidableEq ι] [Finite ι]` and real vector space
  structures on `M`, `N`;
- `P : RootPairing ι ℝ M N` with `[P.IsRootSystem]` and
  `[P.IsCrystallographic]`, and a base `b : P.Base`.

The relative root system of a connected reductive group is crystallographic,
which is Arthur's setting. The definitions module does not need this
hypothesis. The statements keep it so that they do not claim more than
Arthur proves.

The hypothesis `b : P.Base` (a Mathlib base) limits the statements to
reduced root systems. A Mathlib base has no root whose double or half is a
root. So non-reduced systems of type `BC`, which occur as relative root
systems, have no Mathlib base, already in rank one. For such a group the
statements apply to the reduced subsystem of indivisible relative roots.
That subsystem has Arthur's `Δ_0` as base, and Arthur's functions use only
`Δ_0` and its coroots. The comparison with the full relative root system is
a remaining obligation (Markdown of the definitions module, "Restriction to
reduced root systems").

## The statements

1. `AlternatingSumStatement` (Arthur 1978, Proposition 1.1; Arthur 2005,
   Identity 6.2). For finite sets `Θ₁ ⊆ Θ₂`,
   `∑_{Θ₁ ⊆ Θ ⊆ Θ₂} (−1)^{|Θ₂ \ Θ|} = 1` if `Θ₁ = Θ₂` and `0` otherwise.
   - Arthur sums `(−1)^{dim(A/A_2)}` over parabolics `P_1 ⊆ P ⊆ P_2`, with
     `dim(A_P/A_{P_2}) = |Δ_P^{P_2}| = |Θ₂ \ Θ|`. The statement is pure
     finite combinatorics, so it is stated for any type with decidable
     equality.
2. `TauTauHatVanishingStatement` (the remark after Arthur 1978,
   Corollary 6.2, in the relative form used to prove Lemma 6.3). For
   `Θ_R ⊆ Θ_P ⊆ b.support` with `Θ_R ≠ Θ_P` and every `H`,
   `∑_{Θ_R ⊆ Θ₁ ⊆ Θ_P} (−1)^{|Θ_P \ Θ₁|} τ_R^{P_1}(H) τ̂_{P_1}^P(H) = 0`.
   - Arthur's remark is the case `P = G`. It says `σ_1^1` is the
     characteristic function of the empty set for `P_1 ≠ G`. The proof of
     Lemma 6.3 applies it inside `M_P` ("our remark following Corollary 6.2
     implies that …"), which is the form stated here.
   - Here `τ̂_{P_1}^P` uses the weights `ϖ_i = weightCoordinate P Θ_P i`
     relative to `P`.
3. `SigmaCharacterizationStatement` (Arthur 1978, Lemma 6.1). For
   `Θ₁ ⊆ Θ₂ ⊆ b.support` and every `H`, `σ_{P_1}^{P_2}(H)` is `1` exactly
   when the following hold, and `0` otherwise:
   - (i) `α_i(H_{P_1}) > 0` for `i ∈ Θ₂ \ Θ₁`, that is, `α ∈ Δ_1^2`;
   - (ii) `α_i(H_{P_1}) ≤ 0` for `i ∈ b.support \ Θ₂`, that is,
     `α ∈ Δ_1 \ Δ_1^2`;
   - (iii) `ϖ_i(H) > 0` for `i ∈ b.support \ Θ₂` with
     `ϖ_i = weightCoordinate P b.support i`, that is, `ϖ ∈ Δ̂_2`.

   Arthur describes a subset of `𝔞_1`. The conditions here are on `H_{P_1}`,
   the `𝔞_1`-component. The weights in (iii) vanish on `𝔞_0^{P_2} ⊇ 𝔞_0^{P_1}`,
   so `ϖ_i(H) = ϖ_i(H_{P_1})`. Arthur writes `P_2 ⊃ P_1` with `⊃` meaning
   containment (in Proposition 1.1 `P_1 ⊂ P_2` includes `P_1 = P_2`). The
   case `P_2 = P_1` is the empty set when `P_1 ≠ G`, which is the remark
   after Corollary 6.2. So the statement includes `Θ₁ = Θ₂`.
4. `LanglandsCombinatorialLemmaStatement` (Arthur 1978, Lemma 6.3). For
   `Θ_Q ⊆ Θ_P ⊆ b.support`, `Λ ∈ M` and `H ∈ N`:
   - the sum `∑_{Θ_Q ⊆ Θ_R ⊆ Θ_P} ε_Q^R(Λ) φ_Q^R(Λ, H) τ_R^P(H)` is `0` if
     `Λ(α^∨) ≤ 0` for some `α ∈ Δ_Q^P`, and `1` otherwise;
   - `Λ(α^∨)` is `corootValue P Θ_Q Λ i` for the index `i ∈ Θ_P \ Θ_Q` of
     `α`.

   Arthur takes `Λ ∈ 𝔞_0^*`. Only its restriction to `𝔞_0^G` enters, through
   the values `Λ(α^∨)`.
5. `TauTauHatSigmaExpansionStatement` (Arthur 2005, (8.2)). For
   `Θ₁ ⊆ Θ_P ⊆ b.support` and every `H`,
   `τ_{P_1}^P(H) τ̂_P(H) = ∑_{P_2 ⊇ P} σ_{P_1}^{P_2}(H)`.
   - Arthur derives it from Identity 6.2: inserting the definition of `σ`
     and exchanging the sums leaves
     `∑_{P ⊆ P_2 ⊆ Q} (−1)^{dim(A_2/A_Q)}` as the coefficient of
     `τ_{P_1}^Q τ̂_Q`.
6. `SigmaSupportStatement` (Arthur 2005, Lemma 8.3). For
   `Θ₁ ⊆ Θ₂ ⊆ b.support`:
   - (a) `σ_{P_1}^{P_2}` takes only the values `0` and `1`;
   - (b) there is `c` such that for `H_1^2 ∈ 𝔞_{P_1}^{P_2}`
     (`rootAnnihilator P Θ₁ ⊓ corootSpan P Θ₂`) and `H_2 ∈ 𝔞_{P_2}^G`
     (`rootAnnihilator P Θ₂`) with `σ_{P_1}^{P_2}(H_1^2 + H_2) = 1`, one has
     `τ_{P_1}^{P_2}(H_1^2) = 1` and `‖H_2‖ ≤ c ‖H_1^2‖`.

   Arthur's `H_1 ∈ 𝔞_{P_1}^G = 𝔞_{P_1}^{P_2} ⊕ 𝔞_{P_2}^G` is `H_1^2 + H_2`.
   Statement (a) holds for every `H ∈ N`, since `σ` depends only on
   `H_{P_1}`. Arthur leaves the norm unspecified, and all norms on the
   finite-dimensional `N` are equivalent. The statement uses the `ℓ¹` norm
   in the coroot basis `b.toCoweightBasis`:
   `∑_i |b.toCoweightBasis.repr H_2 i| ≤ c ∑_i |b.toCoweightBasis.repr H_1^2 i|`.
   The constant depends only on the root system and on `P_1, P_2`, as in
   Arthur.

## Scope

- Arthur 1978, Corollary 6.2 is not stated. It is the translate of Lemma 6.1
  by a point `T ∈ 𝔞_0^+` and belongs with the truncation estimates.
- Lemma 6.4 (the partition of `G(𝔸)`) and Arthur 2005, Lemma 8.2 use
  reduction theory and belong to the truncation part of Task 5536.
- The statements concern an abstract reduced root system with a Mathlib
  base. Their use for an actual reductive group needs the specialization
  described in the Markdown of the definitions module. That specialization
  passes through the reduced subsystem of indivisible relative roots when
  the relative root system is of type `BC`. It is not constructed here.
- Proofs: these are statement targets. Each will have its own
  `lean.proof@1` task.
