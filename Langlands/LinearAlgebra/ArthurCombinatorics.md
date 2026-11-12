# Arthur's combinatorics of standard parabolic subgroups

Module `Langlands.LinearAlgebra.ArthurCombinatorics` defines the vector
spaces, projections, weights and characteristic functions of Arthur's
combinatorics of standard parabolic subgroups. It does so for an abstract
root system with a base. It proves the decomposition `𝔞_0^G = 𝔞_0^P ⊕ 𝔞_P^G`
and that the explicit formulas below give the actual projections and dual
coordinates. All proofs are complete. The combinatorial lemmas about these
functions are stated in `Langlands.LinearAlgebra.ArthurCombinatoricsStatement`
(see its Markdown).

This is the first part of item 1 ("parabolic combinatorics") of the L3
truncation block, Task 5536, carried out by the parent program. The contract
of Task 5536 allows an abstract layer over a root pairing with a base,
provided its specialization to the actual relative root system is
constructed. The specialization is not part of this module (see Scope).

## Sources

- J. Arthur, *A trace formula for reductive groups I: terms associated to
  classes in G(ℚ)*, Duke Math. J. 45 (1978), registered as
  `arthur-1978-trace-formula-reductive-groups-I` (PDF page = printed page
  − 910; the text layer is unreliable, so pages were read as rendered
  images):
  - §1, pp.915–916 (PDF pages 5–6). `𝔞_P = Hom(X(M_P)_ℚ, ℝ)`; the simple roots
    `Δ_P`; `Δ_0` is a base of a root system with coroots `α^∨ ∈ 𝔞_0`. For
    `P_1 ⊆ P_2`: `Δ_{P_1}^{P_2} ⊆ Δ_{P_1}`, and `P_2 ↦ Δ_{P_1}^{P_2}` is a
    bijection from parabolics containing `P_1` onto subsets of `Δ_{P_1}`.
    Also `𝔞_{P_2} = {H ∈ 𝔞_{P_1} : α(H) = 0, α ∈ Δ_{P_1}^{P_2}}`,
    `𝔞_{P_1} = 𝔞_{P_1}^{P_2} ⊕ 𝔞_{P_2}` and
    `𝔞_0^{P_2} = 𝔞_0^{P_1} ⊕ 𝔞_{P_1}^{P_2}`. Each `α ∈ Δ_{P_1}^{P_2}` is the
    restriction of a unique `β ∈ Δ_0^{P_2}`, and `α^∨` is the projection of
    `β^∨` onto `𝔞_{P_1}^{P_2}`. `Δ̂_{P_1}^{P_2} = {ϖ_α}` is the basis dual to
    `{α^∨}`.
  - §6, pp.938–940 (PDF pages 28–30). `τ_{P_1}^{P_2}` and `τ̂_{P_1}^{P_2}`,
    regarded as functions on `𝔞_0`. Also
    `σ_1^2(H) = ∑_{P_3 ⊇ P_2} (−1)^{dim(A_2/A_3)} τ_1^3(H) τ̂_3(H)`, and before
    Lemma 6.3 the sign `ε_Q^P(Λ)` and Langlands' function `φ_Q^P(Λ, H)`.
- J. Arthur, *An introduction to the trace formula*, in: Harmonic Analysis,
  the Trace Formula, and Shimura Varieties, Clay Math. Proc. 4 (2005),
  registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`
  (PDF page = printed page + 12), §8, pp.39–42 (PDF pages 51–54). The same
  functions, regarded as characteristic functions on `𝔞_0` that depend only
  on the projection onto `𝔞_{P_1}^{P_2}` relative to
  `𝔞_0 = 𝔞_0^{P_1} ⊕ 𝔞_{P_1}^{P_2} ⊕ 𝔞_{P_2}`.

## The abstract setting

The data are `P : RootPairing ι ℝ M N` with `[DecidableEq ι]`. The lemmas
also use a base `b : P.Base` (Mathlib's `RootPairing.Base`), `[Finite ι]`
and `[P.IsRootSystem]`. The dictionary with Arthur:

- `N` is `𝔞_0^G` and `M = (𝔞_0^G)^*`, with the perfect pairing
  `P.toLinearMap`. Arthur's `𝔞_0 = 𝔞_0^G ⊕ 𝔞_G` also has the central part
  `𝔞_G`. Every function below depends only on the projection to `𝔞_0^G`,
  because the roots and the weights `ϖ` vanish on `𝔞_G`. So the abstract
  layer works on `𝔞_0^G`, and `IsRootSystem` (roots span `M`, coroots span
  `N`) is the right hypothesis.
- The simple roots `Δ_0` are `P.root i`, `i ∈ b.support`, with coroots
  `P.coroot i`.
- A standard parabolic subgroup `P` is recorded by
  `Θ = Δ_0^P ⊆ b.support`, the simple roots of its Levi component, so
  `P_1 ⊆ P_2` corresponds to `Θ₁ ⊆ Θ₂`. Then `Δ_{P_1}^{P_2}` corresponds to
  `Θ₂ \ Θ₁`, `Δ_P = Δ_P^G` to `b.support \ Θ`, and
  `dim(A_{P_1}/A_{P_2}) = |Θ₂ \ Θ₁|`.

## Definitions

- `corootSpan P Θ` is `𝔞_0^P = span{α_i^∨ : i ∈ Θ}`.
- `rootAnnihilator P Θ` is `𝔞_P^G = {H : α_i(H) = 0, i ∈ Θ}`. For
  `P_1 ⊆ P_2`, `𝔞_{P_1}^{P_2}` is
  `rootAnnihilator P Θ₁ ⊓ corootSpan P Θ₂`.
- `cartanBlock P Θ` is the matrix `(α_k(α_j^∨))_{k, j ∈ Θ}`, with the simp
  lemma `cartanBlock_apply`.
- `weightCoordinate P Θ i` is the linear form `∑_{k ∈ Θ} (A_Θ⁻¹)_{ik} α_k`,
  `A_Θ = cartanBlock P Θ`, for `i ∈ Θ`, and `0` for `i ∉ Θ`. For `Θ` in a
  base, `ϖ_i(α_j^∨) = δ_{ij}` for `j ∈ Θ` (`weightCoordinate_coroot`) and
  `ϖ_i` vanishes on `𝔞_P^G`
  (`weightCoordinate_eq_zero_of_mem_rootAnnihilator`). So `ϖ_i(H)` is the
  coefficient of `α_i^∨` in the `𝔞_0^P`-component of `H`.
  - This is Arthur's `ϖ_α ∈ Δ̂_{P_1}^{P}`, for `α ∈ Δ_{P_1}^P` the root
    attached to `i ∈ Θ \ Θ₁`, evaluated on `𝔞_0` through the projection onto
    `𝔞_{P_1}^P`. Write `H = X + ∑_{i ∈ Θ \ Θ₁} c_i α^∨_i + Z` with
    `X ∈ 𝔞_0^{P_1}`, `Z ∈ 𝔞_P^G` and `α^∨_i` the projection of `β_i^∨`. Then
    `ϖ_α(H) = c_i`. Writing `β_i^∨ = α^∨_i + (β_i^∨ − α^∨_i)` with the
    second term in `𝔞_0^{P_1}` shows that `c_i` is the coefficient of
    `β_i^∨` in the `𝔞_0^P`-component of `H`.
  - In particular `ϖ_α` depends only on `P` and `α`, not on `P_1`.
- `levelProjection P Θ = id − ∑_{j ∈ Θ} ϖ_j(·) α_j^∨` is `H ↦ H_P`, the
  projection of `𝔞_0^G = 𝔞_0^P ⊕ 𝔞_P^G` onto `𝔞_P^G`. Its values lie in
  `𝔞_P^G` (`levelProjection_mem_rootAnnihilator`) and
  `H − H_P ∈ 𝔞_0^P` (`sub_levelProjection_mem_corootSpan`).
- `tau P Θ₁ Θ₂ H` is `τ_{P_1}^{P_2}(H)`. It is `1` if `α_i(H_{P_1}) > 0` for
  every `i ∈ Θ₂ \ Θ₁`, and `0` otherwise. The root `α ∈ Δ_{P_1}^{P_2}` is the
  restriction of `β_i` to `𝔞_{P_1}`, and a function on `𝔞_{P_1}` is
  evaluated on `𝔞_0` through `H ↦ H_{P_1}`. Only the
  `𝔞_{P_1}^{P_2}`-component matters, since `β_i` vanishes on
  `𝔞_{P_2} ⊆ rootAnnihilator Θ₂`.
- `tauHat P Θ₁ Θ₂ H` is `τ̂_{P_1}^{P_2}(H)`. It is `1` if `ϖ_i(H) > 0` for
  every `i ∈ Θ₂ \ Θ₁` with `ϖ_i = weightCoordinate P Θ₂ i`, and `0`
  otherwise. For `Θ₂ = b.support` this is Arthur's `τ̂_{P_1} = τ̂_{P_1}^G`.
- `sigma P S Θ₁ Θ₂ H` is Arthur's
  `σ_{P_1}^{P_2}(H) = ∑_{P_3 ⊇ P_2} (−1)^{dim(A_2/A_3)} τ_{P_1}^{P_3}(H) τ̂_{P_3}(H)`,
  with `G` given by `S` (in the statements `S = b.support`). The sum runs
  over `Θ₂ ⊆ Θ₃ ⊆ S` with sign `(−1)^{|Θ₃ \ Θ₂|}`, and `τ̂_{P_3} =
  tauHat P Θ₃ S`.
- `corootValue P Θ_Q Λ i` is `Λ(α^∨)` for `Λ ∈ 𝔞_0^* = M` and the root
  `α ∈ Δ_Q^P` attached to `i`. Its coroot `α^∨` is the projection of `β_i^∨`
  onto `𝔞_Q^P`. Since `β_i^∨ ∈ 𝔞_0^P`, this is its `𝔞_Q`-component
  `levelProjection P Θ_Q β_i^∨`, which does not depend on `P`.
- `epsilon P Θ_Q Θ_P Λ` is `ε_Q^P(Λ) = (−1)^{#{α ∈ Δ_Q^P : Λ(α^∨) ≤ 0}}`.
- `phi P Θ_Q Θ_P Λ H` is `φ_Q^P(Λ, H)`: `1` if for every `α ∈ Δ_Q^P`,
  `ϖ_α(H) > 0` when `Λ(α^∨) ≤ 0` and `ϖ_α(H) ≤ 0` when `Λ(α^∨) > 0`, and `0`
  otherwise. Here `ϖ_α = weightCoordinate P Θ_P i`.

The functions are integer valued so that the alternating sums are integer
sums. The definitions are total. Outside the intended range (a set not
contained in a base, or `Θ₁ ⊄ Θ₂`) they are formulas without meaning, and
the statements always assume the intended range.

## Proved results

- `isCompl_corootSpan_rootAnnihilator`: for `Θ ⊆ b.support`, `𝔞_0^P` and
  `𝔞_P^G` are complementary.
  - The intersection is `0`. Use the invariant form
    `CorootForm(x, y) = ∑_k α_k(x) α_k(y)` on `N`. Mathlib's
    `corootForm_self_smul_root` gives
    `CorootForm(α_i^∨, α_i^∨) α_i(Y) = 2 CorootForm(α_i^∨, Y)`. Hence a vector
    `Y ∈ 𝔞_0^P` killed by the `α_i`, `i ∈ Θ`, has `CorootForm(Y, Y) = 0`.
    Then every root vanishes on `Y`, and `Y = 0` because the roots span `M`
    and the pairing is perfect.
  - The sum is everything by counting dimensions. The coroots of a base are
    linearly independent, so `dim 𝔞_0^P = |Θ|`, and `𝔞_P^G` is the kernel of
    `|Θ|` linear forms.
- `isUnit_det_cartanBlock`: the Cartan block of a subset of a base is
  invertible. A vector `v` in its kernel gives `∑_j v_j α_j^∨` in the
  intersection above.
- `weightCoordinate_coroot`, `weightCoordinate_eq_zero_of_mem_rootAnnihilator`,
  `levelProjection_mem_rootAnnihilator`, `sub_levelProjection_mem_corootSpan`:
  the characterizations quoted above.

The proofs do not use the crystallographic condition.

## Restriction to reduced root systems

Every lemma here, and every statement of the statement module, assumes a
Mathlib base `b : P.Base`. That is a real restriction.

- `RootPairing.Base` requires every root to be an integral combination of
  the base roots, with coefficients of one sign, and every coroot to be such
  a combination of the base coroots.
- Its lemma `eq_one_or_neg_one_of_mem_support_of_smul_mem` shows that no
  base root has its double or its half among the roots.
- So a non-reduced root system of type `BC` has no Mathlib base. Already
  `BC_1`, with roots `±a, ±2a`, has none: choosing `a` leaves the coroot
  `a^∨/2` of `2a` outside the integral span of `a^∨`, and choosing `2a`
  leaves `a` outside the span of `2a`. (Reviewer 2215 observed this.)

The relative root system of a connected reductive group can be of type `BC`.
For such a group the module does not apply to the full relative root system.

Arthur's `Δ_0`, the simple roots of `(P_0, A_0)`, consists of indivisible
roots. It is a base of the reduced root system of indivisible relative
roots, with their coroots. Arthur's constructions use only `Δ_0` and the
coroots `α^∨`, `α ∈ Δ_0`. So the intended specialization goes through that
reduced subsystem. Constructing it, with its Mathlib base, and comparing its
roots, coroots, weights and parabolic indexing with the full relative root
system remains an obligation. It is not done here.

## Scope

The module does not construct the specialization to the relative root
system of an actual connected reductive group over a number field. That
needs the following, none of which is done here:

- the Library's relative root pairing (`RootReflectionAssembly.rootPairing`,
  over `ℚ` on the root span);
- passage to the reduced subsystem of indivisible roots and a Mathlib base
  for it (see above), compared with
  `HasRelativeRootSystem.simpleRelativeRootBasis`;
- base change to `ℝ`;
- the identification of `𝔞_P` with `RealCharacterDual F P` (Task 5536,
  item 1).

It also leaves out `(G, M)`-families and truncation (items 2 and 3 of
Task 5536).
