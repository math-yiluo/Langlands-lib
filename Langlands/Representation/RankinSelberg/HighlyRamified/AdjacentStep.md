# The adjacent-rank step

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. It derives the
induction step of Jacquet–Shalika 1985, §4.4, uniformly in the levels, and assembles the target
from its inputs.

## The Kirillov shell input

`KirillovShellInput` is the test-vector input of the adjacent-rank step. The step uses it
where Jacquet and Shalika use the vector `W'` of (4.4.16)–(4.4.17), but it is an internal
replacement, not their vector. Their `W'` lies in the model of `σ ⊗ χ`, and its Weyl
translate `H'` is supported on the level-`f` shell `ϖ^(-a(r-1)) N_(r-2) K_(r-2)(f)` with a
prescribed constant value (printed page 330). The vector here lies in the model of `σ`, is
supported on the full integral shell, has the values `κ₁ χ(det k)⁻¹`, and has an extra
equivariance under `diag(I, c')`. `KirillovShell.md` (Provenance) lists the differences. The
restriction to `K⁰(f)` that the source builds into `H'` comes here from the weight `φ₁` of
(4.4.18) (`unitLastWeight_firstColumn`, DualWeight, used in `dual_shell_integral`,
DualShellIntegral). Its data: an additive character of conductor
exponent `0`, a generic `σ` of rank `m + 2` with central character `ω_σ`, a nonzero
`ψ⁻¹`-functional `ℓ'`, a quasicharacter `χ`, a unit `ϖ` and `c`. It provides a model vector
`f'` of `σ` and `κ₁ ≠ 0` such that:
- `f'(diag(B,1)) ≠ 0` only if `u B ϖ^c` is integral for some `u ∈ N`;
- `f'(diag(k ϖ^(-c), 1)) = κ₁ χ(det k)⁻¹` for `k ∈ GL_(m+1)(O)`;
- `f'(g diag(I, c')) = (ω_σ χ^(m+1))(c') f'(g)` for integral units `c'`.

It is a hypothesis here, in exactly the form `core_gamma_eq` consumes.

## Auxiliary facts

- `exists_inverseFunctional`: a generic representation has a nonzero functional for the
  inverse standard character. It is the image of a standard functional under the published
  change of character by `-1` (`characterChangeFunctionalEquiv`, `functionalsCongr`,
  `standardCharacter_scale_neg_one`).
- `twist_split`: `π ⊗ χ ∘ det = (π ⊗ ξ ∘ det) ⊗ (ξ⁻¹ χ) ∘ det` (published `twist_twist`).

## The step

`adjacentStep`: from `WhittakerCompletenessStatement`, the essential-vector input
`EssentialPairInput n` for all `n` (EssentialInput), `KirillovShellInput` and the monomial
input `MonomialTwistGamma n` (MonomialGamma), it proves
`UniformPairStability (n + 2) (n + 1)` (candidates of rank `n + 3`, tests of rank `n + 2`). For
levels `m, m'`:
1. `EssentialPairInput n` at level `m` gives `ξ` and `f ≥ 1`, and `MonomialTwistGamma n` at
   levels `m', f` gives `A₀`. The bound is `A = max(A₀, a(ξ) + f + m' + 1)`.
2. Let `a(χ) ≥ A` and `χ' = ξ⁻¹ χ`. Then `a(χ') = a(χ)` because `a(ξ⁻¹) = a(ξ) < a(χ)`
   (`multiplicativeConductor_mul_of_lt`, `multiplicativeConductor_inv`). Put `b = a(χ)` and
   `c = (n + 2) a(χ)`. Then `c ≥ f + b` and `c ≥ 2f`.
3. The candidates `π_i ⊗ ξ ∘ det` are generic. Their central character is `ω₀ ξ^(n+3)`
   (`hasGLCentralCharacter_twist`), trivial on `1 + 𝔭^f`. Their essential vectors are those of
   `EssentialPairInput`.
4. The test `σ` has a central quasicharacter `ω_σ` with `a(ω_σ) ≤ m'`
   (`multiplicativeConductor_le_of_hasGLCentralCharacter`). So `ω_σ` and `χ'` are trivial on
   `1 + 𝔭^b` (`trivialOnPrincipalUnits_of_conductor_le`). `ϖ` is the published uniformizer
   unit, of order `1`.
5. `KirillovShellInput` gives `f'`. The monomial certificates `hGall` come from
   `MonomialTwistGamma n` for `σ^ι` (generic, `isGeneric_inverseTransposePullback_of_inverse`,
   with a level-`m'` vector, `hasPrincipalLevelVector_inverseTransposePullback`) and `χ'⁻¹`
   (`a(χ'⁻¹) = a(χ) ≥ A₀`). Existence of a certificate is the published
   `genericSymmetricGammaFactor_isPadic`. The rank order `n + 1 ≤ n + 2` turns symmetric
   certificates into pair certificates (`isPadicSymmetricGammaFactor_of_le`). The exponent
   `(n + 2)(n + 1) a(χ')` equals `c (n + 1)`.
6. `twist_split` rewrites the given certificates for `π_i ⊗ χ ∘ det` as certificates for
   `(π_i ⊗ ξ ∘ det) ⊗ χ' ∘ det`, and `core_gamma_eq` (CoreStep) gives `G₁ = G₂`.

## The target

`highlyRamifiedGammaStability_of_inputs` proves `HighlyRamifiedGammaStabilityStatement` from:
- `WhittakerCompletenessStatement`, `Conductor.EssentialVectorLevelStatement` and
  `UniformRankOneTwistStatement`, each at the universe `max uF uV uW`;
- `UniformRankOneTwistStatement` at `uV`;
- `KirillovShellInput` at `max uF uV uW`.

`highlyRamifiedGammaStability_of_adjacentStep` (AdjacentInduction) is applied to `adjacentStep`,
with `EssentialPairInput` from `essentialPairInput` (EssentialInput).
