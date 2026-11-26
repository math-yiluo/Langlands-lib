# Statement: the twisted van Dijk formula for normalized product inductions

Module `Langlands.BaseChange.TwistedVanDijkStatement`. It states
`TwistedVanDijkStatement.{u, v, uW}` and supplies no proof.

## Source

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique
non nulle*, Mém. SMF 124 (2011), II.4.5, printed p. 86 (PDF p. 94), source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, file SHA-256
`7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`: the Haar normalizations at
the start of II.4.5, the twisted constant term `φ ↦ φ^{P,σ}` and formula (2)

`Θ^{ι_α(B)}_{ι_α(Ξ)}(φ) = Θ^B_Ξ(φ^{P,σ})`,

described there as a simple generalization to the twisted case of van Dijk's formula
(van Dijk, *Computation of certain induced characters of p-adic groups*, Math. Ann. 199
(1972); see also Clozel 1984 and Lemaire, arXiv:1007.3576). The induced intertwiner `ι_α(B)` is
that of II.4.4, printed p. 85.

## The statement

The statement quantifies over a topological field `F` (universe `u`), a nonarchimedean local
field `E` (universe `v`) with an `F`-algebra structure and the `F`-module topology, an
automorphism `σ : E ≃ₐ[F] E`, a rank `n`, a block shape `B` of `n`, and block representations
`P i` of `GL_{n_i}(E)` on spaces `W i` (universe `uW`), admissible, with σ-intertwiners
`A i : SigmaIntertwiner σ (B.size i) (P i)`. No irreducibility, cyclicity, characteristic or
ramification hypothesis is made.

Write `G = GL_n(E)`, `M = B.Levi E`, `U = B.unipotentSubgroup E` (the block upper unipotent
radical of the standard parabolic `P = B.parabolic E`, as a subgroup of `G`) and
`K = GL_n(𝒪_E)` (`GeneralLinearGroup.integralSubgroup (Fin n)` of the valuation ring). All
four groups carry their Borel σ-algebras (subspace σ-algebras on the subgroups). The measures
are Henniart–Lemaire's:

- `μG` is a Haar measure on `G` with `μG K = 1`;
- `μM` is a Haar measure on `M` giving volume one to `M(𝒪_E)`, the set of block tuples with
  every block in `GL_{n_i}(𝒪_E)`;
- `μU` is a Haar measure on `U` giving volume one to `U(𝒪_E) = U ∩ K`;
- `μK` is the Haar probability measure on `K`.

With these normalizations `dg = dm du dk` (Henniart–Lemaire's integration formula); the
statement does not assert this formula.

Let `φ` be a test function on `G` and `ψ` a test function on `M` with

`ψ(x) = δ_P(x)^{1/2} ∫_U ∫_K φ(k⁻¹ x u σ(k)) dk du`

for every `x ∈ M`, where `x` is included in `G` by `B.leviEmbedding E`, `σ(k)` is the
entrywise action `entrywiseAut σ n`, and `δ_P^{1/2}` is
`(LocalFieldData.ofInstances E).leviHalfModulus B`. Then

`twistedDistribution μG (i(P)) ι(A) φ = twistedDistribution μM (P₁ ⊗ ⋯ ⊗ P_r) (A₁ ⊗ ⋯ ⊗ A_r) ψ`,

where `i(P) = (LocalFieldData.ofInstances E).normalizedProductInduced B P`,
`ι(A) = inducedSigmaIntertwiner σ B A`, the Levi representation is `B.blockTensor P` and its
intertwiner is `leviTensorIntertwiner σ B A`. The Library's `twistedDistribution μ ρ hρ A f`
is the finite-rank trace of `ρ(f) ∘ A`, Henniart–Lemaire's `Θ^A_ρ(f)` (II.1.3, II.2.7).

## Relation to the source

- The function `ψ` is Henniart–Lemaire's `φ^{P,σ}`. The statement does not construct the
  constant term: it applies to every test function on `M` with these values. In the source
  `φ^{P,σ}` is a test function by construction; any construction of the constant term as a map
  to test functions with this evaluation formula provides such a `ψ`.
- The integral is written as an iterated Bochner integral, first over `K`, then over `U`,
  in place of the source's integral over `U(E) × K_E`; the integrand is continuous with
  compact support, so the two agree.
- Henniart–Lemaire's modulus `δ_{P(E)}` is defined by `dμ(pδp⁻¹) = δ_{P(E)}(p) dμ(δ)`; on
  `M` it is `|det Ad(m)|_{𝔲(E)}|_E`, which is the Library's `leviModulus`
  (`∏_{i<j} |det m_i|^{n_j} / |det m_j|^{n_i}`).
- The source states (2) for smooth admissible σ-stable `Π_i`; the statement takes admissible
  `P i` and any σ-intertwiners `A i`, as in the source.
- The untwisted van Dijk formula is the case `E = F`, `σ = 1` with identity intertwiners
  (the remark after formula (3) in the source).
