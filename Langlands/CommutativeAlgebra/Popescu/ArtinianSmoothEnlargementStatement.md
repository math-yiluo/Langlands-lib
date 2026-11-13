# Enlarging an essentially smooth approximation by a power of a unit

`Langlands.CommutativeAlgebra.Popescu.ArtinianSmoothEnlargementStatement` (universe `u`).

Notation as in `ArtinianSmoothApproximationStatement.md`: `Λ_q = Localization.AtPrime q`
with maximal ideal `𝔪_q`, `localTruncation q n = Λ_q ⧸ 𝔪_qⁿ`, `k[y] = MvPolynomial (Fin m) k`
and `toLocalTruncation q n : Λ →+* localTruncation q n` the canonical map.

**Hypotheses** (the data and properties produced by Lemma 11.2).
- `k : Type u` is a field of characteristic `p`, with `p` prime.
- `Λ : Type u` is a `k`-algebra with `GeometricallyRegular k Λ`.
- `q` is a prime of `Λ`, and `n > 0`.
- `φ : k[y] →ₐ[k] Λ`, and `𝔭` is a prime of `k[y]` with `h𝔭 : 𝔭 = q.comap φ`.
- `𝔭.map (algebraMap Λ Λ_q ∘ φ) = 𝔪_q`, and `Localization.localRingHom 𝔭 q φ h𝔭` is
  flat.
- `D : Type u` is a local Artinian ring with an algebra structure of `localTruncation 𝔭 n`
  and `EssentiallySmooth (localTruncation 𝔭 n) D`.
- `ψ : D →+* localTruncation q n` is local and flat, and for every `y ∈ k[y]`,
  `ψ (algebraMap (localTruncation 𝔭 n) D (toLocalTruncation 𝔭 n y)) =
  toLocalTruncation q n (φ y)`.
- `l ∈ Λ` with `l ∉ q`.

**Conclusion.** There are `e > 0`, a local Artinian ring `D' : Type u`, algebra structures
of `D` and of `localTruncation 𝔭 n` on `D'` forming a scalar tower
`localTruncation 𝔭 n → D → D'`, and a ring map `ψ' : D' →+* localTruncation q n` such that

- `EssentiallySmooth D D'` and `EssentiallySmooth (localTruncation 𝔭 n) D'`;
- `ψ'` is local and flat;
- `ψ' ∘ algebraMap D D' = ψ`;
- `toLocalTruncation q n l ^ e ∈ Set.range ψ'`: the `e`-th power of the image of `l` in
  `localTruncation q n` lies in the image of `ψ'`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 11.3 (Tag 07FI, printed p. 27):

> Let φ : k[y₁, …, y_m] → Λ, n, q, p and k[y₁, …, y_m]_p/pⁿ → D → Λ_q/qⁿΛ_q be as in
> Lemma 11.2. Then for any λ ∈ Λ \ q there exists an integer q > 0 and a factorization
> k[y₁, …, y_m]_p/pⁿ → D → D′ → Λ_q/qⁿΛ_q such that D → D′ is an essentially smooth
> map of local Artinian rings, the last arrow is flat, and λ^q is in D′.

## Encoding and scope

- **"As in Lemma 11.2".** The hypotheses are the conclusions (1) and (2) of
  `ArtinianSmoothApproximationStatement` for the given `φ` and `D`, together with the
  standing hypotheses of Lemma 11.2. They are encoded in the same way, including the bound
  prime `𝔭` with `𝔭 = q.comap φ`; see `ArtinianSmoothApproximationStatement.md`.
- **The exponent.** The source calls the exponent "q", which is also the prime. Here it is
  `e`, and `λ` is `l`.
- **The factorization.** `D → D′ → Λ_q/qⁿΛ_q` factoring `ψ` is `ψ' ∘ algebraMap D D' = ψ`.
  The scalar tower makes `localTruncation 𝔭 n → D′` the composite through `D`.
- **Local homomorphisms.** "A map of local Artinian rings" is encoded as `D'` local
  Artinian. As in Lemma 11.2, `ψ'` is required to be local; the proof of Lemma 11.4 uses
  this to get faithful flatness of `D′ → Λ_q/qⁿΛ_q` (step (13), printed p. 30). The source
  proof gives a local `ψ'` in each case: `D′ = D`, `D′ = (D[λ̄])_𝔪` with
  `𝔪 = D[λ̄] ∩ qΛ̄`, and a finite étale local extension `D′` of `D` mapping to
  `Λ̄ = Λ_q/qⁿΛ_q`.
- **The extra conclusion.** `EssentiallySmooth (localTruncation 𝔭 n) D'` is not part of the
  source statement. It is the composite of `localTruncation 𝔭 n → D` and `D → D′`, both
  essentially smooth, and holds for the three cases of the source proof. Lemma 11.4 uses it
  when it applies this lemma repeatedly (step (13)) and when it uses "D′ is essentially
  smooth over the local Artinian ring k[y₁, …, y_m]_p/pⁿ" (step (25), printed p. 31).
- **"λ^q is in D′".** This means that the image of `l` in `Λ_q/qⁿΛ_q`, raised to the power
  `e`, lies in the image of `ψ'`.
- **Universe.** `k`, `Λ`, `D` and `D'` are in one universe `u`.
