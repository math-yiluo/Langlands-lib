# Enlarging a flat Artinian approximation so that it contains a power of a unit

`Langlands.CommutativeAlgebra.Popescu.ArtinianUnitEnlargementStatement` (universe `u`). Let `k` be a
field of characteristic `p > 0`. Let `D` and `L` be Artinian local `k`-algebras, with `D`
essentially of finite type over `k`, and let `ψ : D → L` be a `k`-algebra map that is a local and
flat ring homomorphism. Let `ℓ ∈ L` be a unit. Let `b₁, …, b_t ∈ D` be such that the differentials
`d(b̄_i)` of their residue classes `b̄_i ∈ κ_D` form a basis of `Ω_{κ_D/k}` (linearly independent and
spanning over `κ_D = ResidueField D`). Then there exist

- an Artinian local `k`-algebra `D'`, essentially of finite type over `k`;
- a `k`-algebra map `ι : D → D'`;
- a `k`-algebra map `ψ' : D' → L` that is local and flat, with `ψ' ∘ ι = ψ`;

such that

1. there are `Q > 0` and `u ∈ D'` with `ψ'(u) = ℓ^Q` and `d(ū) = 0` in `Ω_{κ_{D'}/k}`;
2. there are `r ≥ 0` and `v₁, …, v_r ∈ D'` with `ψ'(v_j) = ℓ` for all `j`, such that the
   differentials of the residue classes of `ι(b₁), …, ι(b_t), v₁, …, v_r` form a basis of
   `Ω_{κ_{D'}/k}` (the family is indexed by `Fin t ⊕ Fin r` via `Sum.elim`).

## Source and provenance

This is a refinement, internal to this project, of Stacks Project, Smoothing Ring Maps, Lemma
16.11.3 (Tag 07FI) and its proof (source `stacks-artin-axioms-approximation-2026-11-06`,
smoothing.pdf, printed pp. 27–28). There, for `λ ∈ Λ \ q`, the ring `D` is enlarged to an
essentially smooth `D → D'` with `D'` flat into `Λ_q/qⁿΛ_q` and `λ^q ∈ D'`. Let `α ∈ κ(q)` be the
residue of `λ` and `F` the residue field of `D`. The proof distinguishes three cases.

- `α ∈ F`. Then `D' = D` and a `p`-power of `λ̄` lies in `D`.
- `α` is transcendental over `F`. Then `D' = D[λ̄]` localized, a polynomial algebra over `D`
  localized, with residue field `F(α)`.
- `α` is algebraic over `F`. Then `α^q` is separable over `F` for a `p`-power `q`. `D'` is the
  finite étale extension of `D` with residue field `F(α^q)`, mapped into the henselian ring
  `Λ_q/qⁿΛ_q`.

The statement records what this construction gives, for a unit `ℓ` and an arbitrary flat local
`ψ`, in terms of differentials.

- In the first and third cases `κ_{D'}/κ_D` is finite separable, so a differential basis of
  `Ω_{κ_D/k}` stays a basis of `Ω_{κ_{D'}/k}` (`r = 0`).
- In the transcendental case `κ_{D'} = κ_D(α)`, and one adds `v = λ̄` (`r = 1`).
- In every case `u` can be taken to be the `p`-th power of an element of `D'` (`Q` a multiple of
  `p`), so `d(ū) = 0`.

This is the form needed to complete Stacks' proof of Lemma 16.11.2 (Tag 07FH). That proof picks
`λ_j ∈ Λ` which map into `A` with `dλ_j` a basis of `Ω_{F/k}`. When `Λ → Λ_q/qⁿΛ_q` is not
surjective, such `λ_j` need not exist for the `A` first chosen. Writing the chosen elements of `A`
as `λ_j/s`, one enlargement for the unit `s̄` replaces them by `λ_j s^{Q-1} ∈ Λ`, whose images are
`ι(a_j)u`.

## Encoding

- `ψ` and `ψ'` are `k`-algebra maps; locality and flatness are those of the underlying ring maps
  (`IsLocalHom`, `RingHom.Flat`).
- Residue classes use `IsLocalRing.residue`, and differentials use `KaehlerDifferential.D k κ`.
- All types are in one universe `u`.
