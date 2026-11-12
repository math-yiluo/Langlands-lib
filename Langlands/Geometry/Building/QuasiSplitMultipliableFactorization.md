# Opposite factorization inside a piece over a multipliable relative root

Author: Worker 4783.

Lean module: `Langlands.Geometry.Building.QuasiSplitMultipliableFactorization`.

This internal unit belongs to task 8ffe0456. It continues
`Langlands.Geometry.Building.QuasiSplitMultipliablePieces` with the group theory of a single
piece `{p, q, m = p + q}` over a multipliable relative root `a`. It provides:

- a rank-one Gauss decomposition;
- the factorization of a piece element as (negative part) · (normalizer point) ·
  (negative part);
- the exact value of the commutator `[Y, X_q]`;
- uniqueness and reordering of piece coordinates;
- the effect of a symmetry exchanging `p` and `q`.

Notation as in `QuasiSplitMultipliablePieces`. `U_χ` is `rootGroupPoints j χ` for
`j : T.toGrp ⟶ G` with `G` affine. `[x, y] = x y x⁻¹ y⁻¹`. A piece is given by indices
`lp ≠ lq`, `lm` of a root datum `P` of `j` with `P.root lm = P.root lp + P.root lq`; `p`,
`q` restrict to `a`, under `RestrictsToMultipliableLine f P a`.

## Pieces

- `IsMultipliablePiece f P a lp lq lm` (definition): `lp ≠ lq` are roots of `P` restricting
  to `a` along `f`, and `P.root lm = P.root lp + P.root lq`. This bundles the piece
  hypotheses used in this unit and the next one. `IsMultipliablePiece.swap` exchanges `lp`
  and `lq`.

## Rank one

- `inv_conj_mem_rootGroupPoints`: for a normalizer point `n`, `n⁻¹ U_{nχ} n ⊆ U_χ`. This is
  the published `conj_mem_rootGroupPoints` applied to `n⁻¹`.
- `gauss_decomposition`: let `j` have opposite factor pairs, `T` split, `-α` a root,
  `f ∈ U_{-α}` and `X ∈ U_α`. Then one of the following holds.
  - `f X = X' τ f'` with `X' ∈ U_α`, `τ` normalizing `j`, and `f' ∈ U_{-α}`.
  - `f X = B ν` with `B ∈ U_α` and `ν` normalizing `j` with `ν α = -α`.

  Proof. If `f = 1`, take `X' = X`. Otherwise let `(B₁, B₂)` be the opposite pair of `f`,
  with product `μ_f`, which sends `α` to `-α`. Then `f X = B₁⁻¹ μ_f Z` with
  `Z = B₂⁻¹ X ∈ U_α`. If `Z = 1`, this is the second case. Otherwise `μ_f Z μ_f⁻¹ ∈ U_{-α}`
  is nontrivial; let `(D₁, D₂)` be its pair, with product `μ'`. Then
  `f X = (B₁⁻¹ D₁⁻¹) (μ' μ_f) (μ_f⁻¹ D₂⁻¹ μ_f)`.

## Factorization of a piece element

The setting adds: `G` smooth and locally of finite type, `j` a closed monomorphism with
opposite factor pairs, `T` split, and `IsRootDatumOf j P`.

- `piece_weylAction_m`: the opposite-pair product `μ` of a nontrivial `X_m ∈ U_m` sends `p`
  to `-q` and `q` to `-p`. This is `weylAction_oppositeFactorPair_eq` with `⟨p, m^∨⟩ = 1`
  and `⟨q, m^∨⟩ = 1`.
- `piece_factorization`: let `h = X_q X_m X_p` with `X_q ∈ U_q`, `X_m ∈ U_m` nontrivial and
  `X_p ∈ U_p`. Let `(Y, Y')` be the opposite pair of `X_m`, `μ = Y X_m Y'`, and
  `d = [Y, X_q]`. Then one of the following holds.
  - `h = (Y⁻¹ d e) (μ τ) (f' c Y'⁻¹)` with `e ∈ U_{-q}`, `τ` normalizing `j`,
    `f' ∈ U_{-p}`, `c ∈ U_{-q}`.
  - `h = (Y⁻¹ d e) ν (c Y'⁻¹)` with `e ∈ U_{-q}`, `c ∈ U_{-q}`, and `ν` normalizing `j`
    with `ν p = q`.

  Proof. Write `X_m = Y⁻¹ μ Y'⁻¹`. Then `X_q Y⁻¹ = Y⁻¹ d X_q`, with `d ∈ U_{-p}`
  (`piece_commutator_mem_neg_m_q`). Also `Y'⁻¹ X_p = X_p c Y'⁻¹`, where
  `c = [X_p⁻¹, Y'⁻¹] ∈ U_{-q}`. Hence `h = Y⁻¹ d μ (f X_p) c Y'⁻¹` with
  `f = μ⁻¹ X_q μ ∈ U_{-p}`. Apply `gauss_decomposition` to `f X_p`, and move the factor of
  `U_p` across `μ`, where it becomes `e = μ X' μ⁻¹ ∈ U_{-q}`. In the second case
  `ν = μ ν'` sends `p` to `μ(-p) = q`.
- `piece_val_commutator_neg_m`: for a point `x` of a normalizer-stable apartment class of `j`
  (with `G` connected reductive and `j` a maximal split torus), `Y ∈ U_{-m}` nontrivial and
  `Z ∈ U_q`: `x_{-p}([Y, Z]) = x_q(Z) + x_{-m}(Y)`. The index of `-m` is
  `P.reflectionPerm lm lm`, with coroot `-m^∨` and `⟨q, -m^∨⟩ = -1`. The proof combines
  `piece_conj_eq_commutator_neg_m` with the reflection formula
  `KPApartmentData.val_eq_val_conj_oppositeFactorPair`.

## Uniqueness, reordering and symmetry

- `eq_one_of_mem_rootGroupPoints_of_mem_unipotent`: a point of `U_δ` in the dynamic unipotent
  subgroup of `-ν`, where `⟨δ, ν⟩ > 0`, is trivial (published
  `eq_one_of_mem_subgroup_of_mem_negative_parabolic`).
- `piece_eq_of_mul_eq` (**uniqueness**): `x z y = x' z' y'` with `x, x' ∈ U_q`,
  `z, z' ∈ U_m`, `y, y' ∈ U_p` forces equal factors. Proof:
  `x'⁻¹ x = z' (y' y⁻¹) z⁻¹` lies in `U_q` and in the dynamic unipotent subgroup of `p^∨`,
  since `⟨m, p^∨⟩ = 1` and `⟨p, p^∨⟩ = 2`, while `⟨q, -p^∨⟩ = 1`. So `x = x'`. Then
  `z'⁻¹ z = y' y⁻¹ ∈ U_m ∩ U_p`, which is trivial by the cocharacter `q^∨`.
- `piece_reorder`: `x z y = y (z [x, y]) x`, and `z [x, y] ∈ U_m`. This uses that `U_m`
  commutes with `U_q` and with `U_p`.
- `piece_swap`: let `s` be an endomorphism of the rational points. Let `σ` be a map on
  characters exchanging `p` and `q` and fixing `m`. Assume `s` carries each `U_χ` into
  `U_{σχ}` and `φ_{σχ}(s w) = φ_χ(w)`. If `s` fixes `x z y`, then `s x = y`, `s y = x`,
  `s z = z [x, y]`. Hence `φ_p(y) = φ_q(x)` and `φ_m(z [x, y]) = φ_m(z)`. Proof:
  `s(x z y) = (s x)(s z)(s y)` is a product in the order `p, m, q`. By `piece_reorder`,
  `x z y = y (z [x, y]) x`. Uniqueness in the order `p, m, q` concludes. In the application,
  `s` is the Galois action on `G(K)` for a Galois element exchanging `p` and `q`.

## Provenance

These are the group-theoretic steps replacing the explicit `SU₃` computation of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §2.7 and §3.2, used in their
proof of Proposition 6.1.19 (printed pp. 206–207, PDF pp. 237–238) for roots of type R2. The
statements are internal. Their proofs compose published Library results: opposite factor
pairs, separation of opposite root groups, dynamic unipotent subgroups, and Weyl actions of
normalizer points. They also use the preceding unit `QuasiSplitMultipliablePieces`.

## Scope

This unit proves no axiom of the descended family by itself. The degenerate case of
`piece_factorization` is excluded only later, using the original normalizer point; the
Galois symmetry is applied in the final unit.
