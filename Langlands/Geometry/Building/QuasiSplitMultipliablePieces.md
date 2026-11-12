# Root pieces over a multipliable relative root

Author: Worker 4783.

Lean module: `Langlands.Geometry.Building.QuasiSplitMultipliablePieces`.

This internal unit belongs to task 8ffe0456. It prepares the proof of axiom V 5 at
multipliable relative roots (type R2) for the descended quasi-split family. Over a splitting
field, the absolute roots over a multipliable relative root `a` split into *pieces*
`{p, q, m = p + q}`: `p` and `q` restrict to `a`, and `m` restricts to `2a`. This module
provides:

- the root combinatorics of pieces;
- the commutation relations between their root groups;
- the reflection–commutator identity;
- exact values of commutators at points of a normalizer-stable apartment class.

Notation. `T` is a commutative group scheme over a field, `j : T.toGrp ⟶ G`, and `P` is a
root datum of `j` (`IsRootDatumOf j P`) with finitely many roots. For a character `χ` of `T`,
`U_χ` is `rootGroupPoints j χ`, the rational points of `RelativeRoot.subgroup j χ`. A second
commutative group scheme `S` comes with `f : S ⟶ T`, and the restriction of `χ` is `f ≫ χ`.
`⟨χ, l^∨⟩` is `P.toLinearMap χ (P.coroot l)`. The commutator of `x, y` is
`x * y * x⁻¹ * y⁻¹`.

## Combinatorics

- `RestrictsToMultipliableLine f P a` (definition): every root of `P` whose restriction is
  `n • a` (`n : ℤ`) has `n ∈ {1, 2, -1, -2}`. In the application `a` is a multipliable
  relative root; by `hzero` (no root restricts to `0`) and the relative root system, the
  roots over the line of `a` restrict to `±a` and `±2a`.
- `comp_root_reflectionPerm`: the restriction of the reflected root `s_{l'}(l)` is
  `f ≫ P.root l - ⟨l, l'^∨⟩ • (f ≫ P.root l')`. `pairing_eq_of_root_eq` computes pairings
  linearly.
- `sub_pairing_mem_of_restrictsToMultipliableLine` (**reflection bound**): if `l'` restricts
  to `a` and `l` restricts to `c • a`, then `c - ⟨l, l'^∨⟩ ∈ {1, 2, -1, -2}`. It applies the
  definition to `s_{l'}(l)`.
- For distinct roots `l ≠ l'` over `a`:
  - `pairing_eq_zero_or_neg_one`: `⟨l, l'^∨⟩` is `0` or `-1`. A positive pairing would make
    `P.root l - P.root l'` a root (Mathlib `root_sub_root_mem_of_pairingIn_pos`), restricting
    to `0`.
  - `exists_root_add_iff`: `P.root l + P.root l'` is a root exactly when `⟨l, l'^∨⟩ = -1`. If
    the pairing were `0`, reflecting the sum in `l'` would give the root `P.root l - P.root l'`.
  - `partner_unique`: `l` has at most one such partner. With two partners `l₁ ≠ l₂`, the root
    `P.root l + P.root l₁` reflected in `l₂` would restrict to `3a` or `4a`.
  - `pairing_symm_of_neg_one`: the partner relation is symmetric.
- `combination_bounds`: let `ξ` be a root over `a`, and `α`, `δ` characters restricting to
  `cα • a`, `cδ • a` and pairing to `sα`, `sδ` with `ξ^∨`. If `n • α + l • δ` is a root, then
  `n cα + l cδ` and `(n cα + l cδ) - (n sα + l sδ)` are `±1` or `±2`.
  `combination_ne_zero`: the combination is nonzero if `n sα + l sδ ≠ 0`. These two lemmas
  reduce each root-exclusion argument below to linear arithmetic (`omega`).

## Group lemmas

The setting is an affine smooth `G`, a monomorphism `j`, and a split `T`.

- `commutator_mem_of_only_root_combination`: assume `j` has opposite factor pairs, and the
  only root among the combinations `n • α + l • δ` (`n, l > 0`, all nonzero) is `α + δ`.
  Then `[U_α, U_δ] ⊆ U_{α+δ}`. The published `semigroupCommutator` places the commutator in
  the subgroup of these combinations. The published
  `mem_semigroupSubgroup_iff_existsUnique_rootPointsProduct`, with the one-point enumeration
  of `α + δ`, identifies that subgroup with `U_{α+δ}`.
- `eq_one_of_mem_rootGroupPoints_of_pairing`: if a cocharacter pairs positively with `δ` and
  negatively with `ε`, then `U_δ ∩ U_ε = 1` (published
  `eq_one_of_mem_subgroup_of_mem_negative_parabolic`).
- `conj_eq_commutator_of_oppositeFactorPair` (**reflection–commutator identity**): let
  `X ∈ U_α` have opposite pair `(A, B)`, and suppose `μ = A X B` carries `δ` to `ε`. Assume
  `U_{-α}` commutes with `U_δ`, `U_δ` commutes with `U_ε`, `[U_α, U_δ] ⊆ U_ε`,
  `[U_{-α}, U_ε] ⊆ U_δ`, and `U_δ ∩ U_ε = 1`. Then `μ Z μ⁻¹ = [X, Z]` for `Z ∈ U_δ`. Proof:
  write `E = [X, Z]` and `c = [A, E] ∈ U_δ`. Then `μ Z μ⁻¹ = E (c Z)` with `μ Z μ⁻¹` and `E`
  in `U_ε`, so `c Z ∈ U_δ ∩ U_ε` is `1`.

## Reflection formula

Here `D` is a published `KPApartmentData i ω` for a maximal split torus `i` of a connected
reductive group, and `x` an apartment point.

- `KPApartmentData.oppositeFactorPair_smul_vsub`: let `u ∈ U_α` be nontrivial with opposite
  pair `p` and value `t = x_α(u)`. Then the product `μ` of the pair moves `x` by `-t` times
  the published coroot class `oppositeFactorPairCorootClass`. Proof: as in the published
  `rootForm_oppositeFactorPair_vsub`, `μ` fixes the point `x - (t/2) c`
  (`oppositeFactorPair_smul_eq_self`) and acts linearly by the reflection along `c`
  (`translationAction_oppositeFactorPair`).
- `KPApartmentData.val_eq_val_conj_oppositeFactorPair`:
  `x_δ(Z) = x_{μδ}(μ Z μ⁻¹) + t ⟨δ, ν⟩`, where `ν` is the published integral coroot
  `IsOppositeFactorPair.coroot` and `μδ` is the published `weylAction`. Proof: evaluate the
  identity `μ • x = (-t ν) + x` at `(μδ, μ Z μ⁻¹)`, using
  `⟨μδ, ν⟩ = -⟨δ, ν⟩` (published `coroot_spec`).

## Pieces

A piece is given by indices `lp ≠ lq` of roots over `a` and an index `lm` with
`P.root lm = P.root lp + P.root lq` (hypotheses `hp`, `hq`, `hpq`, `hm`), under
`RestrictsToMultipliableLine f P a`.

- `piece_pairing_pq`, `piece_pairing_qp`: `⟨p, q^∨⟩ = ⟨q, p^∨⟩ = -1`.
- `piece_coroot_m`: `m^∨ = p^∨ + q^∨`, since `m = s_q(p)` and coroots transform by the
  coreflection.
- `piece_pairings`: the table of pairings `⟨p, p^∨⟩ = ⟨q, q^∨⟩ = ⟨m, m^∨⟩ = 2`,
  `⟨q, p^∨⟩ = ⟨p, q^∨⟩ = -1`, and `⟨m, p^∨⟩ = ⟨m, q^∨⟩ = ⟨p, m^∨⟩ = ⟨q, m^∨⟩ = 1`.
- `piece_restrictions`: the restrictions `a, a, 2a, -a, -a, -2a` of `p, q, m, -p, -q, -m`.
- `root_mem_relativeRoots`, `mem_range_root_of_mem_relativeRoots`: the roots of `P` are the
  published `relativeRoots j`. `toLinearMap_neg_root` computes pairings of negated roots.

Commutation, assuming `T` split, opposite factor pairs for `j`, and `IsRootDatumOf j P`. Each
proof applies the group lemmas above; `combination_bounds` with a suitable root `ξ ∈ {p, q}`
excludes every other combination, by `omega`.

- `piece_commutator_mem_pq`: `[U_p, U_q] ⊆ U_m`.
- `piece_commute_neg_p_q`: `U_{-p}` and `U_q` commute.
- `piece_commute_m_q`: `U_m` and `U_q` commute.
- `piece_commute_neg_m_neg_p`: `U_{-m}` and `U_{-p}` commute.
- `piece_commutator_mem_neg_p_m`: `[U_{-p}, U_m] ⊆ U_q`.
- `piece_commutator_mem_m_neg_p`: `[U_m, U_{-p}] ⊆ U_q`.
- `piece_commutator_mem_neg_m_q`: `[U_{-m}, U_q] ⊆ U_{-p}`.
- `piece_eq_one_of_mem_q_of_mem_m`: `U_q ∩ U_m = 1`, using the cocharacter `-p^∨`.
- `piece_eq_one_of_mem_q_of_mem_neg_p`: `U_q ∩ U_{-p} = 1`, using `m^∨`.

Reflections, assuming moreover that `G` is locally of finite type and `j` a closed subgroup.

- `IsOppositeFactorPair.coroot_eq_rootDatum`: the integral coroot of an opposite pair of a
  nontrivial point of `U_{P.root l}` is `P.coroot l`. This is the published
  `IsRootDatumOf.coroot_eq_of_weylAction_of_finite_weylImage`; the Weyl image is finite by
  the published `splitTorusWeylImageFinite`.
- `weylAction_oppositeFactorPair_eq`: the pair product acts on characters by
  `χ ↦ χ - ⟨χ, l^∨⟩ • P.root l`.
- `piece_conj_eq_commutator_p`: for `X ∈ U_p` nontrivial with pair product `μ` and
  `Z ∈ U_q`, `μ Z μ⁻¹ = [X, Z]`, an element of `U_m`.
- `piece_conj_eq_commutator_neg_m`: for `Y ∈ U_{-m}` nontrivial with pair product `μ` and
  `Z ∈ U_q`, `μ Z μ⁻¹ = [Y, Z]`, an element of `U_{-p}`. The index of `-m` is
  `P.reflectionPerm lm lm`, with coroot `-m^∨`.
- `piece_val_commutator` (**exact commutator values**): let `D` be a normalizer-stable
  apartment class of `j` (with `G` connected reductive and `j` a maximal split torus) and `x`
  an apartment point. For `X ∈ U_p` nontrivial and `Z ∈ U_q`,
  `x_m([X, Z]) = x_q(Z) + x_p(X)`. Proof: the reflection–commutator identity and the
  reflection formula with `⟨q, p^∨⟩ = -1`.

## Provenance

The structure of roots over a multipliable relative root of a quasi-split group is
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §2.6, Notation 2.6.11 and the
paragraphs after it (printed pp. 96–97, PDF pp. 127–128). For `ã` over `a`, there is a unique
other root `ã'` over `a` not orthogonal to `ã`, and `ã + ã'` is a root over `2a`. The group
`U_a` is the restriction of scalars of `U_ã U_ã' U_{ã+ã'}`, a group of `SU₃` type
(Construction 2.9.16). The Lean statements are internal. They derive this combinatorics from
the reflection bound, which uses only that the roots over the line of `a` restrict to `±a`
and `±2a`. The reflection–commutator identity and the exact commutator values replace the
explicit `SU₃` formulas of Kaletha–Prasad §2.7 and §3.2. They are derived from the published
opposite-factor-pair, semigroup-commutator and apartment-rigidity results of the Library.

## Scope

This unit proves no axiom of the descended family by itself. It is used by the later units
of task 8ffe0456 for V 5 at multipliable roots.
