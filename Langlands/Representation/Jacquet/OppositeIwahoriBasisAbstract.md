# Opposite Iwahori bases from one contracting central element

Worker 1045 wrote this module and this explanation. It is an internal,
purely topological-group construction used by the proof of
`Langlands.Aubert.General.RationalPointFamily.RationalOppositeIwahoriBasisStatement`.
No algebraic geometry is involved.

## Main result

`Langlands.Jacquet.hasOppositeIwahoriContractionBasis_of_contraction` works in
a group `Γ` with a topology for which `Γ` is a locally compact
`NonarchimedeanGroup`. It takes three subgroups `U`, `M`, `O` and an element
`g`, and assumes:

- `O` and `U` are closed;
- `g ∈ M`, and `g` commutes with every element of `M`;
- `M` normalizes `O` and `U`;
- uniqueness of factorization: `o * m * u = o' * m' * u'` with `o, o' ∈ O`,
  `m, m' ∈ M`, `u, u' ∈ U` forces `o = o'`, `m = m'` and `u = u'`;
- the open cell condition: for any three identity neighborhoods `A`, `B`,
  `C`, the set of products `a * b * c` with `a ∈ A ∩ O`, `b ∈ B ∩ M` and
  `c ∈ C ∩ U` is an identity neighborhood;
- uniform contraction of `U` by `g`: for every compact `C ⊆ U` and every
  identity neighborhood `W`, eventually in `n` every `g ^ n * c * (g ^ n)⁻¹`
  with `c ∈ C` lies in `W`;
- the same for `O` with conjugation `(g ^ n)⁻¹ * c * g ^ n`.

It concludes `Jacquet.HasOppositeIwahoriContractionBasis U M O g`: every
open set containing `1` contains a compact open subgroup `K` satisfying both
`IsIwahoriContraction K U M O g` and `IsIwahoriContraction K O M U g⁻¹`. The
same `g` serves every `K`.

## Auxiliary results

- `conj_conj_of_commute`: if `a` and `b` commute, conjugation by `a` and
  conjugation by `b` commute. This is a group identity.
- `exists_isCompact_openSubgroup_subset`: in a locally compact
  nonarchimedean group, every identity neighborhood `W` contains a compact
  open subgroup. Mathlib's `local_compact_nhds` gives a compact neighborhood
  inside `W`. `NonarchimedeanGroup.is_nonarchimedean` gives an open subgroup
  inside that neighborhood. An open subgroup is closed, so it is compact.
- `eventually_forall_conj_mem`: for compact `S` and an identity
  neighborhood `Q`, all `y` near `1` satisfy `s * y * s⁻¹ ∈ Q` for every
  `s ∈ S`. This follows from continuity of `(y, s) ↦ s * y * s⁻¹` and
  `IsCompact.eventually_forall_of_forall_eventually`.
- `exists_stable_piece`: let `V` be a compact open subgroup, `H` a closed
  subgroup normalized by a subgroup `M`, and let `h ∈ M` commute with `M`
  and contract compact subsets of `H` uniformly. Set
  `P = {x ∈ H | h ^ k * x * (h ^ k)⁻¹ ∈ V for every k ≥ 0}`. Then:
  - `P` is a subgroup of `H` contained in `V`;
  - `P` is closed, as an intersection of `H` with preimages of `V` under
    continuous conjugations, hence compact;
  - conjugation by `h` maps `P` into itself (shift the exponent);
  - conjugation by every `b ∈ V ∩ M` maps `P` into itself
    (`conj_conj_of_commute`, `b ∈ V`);
  - there is an identity neighborhood `Y` with `H ∩ Y ⊆ P`. By uniform
    contraction of the compact set `V ∩ H` into `V`, there is `N` such
    that `h ^ k * c * (h ^ k)⁻¹ ∈ V` for all `k ≥ N` and `c ∈ V ∩ H`.
    Take `Y` to be the finite intersection of the conditions for `k ≤ N`.

## Proof of the main result

Fix an open `W ∋ 1` and a compact open subgroup `V ⊆ W`.
`exists_stable_piece` applied to `O` with `h = g⁻¹` gives `A0`, with
neighborhood `YA`. Applied to `U` with `h = g` it gives `C0`, with
neighborhood `YC`. Let `B0 = V ∩ M`. By the open cell condition (with `YA`,
`V`, `YC`), the set `Z = A0 * B0 * C0` of triple products is an identity
neighborhood. Choose an open subgroup `Q ⊆ Z`.

`eventually_forall_conj_mem` and the two contraction hypotheses give one
exponent `n` with two properties. Conjugation by `g ^ n` carries every
`c ∈ C0` to an element `y` with `s * y * s⁻¹ ∈ Q` for all `s ∈ A0`.
Conjugation by `(g ^ n)⁻¹` carries every `a ∈ A0` to an element `y` with
`y⁻¹ ∈ Q` and `s * y * s⁻¹ ∈ Q` for all `s ∈ C0`. Let `A` be the subgroup of
`x` with `g ^ n * x * (g ^ n)⁻¹ ∈ A0`. Then:

- `A ⊆ A0 ⊆ O`, because `A0` is stable under conjugation by powers of `g⁻¹`;
- `A` is stable under conjugation by `g⁻¹` and normalized by `B0`;
- `O ∩ Y' ⊆ A` for an identity neighborhood `Y'`, the preimage of `YA` under
  conjugation by `g ^ n`.

The key step `hswap` shows `C0 * A ⊆ A * B0 * C0`. Let `c ∈ C0` and
`a ∈ A`, and put `ã = g ^ n * a * (g ^ n)⁻¹ ∈ A0`. By the second property
of `n`, `a⁻¹` and `c * a * c⁻¹` lie in `Q`. Hence `a⁻¹ * (c * a * c⁻¹) ∈ Q ⊆ Z`,
so this element equals `o1 * m1 * u1` with factors in `A0`, `B0`, `C0`. By
the first property of `n` with `s = ã⁻¹`, the conjugate of `a⁻¹ * c * a` by
`g ^ n` lies in `Q ⊆ Z`. It therefore equals `o2 * m2 * u2` with factors in
`A0`, `B0`, `C0`. Substituting the first factorization, the same conjugate
equals the product of the conjugates of `o1`, `m1` and `u1 * c` by `g ^ n`.
These factors lie in `O`, `M` and `U`, since `M` normalizes `O` and `U`.
Uniqueness of factorization then gives
`g ^ n * o1 * (g ^ n)⁻¹ = o2 ∈ A0`, that is, `o1 ∈ A`. Hence
`c * a = (a * o1) * m1 * (u1 * c)`.

From `hswap` and the `B0`-normalization of `A` and `C0`, the set
`K = A * B0 * C0` is closed under multiplication and inversion, so it is a
subgroup. The open cell condition (with `Y'`, `V`, `YC`) shows that `K` is
an identity neighborhood, so `K` is open. Also `K ⊆ V`, so `K` is closed in
the compact `V` and therefore compact, and `K ⊆ W`. Uniqueness of
factorization gives `K ∩ U = C0` and `K ∩ O = A`.

The fields of `IsIwahoriContraction K U M O g` follow:

- `mem_levi`: `g ∈ M`;
- `factor`: `K = A * B0 * C0`;
- `upper` and `lower`: stability of `C0` under conjugation by `g` and of `A`
  under conjugation by `g⁻¹`;
- `levi`: centrality of `g` in `M`;
- `exhaust`: contraction of the singleton `{x}` into `YC`, whose
  intersection with `U` lies in `C0`;
- `contract`: uniform contraction of the compact `A0 ⊇ K ∩ O` into each
  open subgroup.

For `IsIwahoriContraction K O M U g⁻¹`, the factorization in the order
`U * M * O` comes from factoring `k⁻¹` and inverting. Exhaustion uses
contraction of singletons of `O` into `Y'`. Uniform contraction uses the
compact `C0 = K ∩ U`. The other fields are as before.

## Provenance

This route is an internal derivation for this project. Bill Casselman,
*Introduction to admissible representations of p-adic groups*, Chapter III
(registered as `casselman-2019-jacquet-module`), Section III.4, treats
compact open subgroups with Iwahori factorization for reductive groups as
background. The present module does not follow that text. It uses only the
listed abstract hypotheses, and it does not use Willis's theory of tidy
subgroups.
