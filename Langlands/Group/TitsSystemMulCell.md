# The Tits multiplication axiom from a rank-one factorization

This module is pure group theory. It derives the multiplication axiom `mul_mem_cell` of
`Langlands.Group.IsTitsSystem` for one element `s` from a factorization of `B` adapted to `s`.
It does not assume a Tits system. It supports the proof task for
`Langlands.GroupScheme.RelativeTitsSystemStatement`, where the hypotheses below are rank-one
statements about root subgroups. Those statements are not proved here. The module adds no
axioms.

## Setting

`G` and `W` are groups, `B` and `N` are subgroups of `G`, and `π : N →* W`. The cell
`Langlands.Group.TitsSystem.cell B π w` is the set of products `b * n * b'` with `b, b' ∈ B`,
`n ∈ N` and `π n = w`. A *representative* of `w` is an `n : N` with `π n = w`. The module also
uses the unconditional lemmas `mem_cell_of_eq` and `mul_mem_cell_left` of
`Langlands.Group.TitsSystemBruhat`: a representative of `w` lies in the cell of `w`, and the
cells are stable under left multiplication by `B`.

The data attached to `s ∈ W` are two subsets `B'` and `U` of `G` and a subset `P` of `W`. The
hypotheses are:

- `hBU`: every `b ∈ B` is a product `b' * u` with `b' ∈ B'` and `u ∈ U`;
- `hB'`: every representative `n` of `s` satisfies `n * b' * n⁻¹ ∈ B` for `b' ∈ B'`;
- `hU`: every representative `n` of `s` satisfies `n * u * n⁻¹ ∈ B ∪ cell B π s` for `u ∈ U`;
- `hP`: for `w ∈ P`, every representative `m` of `w` satisfies `m⁻¹ * u * m ∈ B` for `u ∈ U`;
- `hcover`: every `w ∈ W` satisfies `w ∈ P` or `s * w ∈ P`;
- `hs`: `s * s = 1`.

## Results

- `mul_mem_cell_of_conj_mem` (uses `hBU`, `hB'`): if `n` represents `s`, `m ∈ N` satisfies
  `m⁻¹ * u * m ∈ B` for all `u ∈ U`, and `b ∈ B`, then `n * b * m ∈ cell B π (s * π m)`.
  Proof: write `b = b' * u`. Then
  `n * b * m = (n * b' * n⁻¹) * (n * m) * (m⁻¹ * u * m)`, an identity checked by the `group`
  tactic. The outer factors lie in `B`, and `π (n * m) = s * π m`.

- `mul_mem_cell_of_rankOne` (all six hypotheses): for every representative `n` of `s`, every
  `m ∈ N` and every `b ∈ B`,
  `n * b * m ∈ cell B π (π m) ∪ cell B π (s * π m)`.
  Proof: by `hcover`, `π m ∈ P` or `s * π m ∈ P`.
  - If `π m ∈ P`, then `hP` applies to `m` and the previous result puts `n * b * m` in the
    second cell.
  - If `s * π m ∈ P`, write `b = b' * u` and
    `n * b * m = (n * b' * n⁻¹) * (n * u * n⁻¹) * (n * m)`. By `hU`, the middle factor lies in
    `B` or in `cell B π s`.
    - In the first case the product is an element of `B` times the representative `n * m` of
      `s * π m`, so it lies in the second cell.
    - In the second case write `n * u * n⁻¹ = c * n' * c'` with `c, c' ∈ B` and `n'` a
      representative of `s`. The element `n * m` represents `s * π m ∈ P`, so `hP` applies to
      it. The previous result for `n'`, `c'` and `n * m` gives
      `n' * c' * (n * m) ∈ cell B π (s * (s * π m))`, which is `cell B π (π m)` because
      `s * s = 1`. Left multiplication by `(n * b' * n⁻¹) * c ∈ B` puts `n * b * m` in the
      first cell.

- `forall_mul_mem_cell_of_rankOne`: for a set `S ⊆ W` of elements with `s * s = 1`, if every
  `s ∈ S` has data `B'`, `U`, `P` satisfying `hBU`, `hB'`, `hU`, `hP` and `hcover`, then the
  conclusion of `mul_mem_cell_of_rankOne` holds for all `s ∈ S`. This is literally the field
  `mul_mem_cell` of `IsTitsSystem B N π S`.

## Provenance

The results are internal. The argument is the group-theoretic part of the proof of Borel–Tits,
*Groupes réductifs* (1965), Proposition 5.16 (i) (printed p. 101), checked against the scan in
the central library. There `B = P_∅(k)` and `r = r_a` for a simple `k`-root `a`. Borel and Tits
write `U = V_a ⋊ U_(a)` over `k`, where `V_a` is the unipotent radical of the standard
parabolic subgroup attached to `{a}`. Then `r P(k) = Z(S)(k) V_a(k) r U_(a)(k)`. They apply the
Bruhat decomposition 5.15 to the rank-one group `Z(S_a)` and use `w⁻¹(a) > 0`, after replacing
`w` by `r w` if necessary. In the notation of this module the data are:

- `U = U_(a)(k)`;
- `B' = Z(S)(k) V_a(k)`, which every representative of `r_a` normalizes;
- `P = {w | w⁻¹(a) > 0}`.

Then `hU` is a consequence of the rank-one Bruhat decomposition of `Z(S_a)(k)`, which contains
`n U_(a)(k) n⁻¹`. The hypothesis `hcover` holds because `(r_a w)⁻¹(a) = -w⁻¹(a)`. The Lean proof
splits on `hcover` directly instead of replacing `w` by `r w`. Lean proves only the abstract
implication. The factorization, the conjugation properties and the rank-one decomposition for an
actual reductive group are not proved here.
