# Parabolic double cosets across components

This internal algebraic module extends the parabolic double-coset construction
of `Langlands.Group.TitsSystemBruhat` to an ambient group larger than the group
of the Tits system. It constructs an equivalence on the full ambient group and
specifies its value on every normalizer representative. It supplies no geometric
Tits-system or facet comparison theorem.

The groups `G : Type u` and `W : Type v` have independent universes. The data are
subgroups `B`, `N`, `K` of `G`, a subgroup `W₀` of `W`, and homomorphisms
`π : N →* W` and `π₀ : N.subgroupOf K →* W₀`. Here `N.subgroupOf K` is the
intersection of `N` with `K`, viewed inside `K`. The assumptions are:

- `eB : W ≃ DoubleCoset.Quotient (B : Set G) B`, with
  `eB (π n) = DoubleCoset.mk B B (n : G)` for every `n : N`;
- `B ≤ K` and a Tits system
  `IsTitsSystem (B.subgroupOf K) (N.subgroupOf K) π₀ S`;
- compatibility `(π₀ n : W) = π ⟨((n : K) : G), n.property⟩`
  for every `n : N.subgroupOf K`;
- for every `g : G`, a representative `r : N` such that
  `g * (r : G)⁻¹ ∈ K` and `(r : G) ∈ Subgroup.normalizer (B : Set G)`;
- surjectivity of the full projection `π`.

The representative condition is an explicit assertion about all of `G`.
It is fulfilled by representatives of every component when `K` is the kernel
of a component homomorphism. The module does not assume that `K` or `W₀` is
normal and does not use a quotient group of either. It does not ask `S` to
generate the full group `W`: it generates `W₀` through the subgroup Tits system.

For `X Y : Set W₀` with `X ⊆ S` and `Y ⊆ S`, let
`V = (Subgroup.closure X).map W₀.subtype` and
`V' = (Subgroup.closure Y).map W₀.subtype`. Let `P`, `Q` be actual subgroups
of the full `G` whose underlying sets are respectively
`standardParabolic B π (W₀.subtype '' X)` and
`standardParabolic B π (W₀.subtype '' Y)`. Thus the assertion about `P` is exactly

```text
g ∈ P ↔ ∃ w ∈ closure (W₀.subtype '' X), g ∈ cell B π w.
```

These are supplied comparisons, not definitions of arbitrary parahorics.
`exists_subgroup_parabolic_doubleCoset_equiv` proves the existence of

```text
e : DoubleCoset.Quotient (V : Set W) V' ≃
      DoubleCoset.Quotient (P : Set G) Q
∀ n : N, e (DoubleCoset.mk V V' (π n)) = DoubleCoset.mk P Q (n : G).
```

`subgroupParabolicDoubleCosetEquiv` selects such an equivalence by classical
choice. `subgroupParabolicDoubleCosetEquiv_apply` supplies its displayed formula.
The codomains retain all of `G` and the domain retains all of `W`.

The supporting declarations implement the following proof.

- `equiv_eq_doubleCoset_of_mem_cell` identifies `eB w` with the actual
  `B` double coset of any point in `cell B π w`.
  `index_eq_of_mem_cell` then gives uniqueness of full cell indices.
- `coe_mem_cell_of_mem_subgroup_cell` uses projection compatibility to
  include a subgroup cell in its full cell.
  `exists_subgroup_cell_of_mem_cell` proves the converse for indices in `W₀`:
  choose a subgroup normalizer representative using the subgroup Tits system,
  and compare its full `B` double coset using `eB`. Containment `B ≤ K`
  puts both factors inside `K`.
- `mul_normalizing_rep_mem_cell` transports the full cell `C(w)` to
  `C(w * π r)` by multiplying on the right by `r`. The right `B` factor
  becomes `r⁻¹ * b * r`, which is in `B` by the normalizer hypothesis.
- `exists_subgroup_mul_mem_cell` proves that a point of `C(u)` for
  `u ∈ closure X` sends any full cell `C(v)` into some `C(u' * v)`,
  with `u' ∈ closure X`. Remove a normalizing representative `r`
  from the second point, apply the existing `IsTitsSystem.exists_mul_mem_cell`
  inside `K`, and restore `r`. Full cell uniqueness identifies the index of
  the restored second point with `v`.
  `exists_subgroup_mul_mem_cell_right` follows by inversion.
- `coe_eq_standardParabolic_of_subgroup` is an adapter for actual subgroups.
  Given `P ≤ K` and equality between the carrier of `P.subgroupOf K`
  and the subgroup standard parabolic, it proves the required full carrier
  comparison. The subgroup-cell comparisons and
  `MonoidHom.map_closure` identify the two unions. This adapter does not need
  the normalizing representative condition.

The quotient construction follows the existing generic parabolic proof.
Surjectivity of `π` chooses normalizer representatives for elements of `W`.
The formula for `eB` makes choices independent in every larger `P,Q` double
coset. Representatives of `V,V'` belong to `P,Q` by their carrier comparisons,
so the map descends to the double quotient. For injectivity, express the two
parabolic factors as cells, use the left and right cell actions just proved,
and apply full cell uniqueness. For surjectivity, first represent the full
`B` double coset of an arbitrary `g` using `eB`, then enlarge both sides to
`P` and `Q`.

The source context is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered source `kaletha-prasad-2023-bruhat-tits-new-approach`,
Proposition 7.5.5 (printed 261–262, PDF 292–293) and
Theorem 7.8.1(2),(3) (printed 272–273, PDF 303–304).
The latter derives the parahoric bijection from the Iwahori bijection and
the facet-parabolic comparison. The authors' *Corrections and additions*,
1 November 2024, registered source `kaletha-prasad-2024-corrections`,
PDF 35, replaces the insufficient printed injectivity proof for the Iwahori
bijection. Here that full Iwahori-type equivalence is supplied as `eB`;
the module does not repeat or rely on the insufficient argument.

The abstraction to arbitrary subgroups, the compatible projection interface,
the independent universes and the carrier adapter are derived internal content.
To apply this construction to `ParahoricDoubleCosetStatement`, one must still
prove the actual Iwahori equivalence, actual subgroup Tits-system realization,
normalizing component representatives and the actual facet-parabolic comparisons
from that statement's unchanged apartment and common-chamber hypotheses.
None of those is a new premise of either global building target.
