# Positive multiples of dominant characters are realized

Worker 1161. This module proves the positive-multiple step of actual dominant
highest-weight existence for split connected reductive groups. It is internal and
derived; the mathematical background is Milne, *Algebraic Groups* (2017),
Chapter 22, especially Theorem 22.20 and Lemmas 22.24–22.26 (printed pp.468–470,
PDF pp.484–486). Milne's route uses parabolic subgroups containing root groups,
Chevalley's theorem and an isogeny to a simply connected group times a torus.
That route is replaced here by dynamic parabolics, top weight lines of a faithful
representation, the Weyl representatives supplied by `IsRootDatumOf`, and integral
linear algebra. No simple connectedness or coroot-span hypothesis is used.

## Statement

`Langlands.GroupScheme.DominantMultiple.exists_pos_nsmul_mem_realizedSet` takes:

- a field `k`;
- an actual group scheme `G` over `Spec k` with affine structure morphism;
- a split pinning `p : SplitPinning G`;
- a cocharacter `nu` of the pinned torus pairing positively with every simple root;
- `i : H → G` representing the dynamic parabolic of the opposite of
  `nu ≫ p.inclusion`, with `H` affine over the base;
- `tH` with `tH ≫ i = p.inclusion`;
- `j : U → G` with range in the dynamic unipotent subgroup of `nu ≫ p.inclusion`,
  with `U` unipotent;
- a character `lam` with nonnegative pairing against every simple coroot.

It proves that some `n > 0` has `n • lam ∈ realizedSet tH i j`. In other words,
there are a rational character `χ` of `H` restricting to `n • lam` and a coordinate
`f` of `G` with three properties: `f` is left covariant along `i` for `χ`, `f` is
right invariant along `j` on every test scheme, and `f` has counit one.

## Proof as implemented

Write `P` for the supplied root datum, `b` for its base and `S` for
`realizedSet tH i j`, an additive submonoid.

1. **Simple directions.** For each simple root `c`, `exists_simple_dual` gives `ν`
   in the integral coroot span pairing positively with `c` and trivially with
   the other simple roots. So `ν` is dominant, and it pairs nontrivially with the
   root `c`. `exists_mem_realizedSet_pos` gives `x ∈ S` with `⟨x, ν⟩ > 0`,
   orthogonal to the simple coroots of the roots orthogonal to `ν`, that is all
   simple roots other than `c`. `pairing_simple_coroot_pos` then shows
   `⟨x, c^∨⟩ > 0`.
2. **Central directions.** Let `A` be the additive subgroup of characters `y` with
   `y ∈ S`, `-y ∈ S` and `y` orthogonal to every coroot. Let `L` be its integral
   span plus the integral root span. Suppose a cocharacter `n` is orthogonal to
   `L`. Then `n` is orthogonal to all roots. If `n ≠ 0`, the perfect pairing gives
   a character pairing nontrivially with `n`, and
   `exists_neg_mem_realizedSet_of_central` gives an element of `A` pairing
   positively with `n`, a contradiction. The character lattice of the split torus
   is finitely generated (`IsSplitTorus.finite_characterLattice`), so
   `exists_pos_nsmul_mem_of_orthogonal` gives every character a positive multiple
   in `L`. If `x` is orthogonal to the simple coroots and `m • x = a + r` with
   `a ∈ A` and `r` in the root span, then `r` is orthogonal to the simple coroots.
   Hence `r = 0` (`eq_zero_of_mem_rootSpan`), and `m • x = a ∈ S`.
3. **Combination.** `exists_pos_nsmul_mem_of_dominant` combines the simple
   directions with the central multiples to put a positive multiple of `lam` in
   `S`.

The result is intended to be combined with the separate saturation step and the
big-cell glue of the dominant highest-weight existence task. It does not by itself
construct an irreducible representation.
