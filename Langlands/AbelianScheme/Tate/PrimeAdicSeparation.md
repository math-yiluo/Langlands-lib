# Torsion-freeness of prime-adic Tate modules and rational separation

This helper module collects algebraic facts about the Library's actual
prime-adic Tate modules `Langlands.GroupScheme.Tate.PrimeAdic.Integral G T p`
and the actual integral roots-of-unity twist `Langlands.TateTwist.Integral R p`.
It also proves a transfer of separation from integral to rationalized pairings.
The reduction of rational prime-adic polarization Weil nondegeneracy uses all of
them. Throughout, `p` is a prime (`Fact p.Prime`). Nothing here refers to Weil
pairings.

The Tate module construction itself is the inverse limit of torsion points
under multiplication by `p`, as in Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), Chapter X, (10.8),
printed p.144. The facts below are standard consequences of that construction:
Tate modules have no `p`-torsion, and separation over `ℤ_p` with torsion-free
values passes to `ℚ_p`. They are not quoted from a source. The proofs are
internal.

## Module algebra over `ℤ_[p]` (namespace `Langlands.PrimeAdicSeparation`)

- `eq_zero_of_smul_eq_zero`. Let `M` be a `ℤ_[p]`-module in which `p • x = 0`
  forces `x = 0`. Then `c • x = 0` with `c ≠ 0` forces `x = 0`. Proof: write
  `c = u * p ^ v` with `u` a unit (`PadicInt.unitCoeff_spec`). Multiplying by
  `u⁻¹` gives `p ^ v • x = 0`, and induction on `v` gives `x = 0`.
- `eq_zero_of_one_tmul_eq_zero`. For such a module `W`, `1 ⊗ w = 0` in
  `ℚ_[p] ⊗[ℤ_[p]] W` implies `w = 0`. The map `w ↦ 1 ⊗ w` is a localization at
  the non-zero-divisors of `ℤ_[p]`: combine `TensorProduct.isBaseChange` with
  `isLocalizedModule_iff_isBaseChange`. By `IsLocalizedModule.eq_zero_iff`,
  some nonzero `c` has `c • w = 0`, and the previous lemma applies.
- `exists_smul_eq_one_tmul`. Every `X : ℚ_[p] ⊗[ℤ_[p]] M` has a nonzero
  `c : ℤ_[p]` and an `x : M` with `c • X = 1 ⊗ x`. This follows from
  `IsLocalizedModule.mk'_surjective` and `IsLocalizedModule.mk'_cancel'` for
  the same localization.
- `eq_zero_of_smul_eq_zero_rational`. If `c ≠ 0` and `c • X = 0` in a
  `ℚ_[p]`-vector space of the form `ℚ_[p] ⊗[ℤ_[p]] M`, then `X = 0`: the scalar
  action of `c` agrees with that of its image `(c : ℚ_[p]) ≠ 0`.
- `separatingLeft_of_tmul` and `separatingRight_of_tmul`. Let `b : M → N → W`
  be any function and `B` a `ℚ_[p]`-bilinear map on the rationalizations with
  `B (q ⊗ x) (r ⊗ y) = (q * r) ⊗ b x y`. Assume `W` has no `p`-torsion. If `b`
  is left-separating, meaning that `b x y = 0` for all `y` forces `x = 0`, then
  `B.SeparatingLeft` holds; similarly on the right. Proof: let `X` pair to zero
  with everything and choose `c • X = 1 ⊗ x`. For each `y`,
  `1 ⊗ b x y = B (c • X) (1 ⊗ y) = c • 0 = 0`, so `b x y = 0`. Hence `x = 0`,
  so `c • X = 0`, and then `X = 0`.

## Prime-adic Tate modules of group schemes (namespace `Langlands.GroupScheme.Tate.PrimeAdic`)

Here `G` is a commutative group object in `Over S` and `T : Over S`. The level
`Level G T m` is the additive copy of the subgroup of points `T ⟶ G.X` killed by
`m`. An element of `Integral G T p` is a family of level-`p ^ n` points, one for
each `n`, such that the `p`-th power of coordinate `n + 1` is coordinate `n`.

- `evaluation_natCast_smul`. A natural-number scalar acts on each coordinate by
  `nsmul`.
- `eq_zero_of_prime_smul_eq_zero`. `Integral G T p` has no `p`-torsion. If
  `p • x = 0`, then coordinate `n + 1` satisfies `p • x_(n+1) = 0`. The
  transition from level `p ^ (n+1)` to level `p ^ n` is multiplication by `p`
  on the underlying points (`toSection_transition_succ`). It sends `x_(n+1)`
  to `x_n`, so `x_n = 0` (`toSection_injective`).
- `evaluation_surjective`. If every transition from level `p ^ (n+1)` to level
  `p ^ n` is surjective, then every coordinate projection
  `evaluation G T p n` is surjective. Given `y` at level `n`, choose successive
  preimages `w k` at level `n + k` by recursion. The coherent family has
  coordinate `m` equal to the transition of `w m` from level `n + m` down to
  level `m`. Coherence and the value at `n` follow from `transition_comp` and
  `transition_self`.
- `transition_succ_surjective_of_pow`. If every point `T ⟶ G.X` has a `p`-th
  root, every such transition is surjective. If `y` is killed by `p ^ n` and
  `x ^ p = y`, then `x` is killed by `p ^ (n+1)`, and the transition sends it
  to `x ^ p = y`.
- `evaluation_surjective_of_pow`. The combination of the two previous lemmas.
- `exists_map_eq_natCast_smul`. Let `f : G ⟶ H` and `ψ` be a homomorphism of
  point groups with `ψ y ≫ f.hom.hom = y ^ N`. Then for every `z` in
  `Integral H T p` there is `y` in `Integral G T p` with `map T p f y = N • z`.
  Apply `ψ` coordinatewise. It is a homomorphism, so it preserves the level
  subgroups and commutes with the transitions, which are powers. The resulting
  coherent family maps to `N • z`.
- `eq_zero_of_map_eq_zero`. If `0 < N` and every point killed by `f` satisfies
  `x ^ N = 1`, then `map T p f` is injective. If `map T p f y = 0`, each
  coordinate of `y` is killed by `f`, so `N • y = 0`. By torsion-freeness and
  `eq_zero_of_smul_eq_zero` with `c = N ≠ 0`, `y = 0`.

## The roots-of-unity twist (namespace `Langlands.TateTwist`)

- `evaluation_natCast_smul` and `eq_zero_of_prime_smul_eq_zero`. These are the
  same two facts for `Integral R p` over a commutative ring `R`, with coordinates
  in the `p ^ n`-th roots of unity of `R`. The transition is again the
  `p`-th power (`toUnit_transition_succ`), and `toUnit_injective` replaces
  `toSection_injective`.

The module adds no hypotheses beyond those displayed. Its proofs use only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.
