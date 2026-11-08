# Noncommuting root subgroups of a split reductive group

Let `G` be a connected reductive group over a field `k`, with a split maximal torus
`i : T → G` and a root datum `P` of `(G, T)`. Let `β = P.root r` and `β' = P.root r'` be two
roots with `⟨β, β'^∨⟩ = -1`, and suppose no strict combination `n β - m β'` (`n, m > 0`) is
zero or a root. The main theorem `exists_not_commute` says that the root subgroups
`U_β` and `U_β'` do not commute over every test scheme `Z` that has a global function `c ≠ 0`
with `1 + c` a unit. Over a field `Z = Spec L`, any `c ∉ {0, -1}` works.

The intended use is a multipliable relative root `a` of a quasi-split group. There, `β` and
its orbit partner `β'` both restrict to `a`, and `⟨β, β'^∨⟩ = -1` (the module
`Langlands.GroupScheme.Reductive.RootDatumOrbitPartners`). The lemma
`strict_combination_not_root` supplies the hypothesis on strict combinations from the
absence of relative roots `n a` with `n ≥ 3`. The passage from the absolute root subgroups to
the relative root group `U_a` is not made in this module.

Provenance: internal. The statement is the standard fact that root subgroups of an obtuse
pair of roots do not commute (in `SL₃`, `[x_β(s), x_β'(t)] = x_{β+β'}(±st)`). The proof
below avoids the Chevalley commutator formula and uses only the rank-one relation and the
weight-semigroup commutator theorem of the Library.

All declarations live in namespace `Langlands.GroupScheme.RootPairNoncommutation`.

## Definition

- `NotCommuteOver F F' Z`, for subgroup functors `F` and `F'` of a `k`-group scheme `G` and
  a test scheme `Z` over `Spec k`: some `Z`-point of `F` does not commute with some
  `Z`-point of `F'`. That is, `∃ x ∈ F.carrier Z, ∃ y ∈ F'.carrier Z, ¬ Commute x y`.

## Commutation from the absence of strict combinations

- `commute_of_no_strict_combinations hS i c d hc hd hcd hx hy`. Here `G` is smooth and affine
  over `k`, `S` is a split torus, `i : S → G` is any homomorphism, and `c, d` are nonzero
  characters of `S`. Suppose no `n • c + m • d` with `n, m > 0` is zero or a root of
  `roots i`. Then every `Z`-point of `RelativeRoot.subgroup i c` commutes with every `Z`-point
  of `RelativeRoot.subgroup i d`.

  Proof. This is the proof of the Library lemma
  `SplitPinning.commute_of_no_strict_root_combinations`
  (`Langlands.GroupScheme.Rational.OrthogonalSimpleRootCommutation`), with the pinned torus
  replaced by an arbitrary split torus `S` and homomorphism `i`. The root subgroup of a
  nonzero character `c` is the first step of its cyclic weight filtration
  (`RelativeRoot.weightFiltration_one_eq_subgroup`). By the semigroup commutator theorem
  `RelativeRoot.semigroupCommutator`, the commutator `x y x⁻¹ y⁻¹` lies in the subgroup of the
  sum semigroup `{n c + m d : n, m > 0}`. That subgroup is trivial: by
  `RelativeRoot.semigroupSubgroup_eq_bot_of_noAmbientWeights_without_realization` it is enough
  that no element of the semigroup is a weight of the conjugation action, and a nonzero weight
  of conjugation is a root (`RelativeRoot.mem_actionWeightSupport_conjugation_iff`).

## Lattice lemmas

These hold for any root pairing `P : RootPairing J ℤ X Y`.

- `reflection_strict_combination P h n m`: if `⟨β, β'^∨⟩ = -1`, the reflection in `β'` sends
  `n β - m β'` to `n β + (n + m) β'`. Proof: linearity of the reflection, with
  `s_{β'}(β) = β + β'` and `s_{β'}(β') = -β'`.
- `pairing_strict_combination P h n m`: under the same hypothesis,
  `⟨n β - m β', β'^∨⟩ = -(n + 2m)`.
- `strict_combination_not_root P f a hr hr' h hhigh n m hn hm`. Let `f : X →+ M` be an
  additive map with `f β = f β' = a`, let `⟨β, β'^∨⟩ = -1`, and suppose no root `s` has
  `f s = n • a` with `n ≥ 3` (hypothesis `hhigh`). Then for `n, m > 0` the combination
  `n β - m β'` is neither zero nor a root.

  Proof. If it were zero, its pairing with `β'^∨` would vanish, but that pairing is
  `-(n + 2m) < 0`. If it were a root `s`, the reflection of `s` in `β'` would be the root
  `n β + (n + m) β'`. Its image under `f` is `(2n + m) • a` with `2n + m ≥ 3`, which
  contradicts `hhigh`.

In the intended use, `f` is restriction of characters from the absolute maximal torus to the
maximal split torus, and `hhigh` says that `n a` is not a relative root for `n ≥ 3`.

## Character values on cocharacter points

- `cu_cocharacter χ ν u`: at the point `ν(u)` of a cocharacter `ν`, the character `χ` takes
  the value `u ^ ⟨χ, ν⟩`. Here `cu` is `RankOneRootCellRelation.cu`. Proof: the composite
  `χ ∘ ν` is the endomorphism `u ↦ u ^ ⟨χ, ν⟩` of `𝔾_m` (`eq_gmEndEquiv_zsmul`,
  `gmEndEquiv_symm_comp`, `latticePairing_apply`).

## Root data of reductive groups

- `mem_of_isRepresentedBy hf y`: if `f : H → G` represents the subgroup functor `F`, then
  `y ≫ f` is a point of `F` for every point `y` of `H`.
- `isReduced hG hT hi hP`: the root datum of a split maximal torus of a connected reductive
  group is reduced. This is the Library theorem `rootReducedness`, restated for `P`.
- `hasNoHigherRoots hG hT hi hP r`: no multiple `n • β` with `n ≥ 2` of a root `β` is a root
  (`RelativeRoot.HasNoHigherRoots`). Proof: reducedness and Mathlib's
  `RootPairing.nsmul_notMem_range_root`. The character lattice of a split torus is torsion
  free because its rationalization is injective (`IsSplitTorus.character_toRat_injective`).

## Main theorem

- `exists_not_commute hG hT hi hP hpair hstrict c hc hu`. The hypotheses are: `G` is
  connected reductive (`hG`), `i : T → G` is a split maximal torus (`hT`, `hi`), `P` is a
  root datum of `i` (`hP`), `P.pairing r r' = -1` (`hpair`), and no strict combination
  `n β - m β'` is zero or in `roots i` (`hstrict`). Let `c` be a global function on `Z` with
  `c ≠ 0` and `1 + c` a unit. Then
  `NotCommuteOver (RelativeRoot.subgroup i β) (RelativeRoot.subgroup i β') Z`. The witness is
  `x = x_β(1)`.

  Proof. Take monic root maps `x_β`, `x_{β'}` and `x_{-β'}` with the rank-one relation for
  `β'`, from the Library theorem `exists_monic_rootRankOneRelations`. They represent the root
  subgroups (`VectorGroup.IsTorusEquivariant.represents_root`, using `hasNoHigherRoots`).
  Suppose `x` commutes with every point of `U_β'`.

  1. `x` also commutes with every point of `U_{-β'}`. This is
     `commute_of_no_strict_combinations` for the characters `β` and `-β'`, by `hstrict`.
  2. Let `v = 1 + c`. The rank-one relation over `Z` at `X = 1` and `Y = c` reads
     `x_{β'}(1) x_{-β'}(c) = x_{-β'}(v⁻¹ c) β'^∨(v) x_{β'}(v⁻¹)`. Solving for the middle factor
     (`solve_middle`) writes `β'^∨(v)` as a product of points of `U_β'` and `U_{-β'}` and
     their inverses. So `x` commutes with `β'^∨(v)`.
  3. By torus equivariance of `x_β`, conjugation by `β'^∨(v)` sends `x_β(1)` to
     `x_β(β(β'^∨(v)))`. Here `β(β'^∨(v)) = v ^ ⟨β, β'^∨⟩ = v⁻¹` by `cu_cocharacter` and
     `hpair`. By step 2 the conjugate is `x_β(1)` itself. Since `x_β` is a monomorphism,
     `1 = v⁻¹`, so `v = 1` and `c = 0`. This contradicts `hc`.

- `solve_middle h`: in a group, `a b = c t d` implies `t = c⁻¹ (a b) d⁻¹`.

## Scope

The module works over the base field with a split maximal torus. It does not treat relative
root groups of a nonsplit group, base change, or rational points. It does not construct the
pair `β`, `β'` from a multipliable relative root.
