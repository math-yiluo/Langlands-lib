# Stable evaluation pairing between upper and opposite Jacquet modules

This module proves an abstract form of Casselman's canonical pairing between the
upper Jacquet module of the smooth contragredient and the opposite Jacquet
module: Bill Casselman, *Introduction to admissible representations of p-adic
groups*, Chapter III, revision April 29, 2019 (`casselman-2019-jacquet-module`),
Section 6, Theorem III.6.2 and Corollary III.6.3, pages 7–8, with the nested
comparison of Lemma III.5.7. The abstraction, its hypotheses and the route
through stable images are internal to this project; the module adds no statement
to the Library and only supports the proof of
`Langlands.Parabolic.NaturalNormalizedJacquetDualityStatement`.

## Averaging and conjugation helpers

For a smooth representation `ρ` of a topological group `G` and a compact open
subgroup `K`, `Compact.averageMap ρ hρ K hK` is the `K`-average. The helpers show:

- `averageMap_apply_of_mem`: averaging is unchanged by first translating by an
  element of `K`;
- `averageMap_averageMap_of_le`: for `L ≤ K`, `K`-averaging absorbs `L`-averaging;
- `conjOpenSubgroup m K` is the open subgroup `m K m⁻¹`
  (`mem_conjOpenSubgroup`), compact when `K` is (`isCompact_conjOpenSubgroup`);
  translating by `m` carries `K`-fixed vectors to `m K m⁻¹`-fixed vectors
  (`conj_mem_fixedVectors`, packaged as `conjFixedVector`) and intertwines the two
  averages (`averageMap_conj`);
- for `m` commuting with `h`, translation by `m` intertwines powers of compression
  by `h` for `K` and for `m K m⁻¹` (`compressedAction_pow_conj`) and so maps stable
  images to stable images (`conjFixedVector_mem_stableImage`);
- `exists_open_fixed_lift`: every class of a coinvariant quotient of a smooth
  representation lifts to a vector fixed by every open subgroup of some open
  subgroup;
- `smoothDualPairing_averageMap`: a `K`-fixed smooth functional has the same value
  at a vector and at its `K`-average;
- `compressedAction_pow_adjoint`: powers of compression by `g` on the smooth dual
  are adjoint to powers of compression by `g⁻¹`, from the Library adjunction
  `compressedAction_adjoint`. Consequently the power kernel of compression by `g`
  on the smooth dual annihilates the stable image of compression by `g⁻¹`, and the
  stable image of compression by `g` on the smooth dual annihilates the power
  kernel of compression by `g⁻¹`
  (`smoothDualFixedRestriction_eq_zero_of_mem_powerKernelSup` and its `_inv`
  variant), by induction over the supremum of power kernels.

## Group data and hypotheses

`StablePairingData G` records subgroups `N`, `Nbar`, `M` with `M` normalizing `N`
and `Nbar`, an element `g` commuting with `M`, and a predicate `Good` on open
subgroups such that good subgroups are compact, form a neighborhood basis of the
identity (`exists_good_subset`), are stable under conjugation by `M`, admit an
`Nbar M N` factorization inside `K`, satisfy `g⁻¹ (K ∩ Nbar) g ⊆ K` and
`gʳ (K ∩ N) g⁻ʳ ⊆ K` for all `r`, and are *deep*: for good `K₀, K₁` some power
`gʳ` conjugates `K₀ ∩ N` into `K₁`.

`StablePairingData.Admits ρ hρ` asks, for every good `K`: finite-dimensional
`K`-fixed vectors; the stable image of compression by `g` on the smooth dual
surjects onto the `K ∩ M`-fixed upper classes, and the kernel of the upper
quotient map on `K`-fixed smooth functionals lies in the power kernel of
compression by `g`; the same for `ρ`, the opposite quotient and `g⁻¹`. These are
weaker than the Library's canonical-lift bijectivity and power-kernel equalities.

## Class preservation

`compressedAction_inv_pow_apply` shows that the `r`-th power of compression by
`g⁻¹` on a `K`-fixed vector `w` is the `K`-average of `ρ(g⁻ʳ) w`: write `k = l m u`
using the factorization, absorb `gʳ u g⁻ʳ` into `w`, and absorb `g⁻¹ l g` and `m`
into the outer average.

`map_mk_averageMap` is the key comparison. Let `K₁ ≤ K₀` be good, `s` in the
stable image for `K₁`, and `f` a linear map on the opposite quotient invariant
under `K₀ ∩ M` at the class of `s`. Choose `r` by depth and write `s` as the
`K₁`-average of `u = ρ(g⁻ʳ) w`. Then `u` is fixed by `K₀ ∩ N` and by `K₁ ∩ M`, so
`s` and `u` have the same opposite class, and the `K₀`-average of `s` equals the
`K₀`-average of `u`, whose class under `f` equals `f` of the class of `u` by the
factorization of `K₀` and the invariance of `f`.

## The stable pairing

For a good `K`:

- `pairing_eq_of_dual_mk_eq`: `K`-fixed smooth functionals with the same upper
  class agree on the stable image of compression by `g⁻¹` (kernel in the power
  kernel, then annihilation);
- `pairing_eq_of_mk_eq`: a smooth functional in the stable image of compression
  by `g` agrees on `K`-fixed vectors with the same opposite class;
- `pairing_eq_of_le`: for good `K₁ ≤ K₀`, a `K₀`-fixed smooth functional takes the
  same value at stable vectors for `K₀` and `K₁` with the same opposite class. Its
  proof replaces the functional by a stable one with the same upper class,
  replaces the `K₁`-stable vector by its `K₀`-average (same value, and the same
  opposite class by `map_mk_averageMap` applied to the identity), and applies the
  two previous lemmas.

`exists_value` concludes that the value `ℓ(t)` at a `K`-fixed smooth functional
`ℓ` and a stable vector `t` depends only on the upper class of `ℓ` and the
opposite class of `t`, independently of `K`, by comparing any two choices through a
common smaller good subgroup.

`IsStablePairing ρ hρ b` says that the bilinear form `b` on the upper quotient of
the smooth dual and the opposite quotient satisfies `b [ℓ] [t] = ℓ(t)` for every
good `K`, `K`-fixed `ℓ` and stable `t`. `exists_isStablePairing` builds one with
`LinearMap.mk₂` from the class-only values, with additivity and homogeneity checked
on common representatives (`exists_common_lift`).

## Properties of stable pairings

- `IsStablePairing.injective`: if `b x = 0`, lift `x` to a stable functional `ℓ'`
  for some good `K`; it vanishes on the stable image of compression by `g⁻¹`, so it
  is zero by the Library's compact compression evaluation duality
  `compactCompression_stableEvaluationDuality`.
- `IsStablePairing.exists_eq`: a functional `φ` on the opposite quotient invariant
  under `K ∩ M` for a good `K` equals `b x`. The duality gives a stable functional
  `ℓ` with `ℓ(t) = φ[t]` on the stable image; for any class, a stable lift `t₁` for a
  smaller good subgroup is compared with a stable vector for `K` having the class of
  its `K`-average, using `map_mk_averageMap` for `φ`.
- `IsStablePairing.map_action`: `b` is invariant under the diagonal action of
  `M`, by conjugating good subgroups, fixed functionals and stable vectors by `m`.
- `IsStablePairing.exists_open_invariant`: each `b x` is invariant under `U ∩ M`
  for an open `U` fixing a lift of `x`.
- `IsStablePairing.natural`: for an intertwiner `a : ρ → σ` and stable pairings
  for `ρ` and `σ`, `b (J(a*) x) y = bσ x (J(a) y)`, since `a` and its
  contragredient preserve fixed vectors and stable images.
- `IsStablePairing.exists_equiv`: given a topological group `L`, a topological
  isomorphism `ι : L ≃ₜ* M`, a function `χU` and a character `χO` with open kernel
  and `χU l · χO l = 1`, a representation `σU` of `L` identified by `eX` with the
  upper quotient twisted by `χU` through `ι`, and the opposite quotient twisted by
  `χO` through `ι`, the map `x ↦ b (eX x)` is an equivalence of `σU` with the smooth
  contragredient of the twisted opposite quotient. Smoothness of `b (eX x)` comes
  from `exists_open_invariant` and the kernel of `χO`; equivariance from
  `map_action` and `χU l = (χO l)⁻¹`; injectivity from `injective`; surjectivity
  from `exists_eq`, after transporting an open stabilizer in `L` to an open subset
  of `G` meeting `M` in its image under `ι` and choosing a good subgroup inside it.
