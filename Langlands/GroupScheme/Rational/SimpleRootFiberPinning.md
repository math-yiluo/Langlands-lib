# Galois-compatible pinnings in which a relative root fiber consists of simple roots

Module `Langlands.GroupScheme.Rational.SimpleRootFiberPinning`, namespaces
`Langlands.GroupScheme.RelativeRoot` and `Langlands.GroupScheme.SimpleRootFiber`.

Worker 163, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b), SL2 half.

## Purpose

Let `S` be a maximal split torus of `G` over `k`, `f : S ⟶ T` with `T` the centralizer
torus (`j : T ⟶ G` represents the centralizer of `S`), `K/k` a finite extension splitting
`T`, and `P` a reduced root datum of `j_K`. Fix an indivisible relative root `a` with
`2 • a` not a relative root. The construction of SL2 coordinates for `U_a` in
`OrthogonalOrbitSpecialLinear` and `OrthogonalOrbitRootCoordinates` needs a Galois-compatible
pinning over `K` together with a set `O` of simple roots such that:

- `O` is stable under the Galois action on simple roots;
- distinct members of `O` are orthogonal;
- every absolute root of `T_K` restricting to `a` lies in `O`;
- `O` is one Galois orbit, with an embedding `τ t : E →ₐ[k] K` of a field `E` for each
  member, compatible with the Galois action, and every Galois-equivariant family of
  scalars on `O` comes from one element of `E`.

This module supplies these data. It picks the base through a generic cocharacter `ν` of
`S` for which `a` is a simple relative root. Then every absolute root over `a` is simple
for the base, and no Weyl group transitivity argument is needed.

## Relative part (`RelativeRoot`)

Assume `HasRelativeRootSystem i` and `S` split.

- `eq_nsmul_of_not_linearIndependent`: let `β` be a relative root that is ℤ-linearly
  dependent on an indivisible root `b`, and let `μ` be a cocharacter positive on both.
  Then `β = p • b` for some `p > 0`. Proof: dependence gives `n • b = m • β` with
  `n, m > 0`. The ray decomposition `exists_indivisiblePositiveRoot_ray` writes
  `β = p • a'` with `a'` indivisible. If `a' ≠ b`, then
  `disjoint_cyclicTail_indivisibleRoots` is contradicted by `n • b = (m p) • a'`.
- `exists_isGenericCocharacter_mem_simpleRelativeRoots`: every indivisible relative root
  `b` is a simple relative root for some generic cocharacter. Proof:
  `RootReducedness.exists_cocharacter_pairing_eq_zero` gives `ζ` with `⟨b, ζ⟩ = 0` that
  vanishes on no root independent of `b`. `IsSplitTorus.exists_genericCocharacter` gives
  a generic `μ`, negated if needed so that `⟨b, μ⟩ > 0`. Take `λ = N • ζ + μ` with `N`
  larger than every `|⟨γ, μ⟩|`. Then `λ` is generic and `⟨b, λ⟩ > 0`. If `b = β + γ`
  with `β`, `γ` positive for `λ`, then both pair to zero with `ζ`, so both are positive
  multiples of `b` (previous lemma). Pairing with `μ` then gives a contradiction.

## Restriction of absolute roots (`SimpleRootFiber`, sections `Restriction`, `Roots`)

`restrictCharacter k K f hS : characterLattice T_K →+ characterLattice S` is the pullback
along `f_K` followed by the inverse of split character base change. The lemmas
`restrictCharacter_baseChange`, `restrictCharacter_pairing`, `restrictCharacter_galois`,
`restrictCharacter_root_mem` (absolute roots restrict to relative roots, using the
centralizer hypothesis), `regular_root_pairing` (a generic `ν` pushed to `T_K` is regular)
and `simpleRootFiber_mem_base` are imported from
`Langlands.GroupScheme.Rational.SimpleRootValueCharacter`, where the existing helpers
are public in the `SimpleRootFiber` namespace. Both modules reuse those same declarations.
`restrictCharacter_eq_iff` restates restriction to `a` as
`f_K ≫ χ = characterLattice.baseChange _ S a`, which is the Library's
`rootRestrictionFiber` condition.

New results:

- `isOrthogonal_of_restrictCharacter_eq`: let `t ≠ t'` be simple roots of any base of `P`
  with the same restriction `a`, where `2 • a` is not a relative root and
  `⟨a, ν⟩ ≠ 0` for some `ν`. Then `P.IsOrthogonal t t'`. Proof:
  `RootPairing.Base.pairingIn_le_zero_of_ne` gives `⟨t, t'⟩ ≤ 0`. If it were negative,
  `RootPairing.root_add_root_mem_of_pairingIn_neg` would make `root t + root t'` a root.
  This needs `root t ≠ -root t'`, which holds since otherwise `⟨a, ν⟩ = -⟨a, ν⟩`. The sum
  would restrict to `2 • a`, a contradiction. So the pairing is zero, and `IsOrthogonal`
  follows by `RootPairing.pairing_eq_zero_iff'`.
- `eq_one_of_restrictCharacter_eq_nsmul`: if `a` is a relative root, `2 • a` is not, and
  an absolute root restricts to `m • a`, then `m = 1`. This uses
  `HasRelativeRootSystem.eq_one_or_two_of_nsmul_mem`.

## The pinning and the fiber (section `Pinning`)

Add `[FiniteDimensional k K]`, `IsConnectedReductive G_K` and `IsMaximalTorus j_K`.

- `fiberPinning` is `GaloisCompatiblePinningData.ofRegularCocharacter j hP (ν ≫ f) …`, the
  Library's Galois-compatible pinning whose positive roots are those positive on
  `ν ≫ f`. Its roots are those of `P` and its base is `regularCocharacterBase`
  (`fiberPinning_root`, `fiberPinning_support`, both `rfl`).
- `fiberSet a` is the set of simple roots `t` of this pinning with restriction `a`.
  `mem_fiberSet_iff` states this as `f_K ≫ root t = baseChange a`.
- `fiberSet_galois`: the set is stable under the Galois action on simple roots
  (`descendedRegularCocharacterSimpleAction_root` and `restrictCharacter_galois`).
- For `a` simple for `ν`:
  - `fiberSet_isOrthogonal`: if `2 • a` is not a relative root, distinct members are
    orthogonal;
  - `exists_mem_fiberSet`: every absolute root restricting to `a` is a member;
  - `fiberSet_nonempty`: the set is nonempty, by `rootRestrictionFiber_nonempty`.

## The fiber field (section `Field`)

Add `[IsGalois k K]` and `IsClosedSubgroup j`, and let `a` be simple for `ν`.

- `basePoint`, `baseRoot`: a chosen member of the fiber and its actual root.
- `fiberField` is the Library's `rootOrbitField` of the base root, i.e. the fixed field of
  its stabilizer.
- `baseRoot_orbit`: the Galois orbit of the base root is the whole restriction fiber,
  by `rootOrbit_eq_restrictionFiber_of_torusCentralizer`.
- `fiberEmbedding t : fiberField →ₐ[k] K` is the embedding that
  `rootRestrictionFiberEmbeddingEquiv` attaches to the member `t`. Non-members get the
  inclusion, and no result uses these values.
- `fiberEmbedding_galois`: for members `t`,
  `fiberEmbedding (action σ t) = σ ∘ fiberEmbedding t`, by
  `rootRestrictionFiberEmbeddingEquiv_symm_comp`.
- `fiberEmbedding_basePoint`: the base point's embedding is the inclusion, by
  `FiniteGaloisOrbits.orbitEmbeddingEquiv_symm_restriction` at `σ = 1`.
- `exists_eq_fiberEmbedding`: every family `c` of scalars on the simple roots with
  `c (action σ t) = σ (c t)` for members `t` is `t ↦ fiberEmbedding t x` on the fiber, for
  `x = c basePoint`. Here `x` lies in `fiberField` because the stabilizer of the base root
  fixes the base point (roots of `P` are injective). Each member is `action σ basePoint`
  for some `σ`, by `baseRoot_orbit`.

Together, `fiberSet_galois`, `fiberSet_isOrthogonal`, `fiberEmbedding_galois` and
`exists_eq_fiberEmbedding` are the hypotheses `hOs`, `hO`, `hτ` and `FamiliesFromField` of
`OrthogonalOrbitRootCoordinates`, and `mem_fiberSet_iff` gives its `hres`.

## Provenance

Internal. The choice of a generic cocharacter making a given indivisible root simple is the
standard fact that every indivisible root of a root system lies in some basis. Here it is
proved directly from the Library's cocharacter lemmas, not cited from a source. Orthogonality of
simple roots with the same non-multipliable restriction is the usual observation that the
sum of two simple roots at negative pairing is a root. The field and embedding API is the
Library's `RootGaloisOrbits` / `RootFiberTransitivity` description of a Galois orbit of
roots through its stabilizer field. Every step is proved in Lean.
