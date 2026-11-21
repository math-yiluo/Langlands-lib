# Primitive homomorphisms of abelian schemes

This internal module introduces primitive actual homomorphisms of abelian
schemes and proves the existence and uniqueness facts needed to choose a
canonical integral representative of a positive rational ray of
homomorphisms. It adds no literature assertion and no new premise.

## Definition

`IsPrimitiveHom f` is the definition of the module. An actual homomorphism
`f : A ⟶ B` is primitive when every equation `j • g = f`, for a natural
number `j` and an actual homomorphism `g`, forces `j = 1`.

## Torsion actions

`levelMap_multiplication` shows that multiplication by `k` acts on actual
`n`-torsion points as multiplication by `k`, using the published
`GroupScheme.points_multiplication`. `levelMap_comp` states that the action
of a composite is the composite of the actions. `levelMap_nsmul` follows:
`k • f` acts as `k` times the action of `f`, because `k • f` is the
composite of multiplication by `k` with `f` (`groupHom_nsmul_id`).
`levelMap_nsmul_self` concludes that `n • f` kills the `n`-torsion points,
since that level is killed by `n`.

## Existence of a primitive factor

`exists_isPrimitiveHom_nsmul_eq` assumes a bound `N` on the positive
integers `k` for which `f` is `k` times an actual homomorphism. It then
writes `f = k • g` with `k > 0` and `g` primitive. The proof takes the
largest such `k` up to `N` (`Nat.findGreatest`). If `g = j • g'`, then
`k j` is also a divisor of `f` and so `k j ≤ k`. Here `j = 0` is
impossible: it would make `f = 0`, and then `N + 1` would divide `f`. Hence
`j = 1`. This part needs no hypothesis on the base.

## Divisibility and uniqueness on a connected base

The remaining results assume a connected locally noetherian base on which
every positive integer is a unit, the finite-étale torsion statement, and an
algebraically closed point `s`.

`exists_nsmul_eq_iff_levelMap_eq_zero` characterizes divisibility: `f` is
`n` times an actual homomorphism exactly when it kills the actual `n`-torsion
points at `s`. One direction is `levelMap_nsmul_self`. For the other, the
published `kernel_comp_eq_one_of_levelMap_eq_zero` shows that `f` kills the
`n`-torsion kernel. The published isogeny factorization then factors `f`
through multiplication by `n`, as in the proof of
`Tate.exists_ofHom_eq_of_full_image`.

`eq_of_nsmul_eq_nsmul_of_isPrimitiveHom` is uniqueness. Let `f` and `g` be
primitive with `a • f = b • g` for positive `a` and `b`. Then `a = b` and
`f = g`. Write `a = a' d` and `b = b' d` with `d` the greatest common divisor
and `a'`, `b'` coprime (`Nat.exists_coprime'`). Cancellation of `d`
(`hom_nsmul_injective`) gives `a' • f = b' • g`. On `b'`-torsion points the
action of `f` is killed by `a'` and by `b'`, hence by their greatest common
divisor `1`. So `f` kills the `b'`-torsion, and `f` is `b'` times an actual
homomorphism. Primitivity gives `b' = 1`, and symmetrically `a' = 1`.

This module does not treat polarizations, degrees or level structures.
