# Determinant normalization of extensions

This internal module normalizes a representation of `p`-power dimension by a
character twist so that its determinant has `p`-power order. Existence needs a
determinant of finite order whose restriction to a subgroup `N` has `p`-power
order; uniqueness holds among twists by characters killed by an exponent prime
to `p`. In the Clifford theory of wild inertia this picks an extension of a wild
class to its stabilizer that is fixed by every automorphism fixing the class.

## Powers in commutative groups

- `eq_one_of_pow_coprime`: an element killed by two coprime exponents is one.
- `exists_zpow_pow_eq`: if `y^m = 1` and `k` is prime to `m`, then `y` is the
  `k`-th power of a power of `y` (Bézout).
- `exists_split`: an element killed by `p^s * m` with `p^s` and `m` coprime is
  the product of a power killed by `p^s` and a power killed by `m`.

## Determinant characters

- `detChar θ` is the determinant of `θ`, a homomorphism to `ℂˣ`
  (`detChar_apply`). For finite-dimensional representations it is invariant
  under equivalence (`detChar_eq_of_equiv`); it is compatible with pullback
  (`detChar_comp`), and its kernel contains that of `θ` (`ker_le_ker_detChar`).
- `detChar_twist` and `detChar_twist_apply`: for finite-dimensional `θ`,
  `det (twist χ θ) = χ ^ dim θ * det θ`.

## Normalization

Let `N` be a subgroup of `H` and `θ` a finite-dimensional representation of
`H` with `dim θ = p^a`, `p` prime.

- `exists_twist_detChar_pPower`: if `det θ` has finite order `p^s m` with
  `p ∤ m`, and its restriction to `N` has `p`-power order, there is a
  character `γ`, trivial on `N` and on the kernel of `θ`, such that
  `det (twist γ θ)` has `p`-power order. The character `γ` is an explicit
  integer power of `det θ`, inverse to a `p^a`-th root of the prime-to-`p` part
  of `det θ`. It is trivial on `N` because the prime-to-`p` part of a
  `p`-power order element is one.
- `eq_one_of_detChar_pPower`: if `χ` has order dividing some `m` prime to `p`,
  and both `det θ` and `det (twist χ θ) = χ^(p^a) det θ` have `p`-power order,
  then `χ^(p^a)` has both `p`-power order and order dividing `m`, so it is
  one; as `p^a` is prime to `m`, `χ = 1`.

The statements are written pointwise (`∀ h, detChar θ h ^ n = 1`) rather than
as equalities of characters.
