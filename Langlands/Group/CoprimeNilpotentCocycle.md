# Coprime one-cocycles with values in nilpotent groups are coboundaries

This is an internal lemma about abstract groups. It is a helper for the
characteristic-p case of the conjugacy of sections in trigonalizable groups,
where a finite constant diagonalizable group of order prime to p acts on the rational
points of a unipotent group.

## Statements

All groups are abstract groups in any universe. A one-cocycle of `F` with values in `G`,
for an action `φ`, is a function `c : F → G` with `c (f * g) = c f * φ f (c g)`. It is a
coboundary when there is `a : G` with `c f = a * (φ f a)⁻¹` for every `f`.

- `zpow_gcdA_pow`: if `x ^ n = 1` for every `x` in a group `A` and `m` is prime to `n`,
  then `(x ^ m) ^ (Nat.gcdA m n) = x`. Here `Nat.gcdA m n` is Mathlib's Bézout coefficient
  of `m`, so `m * Nat.gcdA m n + n * Nat.gcdB m n = 1`.
- `abelian`: let `F` be a finite group, `A` a commutative group with `x ^ n = 1` for all
  `x`, and `Nat.Coprime (Nat.card F) n`. Let `φ : F → A →* A` be any family of
  endomorphisms (it need not be an action). Then every `c : F → A` satisfying the cocycle
  identity is a coboundary.
- `VanishingStatement.{u, v}` (proved by `exists_coboundary`): let `F` in universe `u`
  be a finite group and `G` in universe `v` a nilpotent group
  (`Group.IsNilpotent G`) with `x ^ n = 1` for all `x`, and
  `Nat.Coprime (Nat.card F) n`. Let `φ : F →* MulAut G` be an action by automorphisms.
  Then every one-cocycle `c : F → G` is a coboundary.

Nothing is assumed about the characteristic or about `n` beyond coprimality; `n = 0` is
allowed only formally, since then `Nat.Coprime (Nat.card F) 0` forces `F` trivial.

## Proof

`zpow_gcdA_pow` writes `x = x ^ (m * gcdA + n * gcdB)` and kills the second factor.

`abelian` is the averaging argument. Put `P = ∏ g, c g`. Applying `φ f` and the cocycle
identity `φ f (c g) = (c f)⁻¹ * c (f * g)` gives
`φ f P = (c f)⁻¹ ^ |F| * ∏ g, c (f * g) = (c f)⁻¹ ^ |F| * P`, since `g ↦ f * g` permutes
`F`. Hence `P * (φ f P)⁻¹ = (c f) ^ |F|`. Raising to the power `Nat.gcdA |F| n` and using
`zpow_gcdA_pow` gives `c f = a * (φ f a)⁻¹` with `a = P ^ (Nat.gcdA |F| n)`, because
`φ f` commutes with integer powers.

`exists_coboundary` is proved by Mathlib's `Group.nilpotent_center_quotient_ind`, which
inducts on nilpotency class through `G ⧸ center G`. The statement is generalized over `φ`
and `c`. For a trivial (subsingleton) group the coboundary is `1`. In the inductive step,
each automorphism preserves the center (`map_center_eq`), so `φ` induces an action on
`G ⧸ center G`, whose elements still satisfy `x ^ n = 1`. The image of `c` is a cocycle
there, so by induction it equals the coboundary of the class of some `a : G`. Then
`f ↦ a⁻¹ * c f * φ f a` takes values in the center. It is a cocycle for the restricted
action on the commutative group `center G` (a direct computation, closed by `group`),
so `abelian` gives `z` in the center with `a⁻¹ * c f * φ f a = z * (φ f z)⁻¹`. Then
`c f = (a * z) * (φ f (a * z))⁻¹`.

## Provenance

Internal. The averaging argument for coprime actions on abelian groups of finite exponent
and the reduction through a central series are the standard proof that
`H¹(F, G)` is trivial for coprime actions; the Lean proof above is self-contained and
uses only Mathlib.
