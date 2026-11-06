# The identity double coset in an enumeration of `P(F) \ G(F) / P(F)`

Module `Langlands.Representation.Geometric.IdentityDoubleCoset`. Bookkeeping for the proof of
Renard VI.5.3 (`MaximalLeviSupercuspidalInductionEndomorphismStatement`), where the geometric
lemma (Renard VI.5.1) is applied with `Q = P` and its graded pieces are indexed by an
enumeration `c : Fin m ≃ P(F) \ G(F) / P(F)` with representatives `z i`. The identity double
coset `P(F) · 1 · P(F)` gives the piece isomorphic to `ρ` itself; every other index has a
representative outside `P(F)`.

## Provenance

Internal. Nothing here formalizes a numbered statement of a source. Renard VI.5.3 singles out
the double coset of the identity among the double cosets `P(F) w P(F)`; this module makes
that index explicit for an arbitrary enumeration and records the elementary group theory
that distinguishes it.

## Double cosets of a subgroup with itself

All in namespace `Langlands.Aubert.General.RepresentedParabolic`, for a group `H` and a
subgroup `K`.

- `doubleCoset_mk_eq_mk_one_iff`: `DoubleCoset.mk K K x = DoubleCoset.mk K K 1` iff `x ∈ K`.
  Proof: by `DoubleCoset.eq`, equality means `a * x * b = 1` for some `a, b ∈ K`, so
  `x = a⁻¹ * b⁻¹ ∈ K`; conversely `x⁻¹ * x * 1 = 1`.
- `identityDoubleCosetIndex K c` (definition): for an enumeration
  `c : Fin m ≃ DoubleCoset.Quotient K K`, the index `c.symm (DoubleCoset.mk K K 1)` of the
  identity double coset.

The remaining statements assume representatives `z : Fin m → H` with
`hz : ∀ i, DoubleCoset.mk K K (z i) = c i`.

- `mem_iff_eq_identityDoubleCosetIndex`: `z i ∈ K` iff `i = identityDoubleCosetIndex K c`.
  Proof: rewrite `z i ∈ K` as `DoubleCoset.mk K K (z i) = DoubleCoset.mk K K 1` by the
  previous lemma, replace the left side by `c i` using `hz`, and apply `Equiv.eq_symm_apply`.
- `mem_identityDoubleCosetIndex`: the representative at the identity index lies in `K`.
- `not_mem_of_ne_identityDoubleCosetIndex`: for `i ≠ identityDoubleCosetIndex K c`, both
  `z i ∉ K` and `(z i)⁻¹ ∉ K` (the second by `inv_mem_iff`).

## Application to a represented parabolic

- `not_mem_pointImage_levi_of_ne_identityDoubleCosetIndex`: for a field `k`, group schemes
  `G, P, M` over `Spec k`, morphisms `p : P ⟶ G` and `l : M ⟶ P`, an enumeration
  `c : Fin m ≃ DoubleCoset.Quotient (pointImage p) (pointImage p)` of
  `P(F) \ G(F) / P(F)` with representatives `z i` as above, and
  `i ≠ identityDoubleCosetIndex (pointImage p) c`, both `z i` and `(z i)⁻¹` lie outside the
  image `pointImage (l ≫ p)` of `M(F)` in `G(F)`. Proof: the previous lemma with
  `K = pointImage p` and `pointImage_comp_le p l : pointImage (l ≫ p) ≤ pointImage p`.
  No hypothesis on `p` or `l` (closedness, Levi decomposition) is needed.
