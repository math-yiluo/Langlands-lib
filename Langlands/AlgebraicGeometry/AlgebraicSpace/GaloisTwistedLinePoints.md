# Rational points of the Galois-twisted line

Author: Worker 105.

This is support for clause (3) of Conrad's Example 5.13 (printed p.20). For `s ∈ K'`,
`linePt K s : ringTest K K' ⟶ lineOver K K'` is the `K'`-point of the line with coordinate `s`.
Its image in the Galois-twisted line `X` is `a(u_s) = atlas (linePt K s)`.

## Helpers

- `unitSpec B` is the map `B → Γ(Spec B, ⊤)`, which is injective (`unitSpec_injective`).
- `ofSpec_specMap`, `ofSpec_ringTestMap`, `ofSpec_linePt_apply` and `ofSpec_conj_linePt_apply`
  compute the ring maps of the points involved.
- `ofSpec_left_algebraMap`: a point of the line over `T` restricts on `K` to the structure map
  of `T`.

## The point with coordinate `0` does not descend (`changeRing_ne_zero`)

Suppose `x ∈ X(K)` restricts to `a(u_0)` in `X(K')`.

1. Restriction from `K` is invariant under the conjugation `σ` of `Spec K'`, because the two
   `K`-algebra maps `K → K'` coincide. So `a(σ ∘ u_0) = a(u_0)`
   (`atlas_app_conj_of_changeRing`).
2. The kernel pair of the atlas gives a `K'`-point `r` of the relation with `t ∘ r = σ ∘ u_0`
   and `s ∘ r = u_0`.
3. `relation_false` rules this out, using the ring map `φ` of `r`:
   - both composites send `X` to `0`, so the unit `pairUnit` is the idempotent `pairIdem` itself;
   - a unit idempotent is `1`;
   - `splitIdem_mul_θ` then gives `θ = σ θ`, contradicting `σ θ ≠ θ`.

## The points with coordinate `c ∈ K^×` descend (`exists_changeRing_eq`)

This part assumes `[Module.Finite K K']`. The map `Spec K' → Spec K` is flat, locally of finite
presentation and surjective (`flat_ofId`, `locallyOfFinitePresentation_ofId`,
`surjective_ofId`). So `X` is a sheaf for the single covering `Spec K' → Spec K`
(`ProductPointsDescent.isSheafFor_singleton`).

It remains to check compatibility. Let `q₁ q₂ : Z ⟶ Spec K'` be two maps that agree over
`Spec K`. Then `a(q₁ ∘ u_c) = a(q₂ ∘ u_c)` (`atlas_app_eq_of_comp_eq`):

- the two points of the line lie over the same base point, since both send `X` to the image of
  `c`;
- their `pairUnit` is `e + (1 − e) c`, a unit because `c` is a unit (`isUnit_idem_add`);
- so `relHom` gives a point of the relation between them, and `atlas_app_t_eq_s` concludes.
