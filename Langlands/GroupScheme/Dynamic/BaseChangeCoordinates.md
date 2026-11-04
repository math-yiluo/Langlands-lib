# Points of the base change of a corepresented group in tensor coordinates

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. It is derived from
the Library's pullback point equivalence `baseChangePointsEquiv` and its
Corepresented and affine-chart point APIs. No external result is used.

Setting: `G = Spec B` is a corepresented affine group over a field `k`. `Ω` is a
field with `Algebra k Ω`, and `scalarMap k Ω : Spec Ω → Spec k`.
`baseChangeGroup F e Ω` is `G_Ω = (GroupScheme.baseChange (scalarMap k Ω)).obj G`.
For an `Ω`-algebra `A` (with a compatible `k`-algebra structure),
`testOver Ω A` is `Spec A` over `Spec Ω`.

## Definitions

- `testOverHom` and `testOverInv`: identity morphisms comparing `Spec A` over
  `Spec k` with `Spec A` over `Spec Ω` pushed forward to `Spec k`. Their two
  structure maps agree by `specMap_algebraMap_comp_scalarMap` (scalar tower).
  `testOverHom_comp_testOverInv` records that the composite is the identity.
- `basePoint z`: the `k`-point of `G` over `Spec A` underlying a point `z` of
  `G_Ω` over `Spec A`, namely `testOverHom ≫ baseChangePointsEquiv z`.
- `ofAlgHom F e φ`: the point `Spec.map φ` of `G` given by a `k`-algebra map
  `φ : B → A`. `pointAlgHom_ofAlgHom` and `ofAlgHom_pointAlgHom` say that
  `ofAlgHom` and `pointAlgHom` are mutually inverse.
- `bcPoint F e Ω A φ`: the point of `G_Ω` over `Spec A` whose underlying
  `k`-point is `ofAlgHom φ`. It is obtained from the inverse of the pullback
  point equivalence. `basePoint_bcPoint` and `pointAlgHom_basePoint_bcPoint`
  compute its underlying point and classifying map.
- `classifying z : Ω ⊗[k] B →ₐ[Ω] A`: the map `ω ⊗ b ↦ ω · (basePoint z)(b)`,
  built with `Algebra.TensorProduct.lift`. `classifyingHom z` is its spectrum,
  as a morphism `Spec A → Spec (Ω ⊗[k] B)` over `Spec Ω`.
- `univPoint F e Ω`: the universal point
  `bcPoint F e Ω (Ω ⊗[k] B) includeRight`.
- `comparisonMap π : Γ(H, ⊤) → Ω ⊗[k] B`, for a homomorphism `π : G_Ω ⟶ H` to
  an affine `Ω`-group: the affine-chart classifying map of
  `univPoint ≫ π`.

## Results

- `classifyingHom_comp_univPoint z`: every point `z` of `G_Ω` over `Spec A` is
  `classifyingHom z ≫ univPoint`. Proof: the pullback point equivalence is
  injective and natural. The underlying `k`-point of the right side is
  `Spec` of `classifying z ∘ includeRight`, which is the classifying map of
  `basePoint z`.
- `pointRing_comp_eq π z`: the affine-chart classifying map of `z ≫ π` is
  `comparisonMap π` followed by `classifying z`. This combines the previous
  result with the Library's `AffineChart.pointRing_comp`.
