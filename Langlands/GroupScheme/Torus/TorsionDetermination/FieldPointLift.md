# Lifting field-valued points through morphisms with surjective stalk maps

Module `Langlands.GroupScheme.Torus.TorsionDetermination.FieldPointLift`, namespace
`Langlands.GroupScheme.TorsionDetermination`.

This is a helper module for the proof of
`Langlands.GroupScheme.MultiplicativeTypeTorsionDeterminationStatement`. It holds a standard
scheme-theoretic fact, stated and proved here because the Library lacks it. Immersions
(indeed all preimmersions) have surjective stalk maps, so it applies to them.

## Declarations

- `residueFieldMap_bijective f x`: if `f : X ⟶ Y` has surjective stalk maps
  (`SurjectiveOnStalks f`), then the induced map of residue fields
  `κ(f x) → κ(x)` is bijective. It is injective as a field homomorphism. It is surjective
  because every element of `κ(x)` comes from the stalk at `x`, and the stalk map is surjective.
- `exists_lift_of_mem_range f p hx`: let `f : X ⟶ Y` have surjective stalk maps, let `F` be a
  field and `p : Spec F ⟶ Y`. If the image of the closed point of `Spec F` under `p` equals
  `f x` for some `x : X`, then there is `q : Spec F ⟶ X` with `q ≫ f = p`.

## Proof of `exists_lift_of_mem_range`

The morphism `p` factors as `Spec F → Spec κ(p(pt)) → Y` via a field map
`φ : κ(p(pt)) → F` (Mathlib's `descResidueField` / `stalkClosedPointTo`). Identify
`κ(p(pt)) = κ(f x)` with `κ(x)` using the bijection above. This gives a field map
`ψ : κ(x) → F`, and `q` is `Spec ψ` followed by the canonical morphism
`Spec κ(x) → X`. The equation `q ≫ f = p` follows from
`Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`, which relates the residue-field maps
of `f` to the morphisms `Spec κ(·) → ·`.
