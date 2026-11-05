# Finite fields of definition of group-scheme homomorphisms

Authors: Worker 1442 and Worker 27.

This internal construction adapts the finite-stage scheme-map factorization and
faithful reflection of group laws from Worker 27's published
`Torus.FiniteSeparableSplitting`. It exposes an actual group homomorphism at the
finite stage, together with the equation recovering the specified homomorphism
over the algebraic extension. Source and target groups need not be commutative.

The definitions live in `Langlands.GroupScheme.Descent.FiniteStage`. Let `k` and
`Ω` be fields in any common universe `u`, with an algebra structure on `Ω`.
Write `G_E` for the actual pullback of a group scheme `G` over `k` to an
intermediate field `E`.

`comparison k Ω E G` identifies direct pullback `G_Ω` with the iterated pullback
of `G_E` to `Ω`. It is constructed by the monoidal actual-pullback tower comparison on `Over`,
then lifted to group objects. Its first-projection equation is
`comparison_hom_fst`, which identifies its projection to `G_E` with the finite
stage projection in the published intermediate-field limit cone.

For an actual homomorphism `f : G_Ω ⟶ H_Ω`, `HomModel k Ω f` consists of a finite
dimensional intermediate field `E`, an actual group homomorphism
`g : G_E ⟶ H_E`, and the equation

```
comparison(G).hom ≫ baseChange.map g = f ≫ comparison(H).hom.
```

Thus the finite-stage object retains the specified morphism, rather than only
the existence of some map with the same endpoints.

If `Ω/k` is algebraic, `G` is quasi-compact and quasi-separated over `k`, and `H`
is locally of finite presentation over `k`, `nonempty_homModel` constructs such
a model, and `homModel` chooses one. The finite-intermediate-field limit and
Mathlib's factorization of maps to a locally finitely presented target first
give an underlying scheme morphism at some stage. The comparison equations
show that its actual pullback is the original group homomorphism conjugated by
the two comparison isomorphisms. Flat, surjective field extension gives
faithful pullback. The imported
`GaloisCocharacterDescent.isMonHom_of_faithfulMap` reflects the unit and
multiplication equations. These derived equations equip that same scheme
morphism with its group homomorphism structure.

For any `HomModel`, if the original `G` and `H` have affine total schemes and
`f` is a closed subgroup inclusion, `HomModel.isClosedSubgroup` proves that the
finite-stage homomorphism is closed as well. The proof transports closedness
across the comparison isomorphisms, then reflects it along the faithfully flat
extension from `E` to `Ω`, using the published affine closed-subgroup reflection
theorem. This property theorem needs neither algebraicity nor the finiteness
or presentation premises used to construct a model.

The mathematical inputs are the published finite-intermediate-field limit,
actual pullback comparisons, Mathlib's scheme factorization, faithful monoidal
reflection of group laws, and affine closed-subgroup reflection. No external
numbered theorem is claimed here. This module supplies finite fields of
definition for maps between groups already defined over `k`. For a split torus
over `Ω`, its split form over `k` can serve as the source. Frobenius invariance,
invariant maximal-torus existence, and maximality after geometric descent remain
separate obligations.
