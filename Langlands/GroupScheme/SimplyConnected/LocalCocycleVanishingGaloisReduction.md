# From finite Galois covers to finite separable covers

Authors: Worker 1545.

This internal module proves that the finite-Galois form and the
finite-separable form of local cocycle vanishing for simply connected groups
are equivalent. Neither form is proved unconditionally here.

## Declarations

- `exists_finite_galois_algHom F L` takes a field `L : Type u` that is a
  finite separable extension of `F : Type u`. It produces an intermediate
  field `E` of `SeparableClosure F / F` with `FiniteDimensional F E`,
  `IsGalois F E` and an `F`-algebra map `L →ₐ[F] E`. The field `E` lies in
  the same universe `u`.
- `localSimplyConnectedCocycleVanishing_of_galois` proves
  `LocalSimplyConnectedGaloisCocycleVanishingStatement.{u} →
  LocalSimplyConnectedCocycleVanishingStatement.{u}`.
- `localSimplyConnectedGaloisCocycleVanishing_of_separable` proves the
  converse implication.
- `localSimplyConnectedGaloisCocycleVanishing_iff` combines the two into an
  `Iff`.

The universe `u` is arbitrary throughout.

## Proof of the Galois embedding

Let `E` be `IntermediateField.normalClosure F L (SeparableClosure F)`. This
is the compositum of the images of all `F`-embeddings of `L` into the
separable closure.

- `E` is finite-dimensional over `F` by Mathlib's instance
  `normalClosure.is_finiteDimensional`, since `L/F` is finite.
- `E` is normal over `F` by Mathlib's instance `normalClosure.normal`,
  since `SeparableClosure F` is Galois over `F` by Mathlib's instance
  `separableClosure.isGalois`.
- `E` is separable over `F` by
  `Algebra.isSeparable_tower_bot_of_isSeparable F E (SeparableClosure F)`,
  since `SeparableClosure F` is separable over `F`.

Normality and separability together give `IsGalois F E`. The separable
closure is separably closed, and `L/F` is separable, so `IsSepClosed.lift`
gives an `F`-embedding `L →ₐ[F] SeparableClosure F`. Mathlib's equivalence
`normalClosure.algHomEquiv F L (SeparableClosure F)` turns it into an
`F`-algebra map `L →ₐ[F] E`.

## Proof of the reduction

Assume the Galois form `h`. Fix `F`, an affine group scheme `G` over
`Spec F` with `IsSimplyConnected G`, a finite separable `L/F`, and a
cocycle `ξ` on `Spec L`.

1. Obtain `E` and `φ : L →ₐ[F] E` from `exists_finite_galois_algHom`, and
   give `E` the `L`-algebra structure `φ.toRingHom.toAlgebra`.
2. `fieldExtension_fpqc L E`, from `Langlands.GroupScheme.BaseChangeReflection`,
   says that the spectrum map of `algebraMap L E` is surjective, flat and
   quasi-compact. With this algebra structure, that spectrum map is
   definitionally the underlying scheme morphism of
   `ringTestMap F φ : ringTest F E ⟶ ringTest F L`, from
   `Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints`. So the
   three properties are recorded as instances on `(ringTestMap F φ).left`.
3. `ξ` is restated as a cocycle `ξ'` on `ringTest F L`, which is
   definitionally `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L)))`.
   This is only a change of displayed type, made so that the instances of
   step 2 are found syntactically.
4. The refined cocycle `ξ'.refine (ringTestMap F φ)` lives on
   `ringTest F E`, which is definitionally the Galois cover of `Spec F` by
   `Spec E`. So `h F G hG E` shows that it is trivial.
5. `Cocycle.isTrivial_refine_iff`, from
   `Langlands.GroupScheme.CocycleRefinement`, says that triviality is
   reflected along a surjective, flat, quasi-compact refinement. Applied
   with the instances of step 2, it gives `ξ'.IsTrivial`, which is
   `ξ.IsTrivial`.

## Proof of the converse

Every finite Galois extension is separable, by the instance
`IsGalois.to_isSeparable`. So the separable form `h`, applied to a finite
Galois `M/F` with the same group and cocycle, gives the Galois form
directly.

## Scope

Both implications are unconditional, and the only axioms used are
`propext`, `Classical.choice` and `Quot.sound`. The arithmetic content, which
is the vanishing on finite Galois covers (Kneser, Bruhat–Tits), stays an
open hypothesis. It is the proposition
`LocalSimplyConnectedGaloisCocycleVanishingStatement` in
`Langlands.GroupScheme.SimplyConnected.LocalGaloisCocycleVanishingStatement`.
