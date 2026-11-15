# A finite Galois level inside the maximal unramified extension

Module `Langlands.Geometry.Building.UnramifiedFiniteGaloisLevel`, namespace
`Langlands.Geometry.Building.MaximalUnramified`.

## Setting

`F` is a nonarchimedean local field (any characteristic). `K = F^ur` is the Library's
`inertiaFixedField F`: the intermediate field of `SeparableClosure F / F` fixed by the inertia
subgroup (`Langlands.LocalGalois.Separable.inertiaFixedField`, module
`Langlands/Galois/Local/SeparableInertiaDefinitions.lean`). The Library already provides
the instance `IsGalois F (inertiaFixedField F)`.

## Declarations

### `exists_galoisLevel`

`exists_galoisLevel (F) (E₀ : IntermediateField F (inertiaFixedField F))
[FiniteDimensional F E₀]` states that there exist

- an intermediate field `E` of `SeparableClosure F / F` with `FiniteDimensional F E`,
  `IsGalois F E` and `E ≤ inertiaFixedField F`, and
- a group homomorphism `res : (K ≃ₐ[F] K) →* (E ≃ₐ[F] E)`,

such that

1. `res` is surjective;
2. `res` is compatible with the inclusion `E ⊆ K`: for every `σ` and every `x : K` whose
   value in `SeparableClosure F` lies in `E`, the value of `res σ ⟨x, hx⟩` in
   `SeparableClosure F` is the value of `σ x`;
3. the fixed field of `ker res` is `E`: every `x : K` fixed by all `σ` with `res σ = 1` lies in
   `E`;
4. `ker res` fixes `E₀`: `res σ = 1` implies `σ ∈ E₀.fixingSubgroup`.

The statement uses only standard Galois theory. It gives the finite Galois level at which a
cocycle of `Aut(K/F)` (from `K`-points that are defined over `E₀`) can be treated as a cocycle
of the finite group `Gal(E/F)`. The intended source of `E₀` is the Library theorem
`TwistedGeneratorReduction.exists_finite_fixing_rationalPoints`.

### `GaloisLevel` and `nonempty_galoisLevel`

`GaloisLevel F E₀` is a structure that bundles the data and properties of
`exists_galoisLevel`. Its fields are:

| Field | Meaning |
| --- | --- |
| `E` | the intermediate field of `SeparableClosure F / F` |
| `finiteDimensional`, `isGalois` | `E / F` is finite and Galois; both are registered as instances |
| `le_inertiaFixedField` | `E ≤ inertiaFixedField F` |
| `res` | the homomorphism `(K ≃ₐ[F] K) →* (E ≃ₐ[F] E)` |
| `res_surjective` | clause (1) |
| `res_apply` | clause (2) |
| `mem_of_forall_fixed` | clause (3) |
| `ker_le_fixingSubgroup` | clause (4) |

`nonempty_galoisLevel F E₀ : Nonempty (GaloisLevel F E₀)` holds for every finite-dimensional
`E₀`, and is deduced from `exists_galoisLevel`. The structure defines no new mathematical
object. It is an interface: a consumer that has to keep `E` and `res` around can carry one
term instead of five existential witnesses.

## Proof of `exists_galoisLevel`

- `E₁ := E₀.map K.val` is `E₀` viewed inside `SeparableClosure F`. It is finite over `F`
  because `IntermediateField.equivMap` is an `F`-linear equivalence, and it lies in `K`.
- The Library lemma `Langlands.GroupScheme.GaloisCocycle.exists_finiteDimensional_isGalois_between`
  (module `Langlands/GroupScheme/LocalUnramifiedTwistDescent.lean`) applied to the normal
  extension `K` and `E₁ ≤ K` gives a finite Galois `E` with `E₁ ≤ E ≤ K`. Concretely it is
  the normal closure of `E₁` in `SeparableClosure F`.
- With the algebra `E → K` given by `IntermediateField.inclusion`, `res` is Mathlib's
  `AlgEquiv.restrictNormalHom E`. Mathlib's `AlgEquiv.restrictNormalHom_surjective` gives (1)
  because `K/F` and `E/F` are normal. `AlgEquiv.restrictNormal_commutes` gives (2).
- For (3): if `σ` fixes `IntermediateField.restrict hEK` (that is, `E` as an intermediate field
  of `K / F`), then (2) gives `res σ = 1`. So `x` lies in the fixed field of the fixing
  subgroup of `restrict hEK`. That fixed field is `restrict hEK` by Mathlib's infinite Galois
  correspondence `InfiniteGalois.fixedField_fixingSubgroup`, applicable because `K/F` is
  Galois. `IntermediateField.mem_restrict` turns this into `x ∈ E`.
- For (4): an element `y ∈ E₀` has its value in `E₁ ⊆ E`, and (2) with `res σ = 1` gives
  `σ y = y`.
