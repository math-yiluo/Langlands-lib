# Post-composition actions on spaces of linear maps

Module `Langlands.Automorphic.PlaceComponentHom`, namespace `Langlands.Automorphic.PlaceComponent`.
Worker 174 wrote it as a step towards G1 (Task 5992). Provenance: internal linear algebra.

Let `κ` be a representation of a group `K` and `π` a Lie action on a complex vector space `V`.

## Definitions

- `postComp m : Module.End ℂ V →ₐ[ℂ] Module.End ℂ ((Fin m → ℂ) →ₗ V)` is post-composition.
- `postRep m κ` and `postLie m π` are the representation and Lie action on
  `(Fin m → ℂ) →ₗ V` by post-composition. `postRep_apply` and `postLie_apply` say that
  `(k · φ)(x) = κ k (φ x)` and `(X · φ)(x) = π X (φ x)`.
- `evalAt m x` is evaluation at `x`. It is equivariant by definition.

## Results

- `eq_zero_of_single`, `apply_eq_sum` and `eq_sum_smulRight`: a linear map on `Fin m → ℂ` is
  determined by its values `φ(eⱼ)` on the standard basis, and equals
  `∑ⱼ (proj j).smulRight (φ eⱼ)`.
- `isWeaklyContinuous_postRep`: if `κ` is weakly continuous, so is `postRep m κ`. A linear form
  `μ` on the space of maps satisfies `μ(k · φ) = ∑ⱼ μⱼ(κ k (φ eⱼ))` for the linear forms
  `μⱼ v = μ((proj j).smulRight v)`.
- `isLocallyFinite_postRep`: if `κ` is locally finite, so is `postRep m κ`. Take
  finite-dimensional stable `Eⱼ ∋ φ(eⱼ)` and `E = ⨆ Eⱼ`. Then `φ` lies in the
  finite-dimensional stable space of maps with values in `E`.
- `intertwiners_ne_bot_postRep` (**detection passes to post-composition**). Hypotheses:
  `K` is compact, and a matrix representation `τ` has a nonzero intertwiner into every
  nonzero stable subspace of `V`. Conclusion: `τ` also has one into every nonzero stable
  subspace `N` of the space of maps. Proof:
  1. Take `φ ∈ N` and `j` with `φ(eⱼ) ≠ 0`.
  2. The image of `N` under `evalAt eⱼ` is a nonzero stable subspace of `V`, so it receives a
     nonzero `τ`-intertwiner `ψ`.
  3. Lift `ψ` through `evalAt eⱼ` restricted to `N` (`CompactMaschke.exists_lift_intertwiner`,
     with the two results above). The lift is a nonzero intertwiner into `N`.
