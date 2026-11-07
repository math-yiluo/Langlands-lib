# Twisting by a locally free module pulled back from a base with finite support

Lean module: `Langlands.AlgebraicGeometry.Modules.FiniteSupportTwistEuler`,
namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`.

Author: Worker 998.

## Role and provenance

This is internal infrastructure for task `981f6bcb-41de-4a08-83b8-48b6eec2b236`, the proof
of `Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingStatement`. It proves a
general form of the twist step, formula (10) in the proof of (9.11) of Edixhoven, van der
Geer and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, printed p.132, PDF p.136). There, the
higher direct images of a line bundle along a projection are supported on a finite set.
Twisting by the pullback of a line bundle that is trivial near this set then does not change
cohomology. Here the twisting module may be locally free of any rank `d`, and the Euler
characteristic is multiplied by `d`. The case `d = 1` is the source's step. The case of
general `d` is used for finite flat base change in
`Langlands.AlgebraicGeometry.Modules.FiniteFlatBaseChangeEuler`. All declarations are
derived. None is a new mathematical notion or a statement target.

## Setting

Throughout, `p : Z ⟶ Y` is a morphism of schemes and `F` is a line bundle on `Z` (a Library
`LineBundle`). `W` is a module on `Y` and `d` a natural number. "Free charts of rank `d`"
for `W` is the hypothesis `hW`: every point `y` has an open neighbourhood `V` with an
isomorphism from the restriction of `W` to `V` to the free module
`SheafOfModules.free (ULift (Fin d))` on `V`. `Rⁿ p_*` is the Library's `higherDirectImage p n`,
and `Hⁿ` is `relativeCohomology`. `tensorObj` is the Library's sheafified tensor product.

## Declarations

- `restrictTensorIso' j M N`: restriction to an open subscheme commutes with `tensorObj`.
  It converts restriction to pullback (`restrictFunctorIsoPullback`) and uses the Library
  comparison `pullbackTensorIso`.
- `pullbackFreeIso f d`: the pullback of the free module on `d` generators is free on `d`
  generators. Pullback is a left adjoint, so it preserves coproducts, and it preserves the
  structure sheaf (`pullbackUnitIso`). The isomorphism is then Mathlib's
  `SheafOfModules.mapFreeIso`.
- `twistRestrictIso p F W d V eV n`: if `eV` identifies the restriction of `W` to the open `V`
  with the free module of rank `d`, then the restriction to `V` of `Rⁿ p_*(F ⊗ p^* W)` is the
  coproduct of `d` copies of the restriction to `V` of `Rⁿ p_* F`. With `j` the inclusion of
  `p⁻¹ V`, the steps are:
  1. `Rⁿ p_*` commutes with restriction to `V` (Library `higherDirectImageRestrictIso`).
  2. The restriction of `F ⊗ p^* W` to `p⁻¹ V` is `j^* F ⊗ (p ∣_ V)^*(W|_V)`
     (`restrictTensorIso'` and the Library `restrictPullbackIso`).
  3. This is `j^* F ⊗ free`, by `eV` and `pullbackFreeIso`.
  4. That is a coproduct of `d` copies of `j^* F`, by the Library
     `lineBundleFiniteFreeTensorIso` applied to the line bundle `j^* F`.
  5. The functor `Rⁿ (p ∣_ V)_*` preserves this finite coproduct. It is additive by the
     Library instance `Langlands.AlgebraicGeometry.Modules.CechResolution.rightDerived_additive`
     (module `Langlands.Cohomology.RightDerivedAdditive`), applied to the pushforward.
  6. Each summand is converted back by step 1.
- `relativeGlobalSectionsCoproductIso`: relative global sections of `∐_{i<d} M` are
  `d`-tuples of sections. The functor is additive, so it preserves the finite coproduct
  (a biproduct); `ModuleCat.biproductIsoPi` finishes.
- `isZero_sigma_of_isZero`: a coproduct of zero objects is zero.
- `restrictFreeOfLE`: a free chart over `V` restricts to a free chart over every open
  `V' ≤ V`. It uses Mathlib's `restrictFunctorComp`, `Scheme.homOfLE_ι` and the Library's
  `restrictFiniteFreeIso`.
- `isZero_restrict_of_stalkSupport` and `not_mem_stalkSupport_of_isZero_restrict`: a module
  restricts to zero on an open `O` exactly when its stalks vanish at the points of `O`. The
  stalks are compared by Mathlib's `restrictStalkNatIso`, and the Library's
  `isZero_iff_forall_isZero_stalk` is applied on `O`.
- `isClosed_stalkSupport_of_hasFiniteClosedSupport`: a finite stalk support of closed
  points is closed.
- `stalkSupport_twist_subset`: under `hW`, the support of `Rⁿ p_*(F ⊗ p^* W)` is contained
  in the support of `Rⁿ p_* F`, if the latter is finite and closed. Proof: let `y` lie outside
  the support of `Rⁿ p_* F`. Choose a free chart `V ∋ y` and intersect it with the open
  complement of that support. On the result `V'`, `Rⁿ p_* F` restricts to zero, so by
  `twistRestrictIso` the restriction of `Rⁿ p_*(F ⊗ p^* W)` is a coproduct of zero objects,
  and its stalk at `y` vanishes.
- `finrank_cohomology_twist`: let `p`, `s : Y ⟶ Spec K` (`K` a field), `F`, `W`, `d` satisfy
  `hW`, and let every `R^q p_* F` have finite closed support. If `Hⁿ(Z, F)` along `p ≫ s` is
  finite dimensional, then so is `Hⁿ(Z, F ⊗ p^* W)`, and its dimension is `d` times that of
  `Hⁿ(Z, F)`.
- `eulerCharacteristic_twist`: under the same hypotheses, if `F` has finite cohomology along
  `p ≫ s`, then `F ⊗ p^* W` has finite cohomology, and for every finite-cohomology proof,
  `χ(F ⊗ p^* W) = d · χ(F)`.

## Proof of `finrank_cohomology_twist`

By `stalkSupport_twist_subset`, every `R^q p_*(F ⊗ p^* W)` has finite closed support. The
Library's `finiteClosedSupportLeray` then gives `Hⁿ(Z, F) ≅ Γ(Y, Rⁿ p_* F)` and
`Hⁿ(Z, F ⊗ p^* W) ≅ Γ(Y, Rⁿ p_*(F ⊗ p^* W))` as `K`-modules. Let `S` be the finite support
of `G = Rⁿ p_* F`; it also contains the support of `G' = Rⁿ p_*(F ⊗ p^* W)`. For each `x`,
choose a free chart `V₀ x` of `W` and set `V x = V₀ x ∩ (Y \ (S \ {x}))`. This open contains
`x`, meets `S` only in `x`, and carries a free chart of `W` (`restrictFreeOfLE`).
`sectionsRestrictPi_bijective` (module `FiniteSupportSectionsDecomposition`) gives `K`-linear
equivalences `Γ(Y, G) ≃ Π_{x ∈ S} Γ(V x, G)` and `Γ(Y, G') ≃ Π_{x ∈ S} Γ(V x, G')`. On each
`V x`, `twistRestrictIso` and `relativeGlobalSectionsCoproductIso` give
`Γ(V x, G') ≃ (Fin d → Γ(V x, G))`. Each `Γ(V x, G)` is finite dimensional, being the image of
the finite-dimensional `Γ(Y, G)` under a coordinate projection. Hence
`Hⁿ(Z, F ⊗ p^* W) ≃ Π_{x ∈ S} (Fin d → Γ(V x, G))` is finite dimensional, of dimension
`Σ_x d · dim Γ(V x, G) = d · dim Γ(Y, G) = d · dim Hⁿ(Z, F)` (`Module.finrank_pi_fintype`).

## Proof of `eulerCharacteristic_twist`

Apply `finrank_cohomology_twist` in every degree. If `Hⁿ(Z, F) = 0` for `n ≥ N`, then
`Hⁿ(Z, F ⊗ p^* W)` is finite dimensional of dimension `d · 0 = 0`, hence zero. So
`F ⊗ p^* W` has finite cohomology. The Library cutoff formula
`eulerCharacteristic_eq_sum_range` writes both Euler characteristics as sums over `n < N`,
and the summands differ by the factor `d`.

The module uses only Mathlib and published Library results, and its axioms are `propext`,
`Classical.choice` and `Quot.sound`.
