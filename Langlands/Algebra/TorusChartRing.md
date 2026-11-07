# Ring-level data of a torus chart

Author: Worker 1421.

This is an internal module for the chart construction of task
`45ac6e52-a4d8-4414-91f1-03c3be35223e`. It sets up the algebra of one chart of
the moduli of closed tori. Fix `R`, a finitely presented `R`-Hopf algebra `A`
(the coordinates of the ambient group), a finite index type `r` and `m > 0`.
`W = W R A r m` is the algebra representing homomorphisms `μ_m^r → Spec A`
(`TorusChartAlgebra.W`), and `pointOf g` is the Hopf point `A → C[(ℤ/m)^r]`
classified by a point `g : W → C`.

## The twisting group

- `Γ r m := Multiplicative (AddAut ((ℤ/m)^r))`, the group of automorphisms of
  `(ℤ/m)^r`, and `act : Γ r m →* (W ≃ₐ[R] W)`, Worker 1421's
  `HopfPointTwist.twistAction`. `act_toAlgHom`: `act γ` is
  `twistHom γ⁻¹`.
- An instance: `Γ r m` is finite, since `AddAut ((ℤ/m)^r)` embeds into the
  finite set of self-maps of `(ℤ/m)^r`.
- `pointOf_comp`: `pointOf (h ∘ g) = mapAlgHom h ∘ pointOf g`.
- `pointOf_comp_act`: `pointOf (g ∘ act γ) = mapDomain γ⁻¹ ∘ pointOf g`.
- `pointOf_injective`: over `C` in universe `u`, a point of `W` is determined
  by its Hopf point. This uses `univ_point` and the bijection `homEquiv`.

## Scalar extensions

- `surjective_scalarExt_mapDomain`: pushing a Hopf point forward along a
  surjection of character groups preserves surjectivity of the scalar
  extension (`scalarExt`).
- `ker_scalarExt_mapDomain_addEquiv₂`: pushing forward along an isomorphism
  of character groups does not change the kernel of the scalar extension.
- `support_mapAlgHom_subset`: changing coefficients does not enlarge supports.
- Tensor form. `scalarExt_toGroupAlgebra` identifies the scalar extension of
  the group-algebra form `toGroupAlgebra f` with Mathlib's `AlgHom.liftEquiv`
  of `f : A → C ⊗[R] R[M]`, followed by `C ⊗[R] R[M] ≅ C[M]`. Consequences:
  `ker_liftEquiv` and `surjective_liftEquiv_iff`. The converse direction is
  `ofGroupAlgebra α`, with `toGroupAlgebra_ofGroupAlgebra` and
  `isHopfPoint_ofGroupAlgebra`.

## Chart data

`Datum R A r m gen n`, for generators `gen : σ' → A` and a box size `n`,
records the following:

- `bound`: `rigidityBound r n ≤ m` (Worker 1421's `HopfPointRigidity`).
- `adjoin_gen`: the elements `gen i` generate `A`.
- An element `f ∈ W` and a Hopf point
  `α : A →ₐ[R] (W_f)[ℤ^r]` (`isHopfPoint`) such that:
  - the weights of every `gen i` lie in `box r n` (`support`);
  - its reduction modulo `m` is the universal point of `μ_m^r` over `W_f`
    (`red_comp`);
  - it is a closed immersion, i.e. its scalar extension is surjective
    (`surjective`).
- An element `N ∈ W` fixed by every `act γ` (`invariant`), such that every
  prime not containing `N` misses some translate `act γ f` (`cover`).

Thus `α` is a torus `G_m^r → Spec A` over `D(f)` extending the universal
`μ_m^r`. The translates of `D(f)` cover the invariant principal open `D(N)`.

For a datum `d`:

- `B := W_N`, with the induced `Γ`-action `actB` (from
  `InvariantPrincipalOpen.awayAction`), `actB_algebraMap`,
  `actB_algebraMap_R`, and the `R`-algebra form `actBAlg`.
- `exists_lift`: a point `g` of `W` with `g f` a unit factors through `W_f`.
- `surjective_pointOf_of_isUnit`: at such a point, `pointOf g` is a closed
  immersion. Factor through `W_f` and rewrite with `red_comp`. Reduction
  modulo `m` is surjective, and change of coefficients preserves surjectivity.
- `surjective_pointOf_of_field`: at a field point `g` with `g N ≠ 0`,
  `pointOf g` is a closed immersion. By `cover`, some translate `g ∘ act γ`
  has `f` invertible. Untwist by `γ` using `surjective_scalarExt_mapDomain`.
- `actB_free`: the action on `B` is free on field points. If
  `φ ∘ actB γ = φ ∘ actB δ` for a field-valued `φ`, then `γ = δ`. The induced
  point of `W` is a closed immersion by `surjective_pointOf_of_field`, so
  `TorusChartAlgebra.twist_injective_of_surjective` applies.
- `pushα u := mapAlgHom u ∘ α`, for `u : W_f →ₐ[R] C`, with
  `isHopfPoint_pushα`, `support_pushα`, `surjective_pushα`,
  `red_comp_pushα` (its reduction is `pointOf (u ∘ (W → W_f))`), and
  `mapAlgHom_comp_pushα`.
- `ker_pushα_eq` (rigidity on overlaps): suppose two points `u₁, u₂` of `W_f`
  induce points of `W` that differ by `act γ`. Then the scalar extensions of
  `pushα u₁` and `pushα u₂` have the same kernel. Over the zero ring this is
  trivial. Otherwise the supports generate `ℤ^r`
  (`HopfPointRigidity.closure_support_eq_top`), and
  `HopfPointKernel.ker_scalarExt_eq_of_red_eq` applies to the reductions,
  which differ by `γ⁻¹`.
- `exists_act_of_ker_eq` (injectivity on overlaps): conversely, suppose the
  two kernels agree. Then after localizing `C` at any maximal ideal `P`, the
  two induced points of `W` differ by some `act γ`.
  `HopfPointConnected.exists_addEquiv_localization` gives an automorphism `T`
  of `ℤ^r` relating the two localized extensions.
  `LatticeConfiguration.exists_red_equiv` reduces `T` to an automorphism `Tb`
  of `(ℤ/m)^r`. With `γ := Tb⁻¹`, the claim follows from `pointOf_injective`
  and `red_comp_pushα`.
