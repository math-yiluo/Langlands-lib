# Hopf points with the same kernel over a connected ring

Author: Worker 1421.

This is an internal module for the chart construction of task
`45ac6e52-a4d8-4414-91f1-03c3be35223e`. Let `A` be an `R`-bialgebra, `D` an
`R`-algebra and `M`, `N` abelian groups. Consider two closed-immersion Hopf
points `α : A → D[M]` and `β : A → D[N]` (`HopfPointExtension.IsHopfPoint`
with surjective `scalarExt`). These are two closed embeddings of the split
diagonalizable groups `D(M)` and `D(N)` into `Spec A` over `Spec D`. If they
have the same image (the same kernel of the scalar extension), then locally at
every prime of `D` they differ by an isomorphism `M ≅ N`. The argument: an
isomorphism of group algebras compatible with both embeddings is a Hopf map,
so it sends group-likes to group-likes. Over a ring without nontrivial
idempotents, the group-likes are exactly the monomials.

## Group-likes

- `coeff_diagMap`: the `(ψ, ψ')`-coefficient of `diagMap y` is `y_ψ` if
  `ψ = ψ'`, and `0` otherwise.
- `groupCounit_apply`: the counit sends `y` to the sum of its coefficients.
- `exists_eq_single_of_grouplike`: let `D` be nonzero with only the idempotents
  `0` and `1`. If `diagMap y = inl y · inr y` and the counit of `y` is `1`,
  then `y = single χ 1` for some `χ`. Comparing coefficients gives
  `y_ψ y_ψ' = δ_{ψψ'} y_ψ`. So each coefficient is an idempotent, hence `0` or
  `1`, and distinct nonzero coefficients would have product `0`. The counit
  condition forces some coefficient to be nonzero.
- `inlMap_smul`, `inrMap_smul`, `diagMap_smul`, `groupCounit_smul`:
  `D`-linearity of these maps.

## Maps intertwining two Hopf points

Fix a `D`-algebra map `τ : D[M] → D[N]`.

- `square τ : D[M × M] → D[N × N]` sends `single (a, b) c` to
  `c · inl (τ (single a 1)) · inr (τ (single b 1))` (`square_single`).
  Also `tau_single`, `square_inlMap`, `square_inrMap`, and `square_pairMap`:
  if `τ ∘ α = β`, then `square τ ∘ pairMap α = pairMap β`.
- `tau_scalarExt`: if `τ ∘ α = β`, then `τ ∘ scalarExt α = scalarExt β`.
- `diagMap_tau` and `groupCounit_tau`: suppose `α` and `β` are Hopf points,
  `scalarExt α` is surjective and `τ ∘ α = β`. Then `τ` commutes with the
  comultiplications (through `square τ`) and with the counits. Write `y` as
  `scalarExt α x` and use the Hopf conditions of `α` and `β`.
- `exists_tau_single`: under the same hypotheses, over a nonzero ring with
  only trivial idempotents, `τ` sends each `single χ 1` to some `single ψ 1`.
  The image is group-like by `diagMap_tau` and `groupCounit_tau`, so
  `exists_eq_single_of_grouplike` applies.
- `exists_addEquiv_of_comp`: over such a ring, suppose `α` and `β` are
  closed-immersion Hopf points and `τ ∘ α = β`, `τ' ∘ β = α`. Then some
  `T : M ≃+ N` satisfies `mapDomain T ∘ α = β`. By `exists_tau_single`, `τ`
  and `τ'` act on monomials through maps `T` and `T'`. They are mutually
  inverse because `τ' ∘ τ = id` on the image of `scalarExt α`, which is
  everything, and similarly in the other order. `T` is additive because `τ`
  is multiplicative.

## Localization

- `isIdempotentElem_eq_zero_or_one_of_isLocalRing`: a local ring has only the
  idempotents `0` and `1`.
- `exists_tau_of_ker_le`: if `scalarExt α` is surjective and its kernel is
  contained in that of `scalarExt β`, then some `τ` has `τ ∘ α = β`.
  `AlgHom.liftOfSurjective` provides it.
- `mapAlgHom_smul`, `exists_baseChange_tau`: a map `τ : D[M] → D[N]` induces a
  map `E[M] → E[N]` along any change of coefficients `ψ : D → E`, compatible
  with `mapAlgHom ψ`.
- `exists_addEquiv_localization`: if two closed-immersion Hopf points `α`
  and `β` have scalar extensions with the same kernel, then for every prime
  `P` of `D` some `T : M ≃+ N` relates them after localizing at `P`. Use
  `exists_tau_of_ker_le` in both directions, base change the two maps to
  `D_P`, and apply `exists_addEquiv_of_comp` there. The localized points are
  still closed-immersion Hopf points
  (`HopfPointClosedLocus.surjective_scalarExt_mapAlgHom`).
