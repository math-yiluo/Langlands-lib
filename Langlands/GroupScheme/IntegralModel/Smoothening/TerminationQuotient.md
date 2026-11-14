# Termination of the smoothening sequence: the closure of the reduced points is smooth

Author: Worker 348. Internal helper module for Kaletha–Prasad, Theorem A.6.2. In the source, the
dilatation at step `i` is taken along the Zariski closure `Y(i)` of the reductions of the
`R`-points in the special fibre. Over an algebraically closed residue field, `Y(i)` is a reduced,
hence smooth, closed subgroup (Construction A.6.1). This module proves the ring-theoretic form of
that statement. The argument is internal to this project.

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`.

Setting: `R` is a local ring with residue field `k`, `C` is a commutative Hopf algebra over `R`,
and `Γ` is a set of `R`-points of `C`. `evPt` is defined in `TerminationGamma`.

## The ideal of the reduced points

- `jbar Γ` is the ideal of `k ⊗[R] C` of functions vanishing at the reductions of all points of
  `Γ`, namely the intersection of the kernels of `evPt φ` (`mem_jbar`).
- `counit_eq_evPt`: the counit of `k ⊗ C` is evaluation at the reduction of the counit of `C`.
- `lid_map_evPt_comul`: `(evPt φ ⊗ evPt ψ) ∘ Δ` is `evPt` of the product point
  `(φ ⊗ ψ) ∘ Δ_C`.
- `evPt_antipode`: `evPt φ ∘ S = evPt (φ ∘ S_C)`.
- `quotEv Γ` gives the forms on `(k ⊗ C) ⧸ jbar Γ` induced by the points.
  `quotEv_detects`: they detect zero.
- `isHopfIdeal_jbar`: suppose `Γ` contains the counit (`h1`), is closed under products of points
  (`h2`) and is closed under composition with the antipode (`h3`). Then `jbar Γ` is a Hopf ideal
  (Mathlib's `Ideal.IsHopfIdeal`). The comultiplication condition uses `detects_tensor` for the
  forms `quotEv`.
- `jbar_isRadical`: `jbar Γ` is radical, being an intersection of kernels of maps to a field.
- `smooth_quotient_jbar`: if moreover `k` is algebraically closed and `C` is finitely generated,
  then `(k ⊗ C) ⧸ jbar Γ` is smooth over `k`. It is a reduced, finitely generated, commutative
  Hopf algebra (Mathlib's Hopf quotient structure), so Worker 50's
  `smooth_of_isReduced_of_isAlgClosed` applies.

## The comparison with `C`

- `ptLocus Γ` is the ideal of `c ∈ C` with `φ c ∈ 𝔪` for every `φ ∈ Γ` (`mem_ptLocus`). It only
  needs an algebra structure.
- `quotMap Γ : C →ₐ[R] (k ⊗ C) ⧸ jbar Γ` is `c ↦ [1 ⊗ c]` (`quotMap_apply`). It is surjective
  (`quotMap_surjective`) with kernel `ptLocus Γ` (`ker_quotMap`).
- `quotPoint h1` is the `k`-point of the quotient induced by the counit.
  `quotPoint_quotMap`: it sends `quotMap c` to the residue of `ε c`.

These are the inputs of `gradedIndep_of_formallySmooth` (`TerminationPsi`) in `TerminationCore`.
