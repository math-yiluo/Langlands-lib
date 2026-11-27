# Covering simple-character classes: the scalar condition on fibre characters

This module proves `FibreCharacterAt` (stated in `ClassCoverSurj`) from
`SimpleCharacterChoiceStatement`, for a finite-dimensional `V` and an additive character `ψ_F` of
`F` that is trivial on `𝔭_F` and nontrivial on `𝔬_F` (`IsBKAdditiveCharacter`). Let `[𝔄,n,k+1,γ]` be
a simple stratum on `L`. Two pairs of `Ĉ(𝔄,k,γ)` with the same restriction to `U^{k+2}(𝔄)` have the
same subgroup and differ by `ψ_e`, where `e ∈ 𝔓^{-(k+1)}` and every tame corestriction relative to
`F[γ]/F` carries `e` to a scalar of `F[γ]` modulo `𝔓^{-k}` (`CorestrictionScalarMod`). The condition
on `ψ_F` is essential, since for trivial `ψ_F` every `ψ_e` is trivial.

This is an auxiliary result about the quotient of two extensions, used in the proof of
Lemma (2.7) of Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994),
printed p. 121. Its first part, the existence of `e`, corresponds to the remark on p. 120 that
each `θ ∈ Y^m(θ₀)` has the form `ϑ ψ_c` with `c ∈ 𝔓^{-(m+1)}`. Its scalar condition corresponds
to the step of the proof of (2.7) in which the quotient `ϑ'ϑ⁻¹` of two extensions of `θ₀` is
shown to be `ψ_{B_γ,δ}` on `U^{m+1}(𝔅_γ)` for a scalar `δ ∈ F[γ]`. The conclusion of (2.7)
itself, that the derived stratum `[𝔅_γ,m+1,m,s_γ(c)]` is null or equivalent to a simple stratum,
is not stated in this module. The reduction combines the scalar condition with the derived
stratum of a simple refinement in `refinementSimpleAt` (module `ClassCoverRefine`).

## Tame corestrictions

Let `E` be an intermediate field acting on `V`, with `E^×` normalizing the chain `L`, and let
`s : A → B = End_E(V)` be a tame corestriction (Bushnell and Kutzko, *The admissible dual of
GL(N) via compact open subgroups* (1993), (1.3.3)).

* `tameCorestriction_surjective` and `tameCorestriction_mem` follow from the image clause of the
  Library's `tameCorestriction` (BK93 (1.3.4)): `s(𝔓^j(𝔄)) = 𝔓^j(𝔄) ∩ B`.
* `TameCorestriction.apply_mul_left`, `apply_mul_right`, `apply_add`, `apply_sub`,
  `apply_zero`, `tameCorestriction_smul`: `s` is a homomorphism of `B`-bimodules and commutes
  with the scalars of `F`.
* `tameCorestriction_adjoint`: `s(cx - xc) = 0` for `c ∈ E`.
* `trace_eq_zero_of_tameCorestriction`: for finite-dimensional `V` and `E = F[γ]` a field,
  every element of the kernel of `s` has
  trace `0`. If `γ` is a scalar, `s` is injective
  (`mem_endFiltration_of_tameCorestriction_scalar`). Otherwise, after multiplying by a power of
  a uniformizer, the exactness clause of the Library's `adjointExactness` (BK93 (1.4.10)) writes
  the element as `γx - xγ`, which has trace `0`.
* `corestrictedTrace ψF s` is the function `w ↦ ψ_A(a)` for any `a` with `s a = w`;
  `corestrictedTrace_apply` shows it is well defined when the kernel of `s` has trace `0`. It is
  the character `ψ_B` of BK94 p. 121, defined by `ψ_B ∘ s = ψ_A`.
* `relativeEndUnits_mem_unitFiltration`: a unit of `B` in `U^m` of a chain over `E` whose
  lattices have the same underlying sets as those of `L` at every index lies in `U^m(𝔄)`.

## The scalar condition

`corestrictionScalarMod_of_det`. Let `V` be finite-dimensional, fix an additive character `ψ_F` of
`F` that is trivial on `𝔭_F` and nontrivial on `𝔬_F` (`IsBKAdditiveCharacter`), and write
`ψ_A = ψ_F ∘ tr` and `ψ_e(x) = ψ_A(e(x - 1))`. Let `γ, e ∈ A` and assume that, whenever `F[γ]` is a
field, its units normalize `L`. Suppose that, whenever `F[γ]` is a field, for units `x, x'` of
`B = End_{F[γ]}(V)` lying in `U^{k+1}(𝔄)`, `det_{F[γ]} x = det_{F[γ]} x'` implies
`ψ_e(x) = ψ_e(x')`. Then `CorestrictionScalarMod L γ e k` holds. The condition on `ψ_F` enters
through the duality `mem_dual_centralizerLattice_iff`; for trivial `ψ_F` the hypothesis holds for
every `e`, but the conclusion can fail.

Proof. Let `ℓ = corestrictedTrace ψF s` on `B`. It is additive-to-multiplicative because `s` is
surjective, and it satisfies `ℓ(ab) = ℓ(ba)` because `s` is a bimodule map and the trace is
cyclic (`traceCharacter_mul_comm`). The field `F[γ]` is a nonarchimedean local field, and the
lattices of `L` form a chain `C` over its ring of integers (`LatticeChain.extensionChain`
transferred along `subfieldIntegerEquiv`). By `ψ_A(e(x - 1)) = ℓ(s(e)(x - 1))`, the hypothesis
is the determinant condition of `exists_scalar_of_det_invariant` (module `ClassCoverDet`) for
`z = s(e)` on `C`. That lemma gives a scalar `δ` with `ℓ((s(e) - δ) y) = 1` for every
`y ∈ 𝔓^{k+1}(𝔄) ∩ B`. Choose `a` with `s a = s(e) - δ`. Then `ψ_A(a y) = 1` for every `y` in
`𝔓^{k+1}(𝔄) ∩ B`, so `a ∈ 𝔓^{-k}(𝔄) + a_γ(A)` by the Library's `mem_dual_centralizerLattice_iff`.
Since `s` kills `a_γ(A)` and maps `𝔓^{-k}(𝔄)` into itself, `s(e) - δ ∈ 𝔓^{-k}(𝔄)`.

## The fibre characters

* `simpleCharacters_factorsThroughCentralizerDet`: below the critical depth of `β`, a simple
  character of `H^{m+1}(β,𝔄)` factors through the determinant of the centralizer `B_β` on
  `H^{m+1}(β,𝔄) ∩ B_β^×`. This is a clause of the definition of `simpleCharacters` (BK93
  (3.2.1)(b), (3.2.3)(a)).
* `CharacterPair.apply_eq_of_eq`: equal pairs have equal values.
* `fibreCharacterAt` proves `FibreCharacterAt ψF L n k` from `SimpleCharacterChoiceStatement`, for
  finite-dimensional `V` and `ψ_F` trivial on `𝔭_F` and nontrivial on `𝔬_F`. Let `ϑ, ϑ' ∈ Ĉ(𝔄,k,γ)`
  have the same restriction to `U^{k+2}(𝔄)`. One defining sequence computes `Ĉ(𝔄,k,γ)`
  (`simpleCharacterPairs_eq_choiceImage_of_le`), so both pairs have the subgroup `H = H^{k+1}(γ,𝔄)`,
  with characters `θ, θ'` from the same set of simple characters. The character `χ = θ' θ⁻¹` of
  `H ≤ U^{k+1}(𝔄)` is trivial on `H ∩ U^{k+2}(𝔄)`, so `χ = ψ_e` on `H` with `e ∈ 𝔓^{-(k+1)}`
  (`exists_elementCharacter_of_trivial_succ`, module `ClassCoverFibreChar`). Since `[𝔄,n,k+1,γ]` is
  simple, `k` is below the critical depth of `γ`, so `θ` and `θ'` factor through `det_{F[γ]}` on
  `H ∩ B_γ^×`. The relative units of `B_γ` in `U^{k+1}(𝔄)` lie in `H`
  (`relativeUnitFiltration_le_simpleHGroup`), so `ψ_e = θ' θ⁻¹` depends only on `det_{F[γ]}` there,
  and `corestrictionScalarMod_of_det` gives the scalar condition.

## Comparison with the source

In BK94's proof of (2.7), the restriction of `θ'θ⁻¹` to `U^{k+1}(𝔅_γ)` is `ψ_{B_γ,δ}` with
`δ ∈ 𝔓^{-(k+1)} ∩ B_γ = 𝔔^{-(k+1)}`, where `𝔔` is the radical of `𝔅_γ`. This character is
intertwined by every element of `B_γ^×`, hence so is the coset `δ + 𝔔^{-k}`, and the coset clause
of BK93 (2.4.11), applied in `B_γ` with the order `𝔅_γ` and the group `B_γ^×`, shows that this
coset meets the centre `F[γ]`; so `δ` can be taken in `F[γ]`. Here the intertwining argument is
not used. The hypothesis is
instead that `ψ_e` depends only on `det_{F[γ]}`, which follows from the determinant
factorization of simple characters, and `exists_scalar_of_det_invariant` (module
`ClassCoverDet`) derives the scalar from that hypothesis by an elementary-matrix computation.
