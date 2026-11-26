# Arithmetic pullback of conjugate-contragredient pairings

Module `Langlands.Automorphic.ConjugateContragredientArithmeticTransport`. Proved lemmas
only; no new definitions.

## Setting

The module `Langlands.Automorphic.ConjugateContragredient` defines, for an actual
operator realization `S` of `GL_n` over a CM field, the contragredient functionals
(`IsContragredientFunctional`: algebraic functionals smooth for the finite adelic group
and finite for the standard compact subgroup at infinity), conjugate-contragredient
pairings (`IsConjugateContragredientPairing`: a bilinear pairing `B` invariant under the
finite, compact and Lie algebra operators twisted by the CM involution in the first
variable, whose partial map `x ↦ B (·) x` is a bijection onto the contragredient
functionals) and conjugate self-duality (`IsConjugateSelfDual`: some such pairing
exists), for realizations, full-operator classes and irreducible cuspidal classes.

For a ring isomorphism `e : K ≃+* L` of number fields and a realization `S` over `L`,
`S.arithmeticComap e` is the arithmetic pullback over `K` and
`φ = S.arithmeticComapEquiv e : S.Space ≃L[ℂ] (S.arithmeticComap e).Space` the linear
equivalence between them (module `Langlands.Automorphic.OperatorArithmeticTransport`).
By `arithmeticComapEquiv_symm_finite`, `arithmeticComapEquiv_symm_compact` and
`arithmeticComapEquiv_symm_differential`, `φ⁻¹` carries the action of `d`, `k` or `u` on
the pullback to the action of `finiteEquiv n e d`, `compactEquiv n e k` or
`envelopingEquiv n e u` on `S`. The fields `K : Type uK`, `L : Type uL` have independent
universes.

## General lemmas on dual actions

Let `ρ` be a representation of a group `G` on `V`, `τ` a representation of a group `H` on
`W` over a field `k`, `α : H →* G` a homomorphism and `ψ : W →ₗ[k] V` a linear map with
`ψ (τ h w) = ρ (α h) (ψ w)`. For a functional `l` on `V`:

- `dual_apply_comp_of_intertwining`: `τ.dual h (l ∘ ψ) = (ρ.dual (α h) l) ∘ ψ`, since the
  dual action is `l ↦ l ∘ ρ g⁻¹` and `α` preserves inverses.
- `isSmoothVector_dual_comp_of_intertwining`: if `G`, `H` are topological groups, `α` is
  continuous and `l` is a smooth vector of `ρ.dual`, fixed by an open subgroup `U` of
  `G`, then `l ∘ ψ` is a smooth vector of `τ.dual`, fixed by the open subgroup
  `α⁻¹(U)` (Mathlib's `OpenSubgroup.comap`).
- `isFiniteVector_dual_comp_of_intertwining`: if the orbit span of `l` under `ρ.dual` is
  finite-dimensional, so is the orbit span of `l ∘ ψ` under `τ.dual`, because it lies in
  the image of the former under `l ↦ l ∘ ψ`.

## Results for operator realizations

For `e : K ≃+* L` and a realization `S` over `L`:

- `arithmeticComapEquiv_symm_lieAction`: `φ⁻¹` carries the action of a real Lie algebra
  element `X` on the pullback to the action of `realLieEquiv n e X` on `S`. The proof
  combines `arithmeticComapEquiv_symm_differential` with the published
  `envelopingEquiv_generator` and `complexLieEquiv_complexify`.
- `isContragredientFunctional_comp_arithmeticComapEquiv_symm`: if `l` is a contragredient
  functional of `S`, then `l ∘ φ⁻¹` is one of `S.arithmeticComap e`. This is the general
  lemmas with `ψ = φ⁻¹` and `α` equal to `finiteEquiv n e` (continuous) for smoothness and
  to `compactEquiv n e` for finiteness.
- `isContragredientFunctional_comp_arithmeticComapEquiv`: if `l` is a contragredient
  functional of `S.arithmeticComap e`, then `l ∘ φ` is one of `S`. This is the general
  lemmas with `ψ = φ` and `α` equal to the inverses of `finiteEquiv n e` and
  `compactEquiv n e`; the intertwining identity comes from
  `arithmeticComapEquiv_finite` and `arithmeticComapEquiv_compact` at `α⁻¹ d`.

Together the last two say that `l ↦ l ∘ φ⁻¹` is a bijection from the contragredient
functionals of `S` onto those of the pullback.

Now let `K` and `L` be CM fields, and let `B` be a pairing on `S` and
`B' y x = B (φ⁻¹ y) (φ⁻¹ x)` (in Lean, `B.compl₁₂ φ⁻¹ φ⁻¹`).

- `arithmeticComap_conjugateInvariant_finite`, `arithmeticComap_conjugateInvariant_compact`
  and `arithmeticComap_conjugateInvariant_lie`: if `B` satisfies the finite, compact or
  Lie algebra identity of `IsConjugateInvariantPairing` over `L`, then `B'` satisfies it
  over `K`. For the finite identity, `φ⁻¹` turns `π'(finiteConj K n d)` into
  `π(finiteEquiv n e (finiteConj K n d))`, which equals `π(finiteConj L n (finiteEquiv n e d))`
  by `CMConjugation.finiteEquiv_finiteConj` (module
  `Langlands.Global.CMConjugationArithmeticTransport`). It also turns `π'(d)` into
  `π(finiteEquiv n e d)`, so the identity for `B'` at `d` is the identity for `B` at
  `finiteEquiv n e d`. The compact and Lie algebra identities follow in the same way from
  `compactEquiv_compactConj` and `realLieEquiv_lieConj`.
- `OperatorRealization.IsConjugateSelfDual.arithmeticComap`: if `S` is conjugate
  self-dual, so is `S.arithmeticComap e`. If `B` is a conjugate-contragredient pairing
  of `S`, then `B'` is one of the pullback:
  1. invariance: the three lemmas above;
  2. `B'.flip x = B.flip (φ⁻¹ x) ∘ φ⁻¹` is a contragredient functional by
     `isContragredientFunctional_comp_arithmeticComapEquiv_symm`;
  3. injectivity of `B'.flip`: if `B'.flip x₁ = B'.flip x₂`, evaluating at `φ y` gives
     `B.flip (φ⁻¹ x₁) = B.flip (φ⁻¹ x₂)`, so `φ⁻¹ x₁ = φ⁻¹ x₂` by injectivity of
     `B.flip`, and `x₁ = x₂`;
  4. surjectivity: for a contragredient functional `l` of the pullback, `l ∘ φ` is one
     of `S` by `isContragredientFunctional_comp_arithmeticComapEquiv`, so
     `l ∘ φ = B.flip x` for some `x`, and then `B'.flip (φ x) = l`.
- `OperatorRealization.IsoClass.IsConjugateSelfDual.arithmeticComap`: the same for
  full-operator classes, with representative `S.arithmeticComap e` of
  `IsoClass.arithmeticComap e S.isoClass`.
- `CuspidalOperatorRealization.IsoClass.IsConjugateSelfDual.arithmeticComap`: the same for
  irreducible cuspidal classes, through the published
  `IsoClass.toOperatorClass_arithmeticComap` (module
  `Langlands.Automorphic.OperatorArithmeticTransportClasses`).

## Provenance

These are transport-of-structure results. The argument is the one sketched for
`ArithmeticComapConjugateSelfDualStatement` in
`Langlands/Automorphic/CuspidalArithmeticTransportStatement.md`. It is the analogue
across a field isomorphism of `OperatorRealization.IsConjugateSelfDual.of_equivalence`
in `Langlands.Automorphic.ConjugateContragredient`, where the two realizations are over
the same field. Here the groups acting on the two sides differ, and the CM involutions
are compared through `e`.
