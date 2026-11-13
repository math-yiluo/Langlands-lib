# Central endomorphisms of an induced representation through Frobenius reciprocity

This module is an internal helper. It is not stated as such in the literature. It isolates the
formal half of the Lean proof `inducedProgeneratorCenterInclusion` of the centre inclusion for
the induced progenerator (Renard 2026, VI.10.4, the inclusion `ℨ(R_Ω) ⊆ i_P^G(ℨ_D)` in the
second Lemma, printed p. 211, PDF p. 217). Renard proves that Lemma differently, with the free
`ℨ_D`-module structure of `R_Ω` (the first Lemma of VI.10.4) and the generic irreducibility
VI.8.5. The other half of the Lean proof is the vanishing hypothesis below. For the
progenerator `Π_D` it is proved with the geometric lemma in a separate module
(`CuspidalSupport/InducedKernelVanishing`).

## Setting

`G` is a connected reductive group over a non-archimedean local field `k`, with the point
topology on `G(k)`. `P = M N` is a rational parabolic subgroup with rational Levi subgroup `M` and
geometric unipotent radical `N`. `σ` is a smooth complex representation of `M(k)`. We write
`I = leviInductionFunctor` (normalized parabolic induction `i_P^G`) and
`J = leviJacquetFunctor` (normalized Jacquet functor `r_P^G`). For `f ∈ I σ` let `ev f = f(1)`,
and let `mk f` be the class of `f` in the Jacquet module `J(I σ)`.

## Statement

`inducedCenter_eq_of_kernelVanishing` assumes the following kernel vanishing hypothesis. Let
`h : J(I σ) → σ` be an `M(k)`-intertwiner with `h(J(I a) y) = a(h y)` for every `a ∈ End(σ)` and
every `y`. Then `h(mk f) = 0` for every `f ∈ I σ` with `f(1) = 0`.

The conclusion is the set equality of the target statement
`InducedProgeneratorCenterInclusionStatement`, for this `σ`. The centre of `End(I σ)` equals
the set of endomorphisms `x` for which there is a central `z ∈ End(σ)` with `x = I(z)` and `x`
commutes with every element of `End(I σ)`.

## Proof

The inclusion from right to left is immediate: the last condition is the definition of the
centre (`Subring.mem_center_iff`).

For the inclusion from left to right, let `x` be central. Let `e` be the Frobenius reciprocity
bijection `Hom_G(I σ, I σ) ≃ Hom_M(J(I σ), σ)` of `leviFrobeniusReciprocity`, with
`e(F)(mk f) = ev(F f)`.

1. Evaluation at the identity is natural: `ev(I(a) f) = a(ev f)`. This holds by definition.
   The Jacquet functor acts on classes by `J(g)(mk f) = mk(g f)`, also by definition.
2. If an endomorphism `y` of `I σ` commutes with every `I(a)`, then `e(y)` intertwines `J(I a)`
   with `a`. Check it on a class `mk f`: both sides equal `ev(y(I(a) f)) = ev(I(a)(y f))`.
3. Let `h = e(x)` and `ε = e(id)`, so `ε(mk f) = f(1)`. Both satisfy the condition in step 2:
   `x` because it is central, the identity trivially.
4. `ker ε ⊆ ker h`. Write `w = mk f`. Then `ε w = 0` means `f(1) = 0`, and the hypothesis gives
   `h w = 0`.
5. `ε` is surjective, because evaluation at the identity is surjective
   (`normalizedInduction_eval_surjective`, applied with `continuous_projection_pointImage`).
6. Hence there is a unique linear map `c : σ → σ` with `c(ε w) = h w`. In Lean,
   `c = (ker ε).liftQ h ∘ (ε.quotKerEquivOfSurjective)⁻¹`. It is `M(k)`-equivariant, because
   `ε` and `h` are. So it defines an endomorphism `c` of `σ` (`SmoothRep.ofHom`).
7. `c` is central in `End(σ)`. For `a ∈ End(σ)` and `v = ε w`, step 3 gives
   `c(a(ε w)) = c(ε(J(I a) w)) = h(J(I a) w) = a(h w) = a(c(ε w))`.
8. `x = I(c)`. Since `e` is injective, it suffices that `e(x) = e(I(c))`. On a class `mk f`:
   `e(I(c))(mk f) = ev(I(c) f) = c(ev f) = c(ε(mk f)) = h(mk f) = e(x)(mk f)`. The classes
   `mk f` exhaust `J(I σ)`.

So `z = c` witnesses that `x` lies in the right-hand set.
