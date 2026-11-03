# The conjugation coaction of a cocharacter is a grading

Let `R` be a commutative ring and `F` a group-valued functor on commutative
`R`-algebras, corepresented by `B`. Write `G = Spec B` for the affine group
scheme `Corepresented.groupScheme F e`, and let `χ : 𝔾_m → G` be a cocharacter.
[`Representability`](Representability.md) defines the coaction
`c = Corepresented.coaction χ : B → B[T, T⁻¹]`. It is the ring map of the orbit
map `(g, t) ↦ χ(t) g χ(t)⁻¹` of the universal point. This module proves that
`c` is a `ℤ`-grading of the `R`-algebra `B`:

- `Corepresented.coaction_algebraMap`: `c(r · 1) = r · 1` (a constant Laurent
  polynomial) for `r ∈ R`.
- `Corepresented.sum_coeff_coaction`: the coefficients of `c(b)` sum to `b`.
  `Corepresented.coaction_comp_laurentEvalOne` is the same statement as
  `c` followed by evaluation at `T = 1` being the identity.
- `Corepresented.coaction_coeff_coaction`: for every `b` and `n`, writing
  `c(b)ₙ` for the coefficient of `Tⁿ`, `c(c(b)ₙ) = c(b)ₙ Tⁿ`
  (`AddMonoidAlgebra.single n (c(b)ₙ)`). Its ring-map form
  `Corepresented.coaction_comp_laurentCoeffMap_coaction` is
  `(c ⊗ id) ∘ c = (id ⊗ Δ) ∘ c`, with `Δ(U) = S T`.

These are the counit and coassociativity axioms of a coaction of the Hopf
algebra `R[T, T⁻¹]`. Coassociativity gives `c(b)ₘ` homogeneous of degree `m`,
and the counit axiom gives `b = ∑ₘ c(b)ₘ`.

## Provenance and implementation

This is internal infrastructure for the proof of `DynamicSmoothStatement`. It
makes no claim from the literature beyond the standard fact that a
`𝔾_m`-action on an affine scheme is a `ℤ`-grading of its coordinate ring.

Group-scheme identities (namespace `Langlands.GroupScheme.Dynamic`, any base
scheme `S`):

- `orbit_orbit`: on `(T ×_S 𝔾_m) ×_S 𝔾_m`, the orbit map of the orbit map of
  `g` is the orbit map of `g` precomposed with `((x, s), t) ↦ (x, t s)`. The
  proof unfolds `orbit` and uses that `χ` is a monoid morphism
  (`MonObj.mul_comp`), then closes the group identity with `group`.
- `lift_one_comp_orbit`: the orbit map of `g` at `(x, 1)` is `g`.

Laurent-polynomial points (namespace `Langlands.GroupScheme.AffineLine`), for
`f : Spec A → S`:

- `laurentEvalOne A` is evaluation at `1`, `A[X, X⁻¹] → A`, and
  `laurentOne f : Spec A → Spec A[X, X⁻¹]` is its spectrum over `S`.
  `laurentOne_comp_laurentPoint` says that the Laurent point `(x, X)` composed
  with `laurentOne f` is `(x, 1)`. The first component is a ring identity; the
  second is checked on global units through `Gm.pointsEquiv`.
- `laurentMulRingHom A : A[U, U⁻¹] → A[S, S⁻¹][T, T⁻¹]` fixes `A` and sends
  `U` to `S T`. It is built by `AddMonoidAlgebra.liftNCRingHom` from
  `m ↦ Tᵐ Sᵐ`. `laurentMulRingHom_single` gives `a Uᵐ ↦ (a Sᵐ) Tᵐ`.
  `coeff_laurentMulRingHom` gives the `Tⁿ`-coefficient of the image of `q` as
  `qₙ Sⁿ`, by induction over `q`.
- `laurentMulHom f` is the spectrum of `laurentMulRingHom A`, a morphism over
  `S`. `laurentMulHom_comp_laurentPoint` identifies it, followed by the
  Laurent point, with the iterated Laurent point followed by multiplication
  in `𝔾_m`. First components agree by a ring identity. Second components are
  compared through `Gm.pointsEquiv`, where both sides are the unit `S T`.

The three coaction statements are then proved as follows.

- Compatibility with `R` follows from `algebraMap_comp_pointRing` applied to
  the orbit map of the universal point, which is a morphism over `Spec R`.
- For the counit, compose the orbit map of the universal point with
  `laurentOne`. By `laurentOne_comp_laurentPoint` and `lift_one_comp_orbit`
  this composite is the universal point. So `Spec` of (`c` followed by
  evaluation at `1`) is the identity, and `Spec` is faithful.
  `eval₂_id_one` rewrites evaluation at `1` as the sum of the coefficients.
- For coassociativity, apply `laurentPoint_comp_orbit_left` to the orbit map
  of the universal point itself, a point over `Spec B[S, S⁻¹]` classified by
  `c`. Its orbit map over `Spec B[S, S⁻¹][T, T⁻¹]` is then classified by
  `(c ⊗ id) ∘ c`. On the other hand, by `whiskerRight_orbit`, `orbit_orbit`
  and `laurentMulHom_comp_laurentPoint`, the same morphism is `laurentMulHom`
  followed by the orbit map of the universal point. That composite is
  classified by `laurentMulRingHom ∘ c`. Comparing `Tⁿ`-coefficients by
  `coeff_laurentCoeffMap` and `coeff_laurentMulRingHom` gives
  `c(c(b)ₙ) = c(b)ₙ Sⁿ`.
