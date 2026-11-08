# The complex conjugate of an actual cuspidal operator realization

This module shows that pointwise complex conjugation `f ↦ (x ↦ conj (f x))` maps the
constructed stable automorphic form space of `GL_n` over a number field `F` to itself,
and that the image of an actual operator realization is again an operator
realization. Conjugation is an antilinear bijection onto the image. It commutes with
the finite adelic translations, the standard compact translations at infinity and the
real Lie algebra action. It preserves irreducibility and cuspidality, and it replaces
a central character `χ` by its complex conjugate `conj ∘ χ`. In particular a cuspidal
realization with unitary central character has a conjugate with the same properties.

These are standard facts about automorphic forms: the complex conjugate of an
automorphic form is automorphic, and the complex conjugate of a cuspidal automorphic
representation is cuspidal, with conjugate central character. The module does not
follow a particular source. It is an internal helper for the proof of
`CuspidalUnitaryContragredientExistenceStatement`: there the contragredient of a
unitary cuspidal realization `T` is realized on `T.conjugate`, and the pairing is built
from the antilinear equivalence `T.conjugateEquiv` and an invariant inner product.

The archimedean ingredient is the conjugation `envelopingConj` of the complexified
enveloping algebra and the identity
`smoothConj (envelopingAction u f) = envelopingAction (envelopingConj u) (smoothConj f)`
from `Langlands.Global.ArchimedeanEnvelopingConjugation`.

## General semilinear lemmas (namespace `Langlands`)

- `antilinearConjugatedSubrepresentationOrderIso ρ τ α e hc`: let `e : V ≃ₛₗ[conj] W`
  be an antilinear bijection and `α : A ≃* A` a monoid automorphism with
  `τ a (e f) = e (ρ (α a) f)`. Then `P ↦ e(P)` is an order isomorphism from the invariant
  subspaces of `ρ` to those of `τ`, with inverse `Q ↦ e⁻¹(Q)`. The image of a
  `ρ`-invariant subspace is `τ`-invariant by the hypothesis. The preimage of a
  `τ`-invariant subspace is `ρ`-invariant by the hypothesis applied to `α⁻¹ a`. The
  order and inverse properties come from `Submodule.orderIsoMapComap e`.
- `FiniteVectors.IsFiniteVector.antilinear τ C hC hv`: let `C : V →ₛₗ[conj] W` be
  antilinear. Suppose that for every `h` there is a `g` with `τ h (C v) = C (ρ g v)`.
  If `v` has a finite-dimensional orbit span under `ρ`, then `C v` has a
  finite-dimensional orbit span under `τ`. The orbit span of `C v` lies in the image
  under `C` of the orbit span of `v`, which is finitely generated.

## Conjugation of functions (namespace `Langlands.Automorphic`)

- `continuousConj F n`: pointwise conjugation of continuous rational-left-invariant
  functions on `GL_n(𝔸_F)`, an antilinear map. Rational invariance and continuity are
  preserved because conjugation is continuous.
- `evaluate_continuousConj`, `continuousConj_continuousConj`,
  `continuousConj_rightAction`: the value formula, the involution property, and
  commutation with right translation by any adelic element. The last holds by
  definition.
- `continuousConj_mem_infiniteSmooth`, `continuousConj_mem_finiteSmooth`: smoothness at
  infinity (each archimedean slice is smooth) and smoothness at the finite places
  (invariance under an open compact subgroup) are preserved. The first uses
  `ArchimedeanGL.smoothConj` on each slice. The second uses the same subgroup.
- `finiteSmoothConj F n`: the restriction to `FiniteSmoothRationalFunctions F n`, with
  `finiteSmoothConj_val`, `finiteSmoothConj_finiteSmoothConj`,
  `finiteSmoothConj_rightAction` and `finiteSmoothSlice_finiteSmoothConj`.
- `finiteSmoothConj_envelopingAction`:
  `conj (u · f) = envelopingConj u · conj f`. Both sides are compared slice by slice
  (`finiteSmoothSlice_injective`) with `ArchimedeanGL.smoothConj_envelopingAction`.
- `finiteSmoothConj_centerAction`: the same identity for the action of the center,
  with `centerConj`.

## Conjugation of operators

- `finiteSmoothConjEnd F n A = C ∘ A ∘ C` for a complex-linear endomorphism `A` of the
  finite-smooth functions, where `C = finiteSmoothConj`. The result is complex linear.
- `finiteSmoothConjEnd_apply`, `finiteSmoothConjEnd_finiteSmoothConjEnd`,
  `finiteSmoothConjEnd_mul`, `finiteSmoothConjEnd_add`,
  `finiteSmoothConjEnd_algebraMap`: the value formula; `finiteSmoothConjEnd` is an
  involution, multiplicative and additive, and sends the scalar `c` to `conj c`.
- `finiteSmoothConjEnd_finite`, `finiteSmoothConjEnd_compact`: it fixes the finite
  adelic translations and the standard compact translations at infinity, because
  conjugation commutes with right translation.
- `finiteSmoothConjEnd_envelopingAction`: it sends the differential operator of `u` to
  that of `envelopingConj u`.
- `finiteSmoothConjEnd_mem`: it maps the concrete operator algebra
  `automorphicOperatorAlgebra F n` into itself. The proof is induction over
  `Algebra.adjoin`: the generators are mapped to generators by the three previous
  lemmas, scalars to scalars, and sums and products to sums and products.
- `operatorConj F n`: the induced multiplicative involution of
  `automorphicOperatorAlgebra F n`, with `operatorConj_val`,
  `operatorConj_operatorConj`, `operatorConj_finiteOperator`,
  `operatorConj_compactOperator` and `operatorConj_differentialOperator`.

## Conjugation of forms

- `finiteSmoothConj_mem_automorphic`: conjugation preserves actual automorphic forms,
  that is the three conditions of `automorphicSubrepresentation`.
  - Center finiteness: the center orbit of `conj f` lies in the conjugate of the center
    orbit of `f`, since `z · conj f = conj (centerConj z · f)` by
    `finiteSmoothConj_centerAction` and `centerConj_centerConj`. Apply
    `IsFiniteVector.antilinear`.
  - Finiteness under the standard compact subgroup at infinity: conjugation commutes
    with these translations. Apply `IsFiniteVector.antilinear`.
  - Polynomial growth: `‖conj z‖ = ‖z‖`, so the same bound holds.
- `finiteSmoothConj_mem_operatorCore`: conjugation preserves the stable operator core
  (`f` with `a f` automorphic for every operator `a`). For an operator `a`, apply the
  previous lemma to `operatorConj a` applied to `f`, and use
  `a (conj f) = conj ((operatorConj a) f)`.
- `stableConj F n`: pointwise conjugation of `StableAutomorphicFunctions F n`, an
  antilinear map, with `stableConj_val` and `stableConj_stableConj`.
- `stableConj_operatorAction`:
  `conj (a · f) = (operatorConj a) · conj f` for the stable action of an operator `a`.
- `stableConjEquiv F n`: `stableConj` as an antilinear involutive equivalence, with
  `stableConjEquiv_apply`.

## Constant terms

Under `[CompactSpace (AdeleQuotient F)]`:

- `constantTerm_continuousConj`: the constant term of `conj f` along each standard
  maximal block parabolic is the conjugate of the constant term of `f`. The constant
  term is an integral against `matrixQuotientHaar`, and Mathlib's `integral_conj`
  moves conjugation through the integral.
- `isCuspidal_continuousConj`: `conj f` is cuspidal when `f` is.

## Conjugate characters

- `unitsConj`: complex conjugation on `ℂˣ`, as a continuous homomorphism.
- `conjCharacter F χ = unitsConj ∘ χ`: the complex conjugate of an idele class
  character `χ`. Unitarity is not needed to define it.
- `conjCharacter_apply`, `centralIdeleCharacter_conjCharacter`: the value formulas
  `conjCharacter χ x = conj (χ x)` and the same for the pulled-back character on ideles.
- `norm_conjCharacter`: `‖conjCharacter χ x‖ = ‖χ x‖`.

## The conjugate realization (namespace `OperatorRealization`)

For an actual operator realization `S : OperatorRealization F n`:

- `S.conjugate`: the image of `S` under `stableConjEquiv`. It is invariant under every
  operator `a`, because `a · conj f = conj ((operatorConj a) · f)` and `S` is invariant
  under `operatorConj a`.
- `S.conjugateEquiv : S.Space ≃ₛₗ[starRingEnd ℂ] S.conjugate.Space`: pointwise
  conjugation, the restriction of `stableConjEquiv` to `S`
  (`LinearEquiv.submoduleMap`). `conjugateEquiv_val` and `conjugateEquiv_symm_val` give
  the underlying functions; the inverse is again pointwise conjugation.
- `conjugateEquiv_operatorAction`:
  `a · c f = c ((operatorConj a) · f)` on `S.conjugate`, with `c = S.conjugateEquiv`.
- `conjugateEquiv_finite`, `conjugateEquiv_compact`: `c` commutes with
  `finiteRepresentation d` and `compactRepresentation k`. Each is proved on the
  underlying stable functions from `stableConj_operatorAction` and the fact that
  `operatorConj` fixes the corresponding operator.
- `conjugateEquiv_envelopingAction`: `u · c f = c (envelopingConj u · f)`.
- `conjugateEquiv_lieAction`: `c` commutes with `lieAction X` for every element `X` of
  the real Lie algebra. Here `lieAction X` is the enveloping action of
  `envelopingGenerator (complexify X)`, and this element is fixed by `envelopingConj`
  (`envelopingConj_generator`, `complexConj_complexify`).
- `toContinuous_conjugateEquiv`, `toContinuous_conjugateEquiv_symm`,
  `evaluate_conjugateEquiv`: the underlying continuous function of `c f` is
  `continuousConj` of that of `f`; its values are the conjugate values.
- `conjugateSubrepresentationOrderIso`: the order isomorphism between invariant
  subspaces of `S` and of `S.conjugate`, from
  `antilinearConjugatedSubrepresentationOrderIso` with `α = operatorConj`.
- `conjugate_isIrreducible_iff`: `S.conjugate` is irreducible if and only if `S` is.
  Irreducibility is `IsSimpleOrder` of the invariant subspaces, which an order
  isomorphism preserves.
- `HasCentralCharacter.conjugate`: if `S` has central character `χ`, then
  `S.conjugate` has central character `conjCharacter χ`. Every element of
  `S.conjugate` is `c g`. Its value at `z x` is
  `conj (χ(z) g(x)) = conj (χ(z)) · conj (g(x))`.
- `conjugate_isCuspidal_iff` (under `[CompactSpace (AdeleQuotient F)]`): `S.conjugate`
  is cuspidal if and only if `S` is, by `isCuspidal_continuousConj` in both directions
  and the involution property.

## The conjugate cuspidal realization (namespace `CuspidalOperatorRealization`)

Under `[CompactSpace (AdeleQuotient F)]`, for `T : CuspidalOperatorRealization F r`:

- `T.conjugate`: the conjugate realization `T.realization.conjugate`, with
  irreducibility and cuspidality from the two `iff` lemmas above.
- `T.conjugateEquiv : T.Space ≃ₛₗ[starRingEnd ℂ] T.conjugate.Space`: pointwise
  conjugation.
- `conjugateEquiv_finite`, `conjugateEquiv_compact`, `conjugateEquiv_lieAction`: the
  three commutation identities
  `T.conjugate.realization.finiteRepresentation d (c f) = c (T.realization.finiteRepresentation d f)`,
  the same for `compactRepresentation k`, and the same for `lieAction X` with real `X`.
- `toContinuous_conjugateEquiv`: the underlying continuous function of `c f` is the
  pointwise conjugate of that of `f`.
- `HasCentralCharacter.conjugate`: the central character of `T.conjugate` is
  `conjCharacter χ` when that of `T` is `χ`.

## Unitary central characters

- `Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter.conjugate`:
  if `T` has a unitary central character, then so does `T.conjugate`. If `χ` is a
  unitary central character of `T`, then `conjCharacter χ` is a central character of
  `T.conjugate`, and it is unitary by `norm_conjCharacter`.
