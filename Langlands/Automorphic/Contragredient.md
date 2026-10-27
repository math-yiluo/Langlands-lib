# Contragredient realizations

This module defines when an actual automorphic realization `T` of `GL_n` over
a number field `F` realizes the contragredient `π̌` of another realization
`S`. It applies to the Library's full-operator realizations
(`OperatorRealization F n`), their isomorphism classes, and irreducible
cuspidal classes (`CuspidalOperatorRealization.IsoClass F r`, of rank
`r + 1`). The relation is stated directly as an isomorphism onto the
contragredient. The module does not construct a contragredient realization
or prove that one exists. It uses no Petersson inner product, admissibility
or multiplicity statement and asserts none.

## Setting

`F` is any number field; no CM hypothesis is used. A realization `S` has a
complex vector space `S.Space` of automorphic functions with three families
of operators:

- the finite adelic representation `S.finiteRepresentation` of
  `GL_n(𝔸_{F,f})`;
- the representation `S.compactRepresentation` of the standard compact
  subgroup `K_∞ = standardInfiniteCompact F n` of `GL_n(F ⊗ ℝ)`;
- the real Lie algebra action `S.lieAction X`, for `X` in
  `ArchimedeanGL.RealLieAlgebra F n`.

Two published declarations from `Langlands/Automorphic/ConjugateContragredient`
are reused unchanged. Neither uses the CM hypothesis of that module.

- `lieAction S X` is the action of `1 ⊗ X` in the complexified Lie algebra,
  through the enveloping algebra.
- `IsContragredientFunctional S l`, for `l : Module.Dual ℂ S.Space`, says that
  `l` is a smooth vector of the algebraic dual of the finite representation
  and a finite vector of the algebraic dual of the compact representation.
  These functionals form the underlying space of the contragredient `π̌`.

## Definitions

- `IsInvariantPairing S T B`, for a complex bilinear form
  `B : S.Space → T.Space → ℂ`, is the conjunction of three conditions. For
  all `d ∈ GL_n(𝔸_{F,f})`, `k ∈ K_∞`, real Lie algebra elements `X`,
  `y ∈ S.Space` and `x ∈ T.Space`:
  - `B (S(d) y) (T(d) x) = B y x`;
  - `B (S(k) y) (T(k) x) = B y x`;
  - `B (S(X) y) x + B y (T(X) x) = 0`.
- `IsContragredientPairing S T B` says that `B` is an invariant pairing and
  that the map `x ↦ B (·) x` (`B.flip`) is a bijection from `T.Space` onto the
  contragredient functionals of `S`. In Lean this is three conditions: every
  `B.flip x` is a contragredient functional, `B.flip` is injective, and every
  contragredient functional of `S` is some `B.flip x`.
- `IsContragredientOf T S` says that some bilinear form
  `B : S.Space → T.Space → ℂ` satisfies `IsContragredientPairing S T B`. Read
  it as "`T` is a contragredient of `S`". The first argument is the
  contragredient.
- `OperatorRealization.IsoClass.IsContragredientOf d c` says that some
  realization `T` in the class `d` is a contragredient of some realization
  `S` in the class `c`.
- `CuspidalOperatorRealization.IsoClass.IsContragredientOf d c` says that the
  underlying full-operator class `d.toOperatorClass` is a contragredient of
  `c.toOperatorClass`. Like every cuspidal declaration in the Library, it
  carries the hypothesis `CompactSpace (AdeleQuotient F)`.

## Theorems

- `IsInvariantPairing.flip_finite`, `IsInvariantPairing.flip_compact` and
  `IsInvariantPairing.flip_lieAction`: for an invariant pairing, `B.flip`
  intertwines the action of `T` with the contragredient action on functionals
  of `S`. In Lean,
  `B.flip (T(d) x) = S.finiteRepresentation.dual d (B.flip x)` and
  `B.flip (T(k) x) = S.compactRepresentation.dual k (B.flip x)`, where Mathlib's
  `Representation.dual` acts by `l ↦ l ∘ S(g⁻¹)`. For the Lie algebra,
  `B.flip (T(X) x) = -(B.flip x ∘ S(X))`.
- `IsContragredientOf.of_equivalence_left` and
  `isContragredientOf_congr_left`: the relation depends only on the
  equivalence class of `S`. If `e : S ≃ S'`, the pairing `B` for `S` gives the
  pairing `(y, x) ↦ B (e⁻¹ y) x` for `S'`. Contragredient functionals pull back
  along intertwiners because the dual of an intertwiner preserves smooth
  vectors and finite vectors. Two private helpers do this; they repeat the
  private helpers of the same name in `ConjugateContragredient`, which cannot
  be imported.
- `IsContragredientOf.of_equivalence_right` and
  `isContragredientOf_congr_right`: the relation depends only on the
  equivalence class of `T`. If `e : T ≃ T'`, the pairing
  `(y, x) ↦ B y (e⁻¹ x)` works for `T'`.
- `isoClass_isContragredientOf_iff`: for realizations `T` and `S`, the class
  relation `T.isoClass.IsContragredientOf S.isoClass` holds exactly when
  `T.IsContragredientOf S`.
- `CuspidalOperatorRealization.isoClass_isContragredientOf_iff`: the same
  statement for cuspidal realizations and their underlying full-operator
  realizations.

## Why the pairing expresses `T ≅ π̌`

Let `π` be the realization `S`. The contragredient `π̌` acts on the
contragredient functionals by `π̌(g) l = l ∘ π(g⁻¹)`, and the real Lie algebra
acts by `π̌(X) l = -l ∘ π(X)`. Let `L` be a linear bijection from `T.Space`
onto the contragredient functionals, and put `B y x = L x y`, so that
`L = B.flip`. Then `L` intertwines `T(g)` with `π̌(g)` exactly when
`B y (T(g) x) = B (π(g⁻¹) y) x` for all `x` and `y`. Replacing `y` by
`π(g) y` gives the two group conditions. The Lie algebra condition is exactly
`L ∘ T(X) = π̌(X) ∘ L`. It is required for real `X`. Complex-linearity then
gives it on the complexified Lie algebra, and hence on the enveloping
algebra. Therefore `IsContragredientPairing S T B` says exactly that `B.flip`
is an isomorphism of `(𝔤, K_∞) × GL_n(𝔸_{F,f})`-modules from `T` onto `π̌`. The
three `flip` theorems prove the intertwining direction of this equivalence
in Lean. The remaining explanation is not a separate Lean theorem, because
the Lean definition is the pairing form itself.

## Source and provenance

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Invent. Math. 139 (2000), §2.2, printed p. 444, PDF page 6
(source `henniart-2000-simple-proof`). After defining when a representation
`S` of `W_F` and an automorphic representation `Π` of `GL_n(𝔸_F)` are
associated, Henniart writes: "Cela implique immédiatement que `S^∨` et `Π^∨`
sont associées". This module supplies `Π^∨` for the Library's realizations, so
that this consequence can be stated over actual automorphic objects.

The module is derived. Henniart does not spell out the realization of the
contragredient. We take the contragredient in the standard sense for
automorphic representations, as in the published `ConjugateContragredient`
module: the algebraic functionals that are smooth for `GL_n(𝔸_{F,f})` and
`K_∞`-finite, with the dual actions. A realization `T` is a contragredient of
`S` when it is isomorphic to this space through a pairing, as explained above.
The definitions follow `IsConjugateInvariantPairing`,
`IsConjugateContragredientPairing` and `IsConjugateSelfDual` of that module,
with the CM involution removed and a second realization `T` in place of `S`.
`IsContragredientOf` is a relation, not a construction: it does not assert
that a realization on automorphic functions realizing `π̌` exists, and the
module proves no such existence.
