# Realizations isomorphic to their conjugate contragredient

This module defines Harris's condition `π ≅ π̌ ∘ c` for actual automorphic
realizations of `GL_n` over a CM field `E`, where `c` is the CM involution.
It applies to the Library's full-operator realizations
(`OperatorRealization E n`), their isomorphism classes, and irreducible
cuspidal classes (`CuspidalOperatorRealization.IsoClass E r`, of rank
`r + 1`). The condition is stated directly as an isomorphism onto the
contragredient. No Petersson inner product, admissibility or multiplicity
statement is used or asserted.

## Setting

`E` is a number field with `IsCMField E`. A realization `S` has a complex
vector space `S.Space` of automorphic functions with three families of
operators:

- the finite adelic representation `S.finiteRepresentation` of
  `GL_n(𝔸_{E,f})`;
- the representation `S.compactRepresentation` of the standard compact
  subgroup `K_∞ = standardInfiniteCompact E n` of `GL_n(E ⊗ ℝ)`;
- the differential action `S.envelopingAction` of the complex universal
  enveloping algebra.

The CM involution acts on these groups through `finiteConj`, `compactConj`
and `lieConj` from `Langlands/Global/CMConjugationGL`.

## Definitions

- `lieAction S X`, for `X` in the real Lie algebra
  `ArchimedeanGL.RealLieAlgebra E n`, is the action of `1 ⊗ X` in the
  complexified Lie algebra, through the enveloping algebra.
- `IsContragredientFunctional S l`, for a linear functional
  `l : Module.Dual ℂ S.Space`, says two things. First, `l` is a smooth vector
  of the algebraic dual of the finite representation: an open subgroup of
  `GL_n(𝔸_{E,f})` fixes it (`Langlands.IsSmoothVector`). Second, `l` is a
  finite vector of the algebraic dual of the compact representation: its
  `K_∞`-orbit spans a finite-dimensional space
  (`FiniteVectors.IsFiniteVector`). These functionals form the underlying
  space of the contragredient `π̌`.
- `IsConjugateInvariantPairing S B`, for a complex bilinear form
  `B : S.Space → S.Space → ℂ`, is the conjunction of three conditions. For all
  `d ∈ GL_n(𝔸_{E,f})`, `k ∈ K_∞`, real Lie algebra elements `X`, and vectors
  `x, y`:
  - `B (π(c d) y) (π(d) x) = B y x`;
  - `B (π(c k) y) (π(k) x) = B y x`;
  - `B (π(dc X) y) x + B y (π(X) x) = 0`.

  Here `c d = finiteConj E n d`, `c k = compactConj E n k`,
  `dc X = lieConj E n X`, and `π(X) = lieAction S X`.
- `IsConjugateContragredientPairing S B` says that `B` is a conjugate
  invariant pairing and that the map `x ↦ B (·) x` (`B.flip`) is a bijection
  from `S.Space` onto the contragredient functionals. In Lean this is three
  conditions: every `B.flip x` is a contragredient functional, `B.flip` is
  injective, and every contragredient functional is some `B.flip x`.
- `IsConjugateSelfDual S` says that some bilinear form `B` satisfies
  `IsConjugateContragredientPairing S B`.
- `OperatorRealization.IsoClass.IsConjugateSelfDual c` says that some
  realization in the class `c` is conjugate self-dual.
- `CuspidalOperatorRealization.IsoClass.IsConjugateSelfDual c` says that the
  underlying full-operator class `c.toOperatorClass` is conjugate self-dual.
  Like every cuspidal declaration in the Library, it carries the hypothesis
  `CompactSpace (AdeleQuotient E)`.

## Theorems

- `IsConjugateSelfDual.of_equivalence` and
  `isConjugateSelfDual_iff_of_equivalence`: the condition is invariant under
  full-operator equivalence. If `e : S ≃ T`, the pairing `B` for `S` gives
  the pairing `(y, x) ↦ B (e⁻¹ y) (e⁻¹ x)` for `T`. Contragredient functionals
  pull back along intertwiners because the dual of an intertwiner preserves
  smooth vectors and finite vectors.
- `isoClass_isConjugateSelfDual_iff`: a class is conjugate self-dual exactly
  when any given representative is.
- `CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff`: the same
  statement for a cuspidal realization and its underlying full-operator
  realization.

## Why the pairing expresses `π ≅ π̌ ∘ c`

The contragredient `π̌` acts on contragredient functionals by
`π̌(g) l = l ∘ π(g⁻¹)`. The representation `π̌ ∘ c` acts by `π̌(c g)`. Let
`T` be a linear bijection from `π` onto the contragredient functionals, and
put `B y x = T x y`, so that `T = B.flip`. Then `T` intertwines `π(g)` with
`π̌(c g)` exactly when `B y (π(g) x) = B (π((c g)⁻¹) y) x` for all `x, y`.
Replacing `y` by `π(c g) y` gives the group conditions above, since `c` is a
group automorphism. For the Lie algebra, put `g = exp(tX)` and differentiate
at `t = 0`. The derivative of `c(exp(tX))` is `dc X`, and the derivative of
the contragredient action of `exp(tX)` is `-X`. This gives the third
condition. Conversely, this condition is exactly the statement that
`T ∘ π(X) = π̌(dc X) ∘ T` for the contragredient Lie algebra action
`π̌(Y) l = -l ∘ π(Y)`. It is required for real `X`. Complex-linearity then
gives it on the complexified Lie algebra, and hence on the enveloping
algebra. Therefore `IsConjugateContragredientPairing S B` says exactly that
`B.flip` is an isomorphism of `(𝔤, K_∞) × GL_n(𝔸_{E,f})`-modules from `π`
onto `π̌ ∘ c`. This equivalence is explained here; it is not a separate Lean
theorem, because the Lean definition is the pairing form itself.

## Source and provenance

Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), Theorem 1.2(ii), printed p. 185, PDF page 9
(retained TeX `math_9611226v1.tex`: the theorem is lines 523–537 and
condition (ii) lines 530–533), requires `π_i ≅ π̌_i ∘ c` for each cuspidal
constituent `π_i`. There `E = E₀·K₀` with `E₀` totally real and
`K₀` imaginary quadratic, and `c` is the nontrivial element of `Gal(E/E₀)`,
which is the CM involution of `E`. The set `CU(n, E)` of Harris consists of
the `π` satisfying the conditions of that theorem (printed p. 185, TeX
lines 539–541; restated at the top of p. 186, TeX lines 565–567). It enters the hypotheses
of Harris's Proposition 4.8 used in Henniart's proof.

The module is derived. Harris does not spell out the realization of the
contragredient or of `π̌ ∘ c`. We take the contragredient in the standard
sense for automorphic representations: the algebraic functionals that are
smooth for `GL_n(𝔸_{E,f})` and `K_∞`-finite, with the dual actions. An
isomorphism with `π̌ ∘ c` is encoded by the pairing as explained above. The
definition applies to any CM field, which is more general than Harris's
fields `E₀·K₀`. It does not by itself include the other conditions of
Theorem 1.2: the cohomological (regular) archimedean condition, the
square-integrable local component, and the splitting of `p_i` in `K₀`. These
are separate predicates.
