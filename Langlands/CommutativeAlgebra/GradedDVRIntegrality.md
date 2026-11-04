# Integrality of contracting points of a graded algebra over a DVR

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. It replaces the
root-group valuation step of that proof by a statement about graded algebras.
The statement and its proof are derived here; they are not quoted from the
source. The valuation input is `exists_ne_zero_forall_aeval_eq_zero` from
`Langlands.CommutativeAlgebra.DVRWeightedLeadingTerm`.

Throughout, `k` is a field and `B` is a commutative `k`-algebra with a ring
homomorphism `c : B → LaurentPolynomial B` (a "coaction"). The coefficient
`(c b).coeff n` is the weight-`n` component of `b`.

## Gradings and contracting points

- `IsGrading k c` packages three conditions: `c` maps each scalar
  `algebraMap k B r` to the constant Laurent polynomial `C (algebraMap k B r)`;
  for every `b` the components `(c b).coeff n` sum to `b`; and each component
  is homogeneous: `c ((c b).coeff n) = single n ((c b).coeff n)`.
- For a `k`-algebra map `ε : B → k` (the counit) and a `k`-algebra `R`, a point
  `a : B →ₐ[k] R` is `IsContracting c ε a` when `a` kills every component of
  negative weight and `a ((c b).coeff 0) = ε b` for every `b`. When `B` is the
  coordinate ring of an affine group, `c` the coaction of a cocharacter, and
  `ε` the counit, these are exactly the conditions of the Library's
  `mem_unipotent_iff` for points of the dynamic unipotent subgroup `U(λ)`.
- `contractingIdeal c ε` is the ideal spanned by the negative-weight components
  `(c b).coeff n` (`n < 0`) and the differences `(c b).coeff 0 - ε b`.
  `isContracting_iff` says that `a` is contracting iff it kills this ideal.

## Auxiliary lemmas

- `coeff_mul_mem`: if every component of `y` lies in an ideal `I`, then so does
  every component of `r * y`. Expand `c r` as a finite sum of monomials
  `single m ((c r).coeff m)`; each product with `c y` has components
  `(c r).coeff m * (c y).coeff (n - m)`.
- `coeff_mem_contractingIdeal` (needs `IsGrading`): every component of an
  element of the contracting ideal lies in the contracting ideal. This is proved
  by induction on the span. A generator `(c b).coeff m` is homogeneous of weight
  `m`. A generator `(c b).coeff 0 - ε b` is homogeneous of weight `0`, because
  scalars are constants. Sums are handled componentwise and multiples by
  `coeff_mul_mem`.
- `coeff_aeval` (needs `IsGrading`): if the elements `x i` are homogeneous of
  weights `w i : ℕ`, then for a polynomial `P` with coefficients in `k`, the
  weight-`n` component of `P(x)` is the value at `x` of the weighted-homogeneous
  component of `P` of degree `n` when `n ≥ 0`, and `0` when `n < 0`. This is
  proved by induction on `P`; a monomial in the `x i` is homogeneous of its
  weighted degree.

## `integral_of_contracting`

Hypotheses:

- `B` is a finitely generated `k`-algebra, `IsGrading k c`, and `ε : B →ₐ[k] k`
  satisfies `ε ((c b).coeff n) = if n = 0 then ε b else 0` for all `b` and `n`.
- `M ⊆ B` is a set containing all components `(c m).coeff n` of each `m ∈ M`.
- (`hker`) The only contracting `k`-point `a : B →ₐ[k] k` with `a m = ε m` for
  all `m ∈ M` is `ε`.
- `A : Type u` is a DVR and a `k`-algebra, and its residue field is
  geometrically reduced over `k`.
- (`hrat`) Every nontrivial finitely generated geometrically reduced
  `k`-algebra in `Type u` has a `k`-algebra map to `k`. For separably closed
  `k` this is the statement `SeparablyClosedRationalPointStatement` proposed
  in TaskHub statement task `7fc59080-1437-464e-8a13-8c46eee51d71`, which is
  not yet in the Library; here it is a hypothesis.
- `ξ : B →ₐ[k] FractionRing A` is contracting, and `ξ m` lies in (the image
  of) `A` for every `m ∈ M`.

Conclusion: `ξ b` lies in the image of `A` for every `b ∈ B`.

Proof as implemented. Suppose not. Fix a finite generating set `s` of `B` and
let `I` be the contracting ideal. Both `ξ` and `ε` kill `I`.

1. *Generators.* Index `ι` by pairs `(b, n)` with `b ∈ s` and `n > 0` in the
   support of `c b`, and put `x (b, n) = (c b).coeff n`, of weight `w = n`. By
   `IsGrading` each `x i` is homogeneous of positive weight `w i`.
2. *Presentation modulo `I`* (`hgen`). Every `b ∈ B` is congruent modulo `I` to
   `P(x)` for some `P ∈ k[ι]`. For a generator `b ∈ s`, write `b` as the sum of
   its components. The negative ones lie in `I`, the weight-`0` one is
   `ε b` modulo `I`, and the positive ones are variables. So
   `P = C (ε b) + ∑ X (b, n)` works. Sums and products follow by induction over
   `Algebra.adjoin`.
3. *Equations.* Let `S` be the set of weighted-homogeneous polynomials `P` of
   positive degree such that `P(x) ∈ I` or `y - P(x) ∈ I` for some `y ∈ M`. For
   `P ∈ S` the value `P(ξx)` equals `ξ(P(x))`, which is `0` or `ξ y` and so lies
   in `A`. The coordinates `ξx i = ξ (x i)` are not all in `A`: otherwise every
   `ξ b` would be the image of a polynomial value over `A`, by step 2.
4. *Residue point.* `exists_ne_zero_forall_aeval_eq_zero` (applied to the images
   of `S` in `A[ι]`) gives a nonzero `abar : ι → ResidueField A` with
   `P(abar) = 0` for all `P ∈ S`. Choose `i0` with `abar i0 ≠ 0`. The
   `k`-subalgebra `R` of the residue field generated by the `abar i` and
   `(abar i0)⁻¹` is finitely generated, nontrivial and geometrically reduced. So
   `hrat` gives `ψ : R → k`. Put `a i = ψ (abar i)`. Then `P(a) = 0` for
   `P ∈ S`, and `a i0 ≠ 0` because `abar i0` is invertible in `R`.
5. *A contracting `k`-point* (`haker`, `atil`). If `P(x) ∈ I`, then each
   weighted-homogeneous component `P_d` also has `P_d(x) ∈ I`, by
   `coeff_mem_contractingIdeal` and `coeff_aeval`. For `d > 0` we get
   `P_d ∈ S`, so `P_d(a) = 0`. For `d = 0` the component is a constant killed by
   `ε`, hence zero. So `P(a) = 0`. The map `k[ι] → B/I`, `P ↦ P(x)`, is
   surjective by step 2, and its kernel is killed by evaluation at `a`.
   Composing `B → B/I ≅ k[ι]/ker → k` therefore gives `atil : B →ₐ[k] k`. It
   kills `I`, so it is contracting, and `atil (P(x)) = P(a)`.
6. *Agreement on `M`.* For `m ∈ M`, compare `atil` and `ε` on each component
   `y = (c m).coeff n`. For `n < 0` both vanish; for `n = 0` both give `ε m`.
   For `n > 0`, `ε y = 0`. Take `P'` with `y - P'(x) ∈ I` and let `P` be its
   weighted-homogeneous component of degree `n`. Taking weight-`n` components
   gives `y - P(x) ∈ I`, so `P ∈ S` (as `y ∈ M`), and
   `atil y = atil (P(x)) = P(a) = 0`. Summing the components gives
   `atil m = ε m`.
7. *Contradiction.* By `hker`, `atil = ε`. But `atil (x i0) = a i0 ≠ 0`, while
   `ε (x i0) = 0` because `x i0` has positive weight.

## Intended role in C.1.6

In the C.1.6 argument (with `k` separably closed), `B` is the coordinate ring of
the pseudo-reductive group `G` with the conjugation coaction of the cocharacter
`λ` opposite to the one defining the pseudo-parabolic subgroup. `ξ` is the
`K`-point `u` of `U_G(λ)` obtained from the open cell. `M` comes from the
coordinate ring of the reductive quotient `G''` of `G` over an algebraic
closure, where the image of `u` extends over the base-changed DVR. `hker` is
the triviality of the kernel of `U_G(λ)(k) → G''`. A separate base-change step
over the algebraic closure reduces to the form proved here.
