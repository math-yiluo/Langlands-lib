# Formal characters of actual representations on a split maximal torus

This module applies to a field `k : Type u` of arbitrary characteristic, an
actual affine group scheme `G` over `Spec k`, a supplied `p : SplitPinning G`,
and a finite matrix representation `ρ : MatrixRepresentation G n`. No algebraic
closedness, simple connectedness, semisimplicity or irreducibility is assumed.
Write `X` for `characterLattice p.torus`. For a weight `wt : X` and a rational
point `s` of the torus, write `wt(s) ∈ k` for
`rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm wt) s`,
the value at `s` of the rational character corresponding to `wt`.

The module is built on the published restriction map
`SplitPinning.torusRestriction` from
`Langlands.GroupScheme.Rational.TorusClassFunctionRestriction`. That module
already proves that the coefficients of a restricted class function are
unchanged by root reflections, and that the coefficients of a restricted trace
are the weight-space dimensions. This module adds the evaluation at rational
torus points and assembles the data needed by the separation argument.

## Rational points and the base-field test

These are in namespace `Langlands.GroupScheme.MatrixRepresentation`, for a
field `k` and group schemes `G`, `H` over `Spec k`.

- `rationalAffinePoint_comp`: for a rational point `g` of `H` and a homomorphism
  `f : H ⟶ G`, the base-field affine test `rationalAffinePoint (g ≫ f.hom.hom)`
  is `rationalAffinePoint g ≫ f.hom.hom`. This is associativity of composition.
- `affineUnitsEquiv_rationalAffinePoint`: for a rational character `χ` of `H`,
  the affine `𝔾_m` identification `Gm.affineUnitsEquiv` sends the point
  `rationalAffinePoint g ≫ χ.toMul.hom.hom` to `rationalCharacterEval χ g`. The
  proof uses the published `rationalCharacterEval_eq_affineUnitsEquiv`.

## Evaluation at rational torus points

These are in namespace `Langlands.GroupScheme.SplitPinning`.

- `value_rationalAffinePoint`: the character value
  `SplitCharacterPoint.value wt (rationalAffinePoint s)` used by `pointLift` is
  `wt(s)`, as an element of `k`.
- `pointLift_rationalAffinePoint`: for `x : AddMonoidAlgebra k X`,
  `SplitCharacterPoint.pointLift (rationalAffinePoint s) x` is the finite sum
  `Σ_wt x.coeff wt * wt(s)`. The proof unfolds `pointLift` as the group-algebra
  lift and uses Mathlib's `AddMonoidAlgebra.lift_apply'`.
- `pointLift_torusRestriction_eq_of_rho_eq`: let `s`, `t` be rational points of
  the torus whose images `s ≫ p.inclusion.hom.hom` and `t ≫ p.inclusion.hom.hom`
  in `G` have the same composite with the canonical class-function quotient map
  `ClassFunctions.rho G`. Then, for every class function `f`, the evaluations of
  `p.torusRestriction f` at `rationalAffinePoint s` and at
  `rationalAffinePoint t` are equal. The proof rewrites both sides with the
  published `pointCoordinates_torusPoint` as values of `f` at the image points
  in `G`, and applies the published `ClassFunctions.evaluation_eq_of_rho_eq`.

## The formal character

`formalCharacter p ρ : X →₀ k` is defined as the coefficient function of
`p.torusRestriction (MatrixRepresentation.traceClassFunction ρ)`, the
restriction to the split torus of the trace class function of `ρ`.

- `formalCharacter_apply`: its value at `wt` is the dimension of the weight space
  `p.representationWeightSpace ρ wt`, cast to `k`. This is the published
  `torusRestriction_traceClassFunction_coeff`; its spanning hypothesis is the
  published `iSup_representationWeightSpace_eq_top`, which holds for every
  representation.
- `formalCharacter_reflection`: for every root index `α` and every weight `wt`,
  the value at `p.rootDatum.reflection α wt` equals the value at `wt`. This is
  the published `torusRestriction_coeff_reflection`.
- `representationWeightSpace_ne_bot_of_formalCharacter_ne_zero`: a weight with
  nonzero value has a nonzero weight space, since the zero space has dimension
  zero.
- `formalCharacter_sum_eq_trace`: for every rational point `s` of the torus,
  `Σ_wt formalCharacter p ρ wt * wt(s)` is the trace of the matrix
  `ρ.rationalMatrix (s ≫ p.inclusion.hom.hom)`. The proof combines
  `pointLift_rationalAffinePoint`, `pointCoordinates_torusPoint`, the published
  `traceClassFunction_evaluate`, `rationalMatrix_eq_affineMatrix` and
  `rationalAffinePoint_comp`.

Because the value at `wt` is a natural number cast to `k`, in positive
characteristic it is the weight multiplicity modulo the characteristic. The
result below needs only the value `1` at a weight space of dimension one and the
value `0` at a zero weight space, so this reduction is harmless there.

## Highest-weight character data

`exists_invariant_triangular_of_rho_eq`: let `lam : X` and suppose
`hρ : p.IsHighestWeight ρ lam`. Let `s`, `t` be rational points of the torus
with `(s ≫ p.inclusion.hom.hom) ≫ ClassFunctions.rho G =
(t ≫ p.inclusion.hom.hom) ≫ ClassFunctions.rho G`. Then there is
`c : X →₀ k` such that

1. `c (p.rootDatum.reflection α wt) = c wt` for every root index `α` and every
   weight `wt`;
2. `c lam = 1`;
3. for every `wt` with `c wt ≠ 0`, `lam - wt ∈ p.positiveRootMonoid`, the
   additive monoid generated by the simple roots;
4. `Σ_wt c wt * wt(s) = Σ_wt c wt * wt(t)`.

The witness is `formalCharacter p ρ`. Item 1 is `formalCharacter_reflection`.
Item 2 is `formalCharacter_apply` with the third conjunct of `IsHighestWeight`
(the weight space at `lam` has dimension one). Item 3 combines
`representationWeightSpace_ne_bot_of_formalCharacter_ne_zero` with the fourth
conjunct of `IsHighestWeight` (every weight with a nonzero weight space lies
below `lam`). Item 4 rewrites both sums with `pointLift_rationalAffinePoint` and
applies `pointLift_torusRestriction_eq_of_rho_eq` to the trace class function.
The irreducibility conjunct of `IsHighestWeight` is not used.

## Provenance

This is an internal helper for the proof of
`Langlands.GroupScheme.ClassFunctions.TorusSeparationStatement`. It is a derived
translation of the step in Steinberg 1965 (source
`steinberg-1965-regular-elements-semisimple-groups`), §6, proof of Lemma 6.3,
printed pp. 62–63 (PDF pp. 15–16). There, the restriction to the maximal torus
of the irreducible character with highest weight `δ` is written as `sym δ` plus
a combination of `sym δ'` with `δ' < δ`. Here the same information is recorded
as reflection invariance, coefficient `1` at the highest weight and support
below it, for the actual trace class function of a supplied representation
satisfying the published `IsHighestWeight` predicate. Item 4 is the input that
Steinberg's proof of Corollary 6.6, (b) implies (a), printed p. 63, uses for
points of the torus. Steinberg works over an algebraically closed field with
points of the group. This module works over any field with rational points of
the supplied split torus and the actual scheme-theoretic class-function
quotient. It does not prove that highest-weight representations exist, and
Weyl invariance is proved only for the root reflections of the pinning's root
datum.
