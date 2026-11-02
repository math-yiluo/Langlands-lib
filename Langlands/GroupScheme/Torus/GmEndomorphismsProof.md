# Proof: endomorphisms of the multiplicative group over an integral domain

Author: Worker 207.

`Langlands.GroupScheme.Gm.endomorphismsStatement` proves the published
proposition `Langlands.GroupScheme.Gm.EndomorphismsStatement` from the module
`Langlands.GroupScheme.Torus.GmEndomorphismsStatement`:

```lean
def EndomorphismsStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsDomain R],
    Function.Bijective (multiplication (Gm (Spec R)).toGrp)
```

The theorem has exactly this type, `EndomorphismsStatement.{u}`, for an
arbitrary universe `u`. It takes no further hypotheses. The proof uses only
the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Route

Milne, *Algebraic Groups* (2017), 2.22, proves `End(𝔾_m) ≃ ℤ` over a field by
looking at the image of the coordinate `T` under the comorphism. That image is
a group-like unit of `k[T, T⁻¹]`, and the only such units are the powers of
`T`. The Lean proof follows this idea over an integral domain `R`, working
with points instead of Hopf algebras:

1. The endomorphism is recorded by its value on one universal point, a unit of
   `R[T, T⁻¹]`.
2. Over a domain that unit is `c T^n` with `c ∈ Rˣ`.
3. Evaluation at `T = 1` shows `c = 1`.
4. The endomorphism `multiplication _ n` has the same unit `T^n`, so the two
   endomorphisms are equal.

## Units of Laurent polynomials

These two lemmas are in the namespace `Langlands.GroupScheme`.

- `eq_C_mul_X_pow_of_natTrailingDegree_eq_natDegree`: a polynomial whose
  trailing degree equals its degree is `C p.leadingCoeff * X ^ p.natDegree`.
  The proof compares coefficients with `coeff_C_mul_X_pow`. Coefficients below
  the trailing degree and above the degree vanish.
- `laurent_unit_eq_C_mul_T`: over an integral domain, every unit `v` of
  `LaurentPolynomial R` equals `C c * T n` for some `c : Rˣ` and `n : ℤ`.
  Mathlib's `LaurentPolynomial.exists_T_pow` writes `v = p * T (-a)` and
  `v⁻¹ = q * T (-b)` with polynomials `p` and `q`. Then `p * q = X ^ (a + b)`,
  checked after the injective map `Polynomial.toLaurent`. Neither factor is
  zero. Over a domain, `natDegree` and `natTrailingDegree` are additive on
  products (`natDegree_mul`, `natTrailingDegree_mul`). Both equal `a + b` for
  `X ^ (a + b)`. Since trailing degree is at most degree for each factor, `p`
  has equal trailing degree and degree, so `p` is a monomial by the previous
  lemma. Its leading coefficient is a unit, with inverse the leading
  coefficient of `q`, because the product of the leading coefficients is the
  leading coefficient `1` of `X ^ (a + b)`. The exponent is
  `p.natDegree - a`.

Mathlib has no lemma describing the units of Laurent polynomials, so this
part is internal.

## The universal point

All of these declarations are in the namespace `Langlands.GroupScheme.Gm`.

- `laurentStructure R` is the structure morphism
  `Spec R[T, T⁻¹] ⟶ Spec R`, and `universalPoint R` is the point
  `(relativeLaurentIso R).inv` of `𝔾_{m, Spec R}` defined on it. Here
  `relativeLaurentIso` is the published isomorphism of `𝔾_{m, Spec R}` with
  the relative Laurent spectrum (module
  `Langlands.GroupScheme.MultiplicativeLaurent`).
- `affinePointsEquiv_universalPoint`: under the published equivalence
  `affinePointsEquiv` between affine points and units, the universal point is
  the coordinate `T 1`. The proof uses the published
  `relativeLaurentIso_affinePointsEquiv_val` and the identity
  `(relativeLaurentIso R).inv ≫ (relativeLaurentIso R).hom = 𝟙`.
- `factor_universalPoint`: every point `x : T ⟶ 𝔾_{m, Spec R}` is
  `(x ≫ (relativeLaurentIso R).hom) ≫ universalPoint R`.
- `hom_ext_universalPoint`: two homomorphisms out of `𝔾_{m, Spec R}` are equal
  if they agree on the universal point. This combines the previous lemma with
  the published extensionality lemma `hom_ext_points`.

## The unit of an endomorphism

- `endUnit R φ` is the unit `affinePointsEquiv (universalPoint R ≫ φ)` of
  `R[T, T⁻¹]`. `endUnit_injective` follows from `hom_ext_universalPoint` and
  injectivity of `affinePointsEquiv`.
- `endUnit_multiplication`: the unit of `multiplication _ n` is `T n`. The
  published lemma `points_multiplication` says that multiplication by `n`
  acts on points as the `n`-th power. The published equivalence
  `affinePointsEquiv` is multiplicative, so the unit is the `n`-th power of
  the coordinate unit. The published lemma `relativeCoordUnit_zpow_val`
  identifies that power with `T n`.
- `evalOne R` is evaluation of Laurent polynomials at `T = 1`.
  `affineMap_evalOne_universalPoint` shows that the universal point,
  specialised along `evalOne`, is the identity point `1`. The proof compares
  units with `affinePointsEquiv_naturality` and uses `eval₂_T`.
- `evalOne_endUnit`: the unit of any endomorphism `φ` evaluates to `1` at
  `T = 1`. By naturality, this evaluation is the unit of
  `1 ≫ φ`, and a homomorphism of group objects preserves the identity point
  (`MonObj.one_comp`).

## Conclusion

- `exists_eq_multiplication`: over a domain, `endUnit R φ = C c * T n` by
  `laurent_unit_eq_C_mul_T`. Evaluating at `T = 1` with `evalOne_endUnit`
  gives `c = 1`. Hence `endUnit R φ` and
  `endUnit R (multiplication _ n)` are both `T n`, and `endUnit_injective`
  gives `φ = multiplication _ n`.
- `multiplication_injective`: if `multiplication _ m = multiplication _ n`,
  their units give `T m = T n` in `R[T, T⁻¹]`. These are the single elements
  at `m` and `n` with coefficient `1` of the underlying additive monoid
  algebra. Since `1 ≠ 0` in a domain, `AddMonoidAlgebra.single_left_injective`
  gives `m = n`.
- `endomorphismsStatement` combines injectivity and surjectivity.

## Authorship

Worker 207 authored the proof and this explanation, first shared as revision 1
of this task's public draft. Worker 1173 rechecked the pair in the pinned
environment and submitted it. Worker 1173 left the Lean unchanged and changed
the Markdown only by adding the namespace sentence for the Laurent-polynomial
lemmas and this paragraph. Development compilation does not establish
independent review.
