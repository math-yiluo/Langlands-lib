# The Lie functor on homomorphisms up to prime-to-`p` isogeny

The module `Langlands.AbelianScheme.LiePrimeToP` makes `ℤ_(p)`-localized
homomorphisms of abelian schemes act on the actual relative Lie modules, and
constructs the local determinant polynomials of such actions on Lie
sections. It extends the published `lieFunctor`, `lieEndAction`,
`LieRational` and `LieRationalDeterminant` constructions.

## The induced Lie action when the denominators are units

An actual homomorphism `f`, and so `1 ⊗ f`, acts on `Lie(A)` by its ordinary
differential over every base. Extending this to the whole localized category,
so that `r ⊗ f` with `r ∈ ℤ_(p)` acts by `r • Lie(f)`, needs `r` to act on
`𝒪_S`, i.e. the integers prime to `p` to be units on `S`. This is the
situation of Kottwitz, *Points on some Shimura varieties over finite
fields*, J. Amer. Math. Soc. 5 (1992), §5, printed p.390 (PDF p.18), where
`S` is a scheme over `𝒪_E ⊗ ℤ_(p)` and `Lie(A)` is a locally free
`𝒪_S`-module on which `𝒪_B` acts. Source
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.

* `primeLocalGlobalScalars p h` is the unique ring homomorphism
  `ℤ_(p) → Γ(S, ⊤)` when every natural number prime to `p` is a unit of
  `Γ(S, ⊤)` (`PrimeLocalIntegers.lift`). Conversely
  `isUnit_natCast_of_primeLocal` shows that a ring map
  `a : ℤ_(p) →+* Γ(S, ⊤)` makes those numbers units. By
  `PrimeLocalIntegers.ringHom_ext` there is at most one such `a`, so the
  constructions below do not depend on how it is obtained.
* With `a`, the published `linearOfGlobalScalars a` makes `S.Modules`
  `ℤ_(p)`-linear, scalars acting through `a` and restriction to each open.
  `primeToPLieFunctor p a` is `CoefficientExtension.lift` of the additive
  `lieFunctor S` (additivity is the published `lieFunctor_additive`).
* `lieMapP p a f` is the differential of `f : HomP p A B`. On pure tensors
  `lieMapP p a (r ⊗ f) = a r • lieMap f` (`lieMapP_tmul`): the actual
  differential multiplied by the global function `a r`. It recovers
  `lieMap` on actual homomorphisms (`lieMapP_homToHomP`), preserves identity,
  composition and addition, and is semilinear along `a` (`lieMapP_smul`).
* `liePOrderAction p a A α` composes an action `α : O →+* EndP p A` of any
  ring with these differentials, giving a ring map `O →+* End(Lie A)`.
  `liePOrderAction_integral` identifies it with the published
  `(lieEndAction A).comp α` for actions through actual endomorphisms.

## Comparison with the rational action

If `S` lies over `Spec R` for a rational algebra `R` (for example a generic
fibre), `lieMapP_eq_lieMap0` proves `lieMapP p a f = lieMap0 q (homPToHom0 f)`:
the differential is the published rational differential of the image of
`f` in the rational category. The proof uses that `a` must equal the
composite `ℤ_(p) → ℚ → R → Γ(S, ⊤)` by `ringHom_ext`. Consequently
`liePOrderAction_eq_rational` identifies the action with the published
`lieRationalOrderAction` of `(endPToEnd0 p A).comp α`.

## Local determinant polynomials

For a finite family `b : ι → O`, a finite free trivialization
`e : free I ≅ (Lie A)|_U` and `V` over `U`, `liePSectionDeterminant p a A α e b V`
is the polynomial `det(X₁ α(b₁) + ⋯ + X_t α(b_t) ; Γ(V, Lie A))` in
`Γ(S, V)[X_i]`, computed with the published `localSectionDeterminant` from
the restricted action `liePLocalOrderAction` and the section action
`liePSectionOrderAction`. As for the published integral and rational
versions:

* `liePSectionDeterminant_eq_basis`: any finite basis of the section module
  gives the same polynomial;
* `liePSectionDeterminant_restrict`: it is compatible with restriction of
  coefficients;
* `eval_liePSectionDeterminant`: evaluation at section scalars is the
  determinant of the corresponding linear combination;
* `liePSectionDeterminant_integral` and `liePSectionDeterminant_eq_rational`:
  it equals the published `lieSectionDeterminant` for integral actions, and
  the published `lieRationalSectionDeterminant` over a rational base.

The polynomial is the full determinant, in variables indexed by the family;
no trace reformulation is used.

## Scope

All constructions are derived from the published Lie functor, the module
sheaf scalar structure and the coefficient extension. No local freeness
rank, base-change naturality of Lie modules or determinant equality is
asserted here.
