# Additive polynomials and composition maps

This module is the polynomial algebra behind the companion module
`AdditiveGroupQuotient`. That module shows that a quotient of a one-dimensional
vector group over a field is trivial or again a one-dimensional vector group.
Everything here is over a field `k`, in namespace
`Langlands.GroupScheme.RelativeRoot.AdditivePolynomial`. The module is internal to
this formalization: it records the algebra that the scheme argument needs, and it
changes no published definition.

## Additivity from a membership condition

Write `k[X][X]` for polynomials in two variables, with outer variable `Y` and inner
variable `X`. For `f : k[X]`, `f.map C` is `f(Y)`, `C f` is `f(X)`, and
`taylor X (f.map C)` is `f(X + Y)`.

- `eq_zero_of_mem_span`: let `f` be monic. Suppose `h` lies in the ideal
  `(f(X), f(Y))`, has `Y`-degree below `deg f`, and has every coefficient (a
  polynomial in `X`) of degree below `deg f`. Then `h = 0`. Write
  `h = a f(X) + b f(Y)` and reduce modulo the monic `f(Y)`. The left side is
  unchanged and the right side becomes `f(X) · (a mod f(Y))`. A nonzero
  coefficient of `a mod f(Y)` would give `h` a coefficient of degree at least
  `deg f`.
- `taylor_map_coeff`: the coefficient of `Y^n` in `f(X + Y)` is the `n`-th Hasse
  derivative of `f`.
- `taylor_eq_of_mem_span`: if `f` is monic of positive degree and
  `f(X + Y) ∈ (f(X), f(Y))`, then `f(X + Y) = f(X) + f(Y)`. Apply
  `eq_zero_of_mem_span` to `h = f(X + Y) - f(Y) - f(X)`. The coefficient of `Y^n`
  in `h` is `D_n f - f_n - [n = 0] f`. It vanishes for `n ≥ deg f`: above
  `deg f` both terms are zero, and at `n = deg f` both equal the leading
  coefficient. For `n > 0` its degree in `X` is below `deg f`. For `n = 0` it is
  the constant `-f_0`.
- `eval₂_add_of_taylor_eq`: the identity `f(X + Y) = f(X) + f(Y)` gives
  `f(a + b) = f(a) + f(b)` in every commutative ring with a ring map from `k`.
  Evaluate both sides at `X = a`, `Y = b`.

## Composition maps

`compHom f : k[X] →+* k[X]` is the composition map `p ↦ p ∘ f`. In Lean it is
`aeval f`. `compHom_C` and `compHom_X` record that it fixes constants and sends
`X` to `f`.

Let `f` have positive degree. Integrality and faithful flatness also use that
`f` is monic.

- `compHom_injective`: `compHom f` is injective, because a composite `p ∘ f` with
  `f` nonconstant is zero only if `p` is.
- `compHom_isIntegral`: `compHom f` is integral. The polynomial `f(T) - X` is
  monic in `T` with coefficients in the source, and `compHom f` maps it to
  `f(T) - f`, which has the root `T = X`. Integral elements are closed under
  sums and products, so every polynomial in `X` is integral.
- `flat_of_injective`: an injective ring map from a Dedekind domain to a domain
  is flat, because the target is torsion-free. It is stated for a ring map
  rather than an algebra, so that it applies to the endomorphism `compHom f` of
  `k[X]` without clashing with the algebra structure of `k[X]` over itself.
- `compHom_flat` and `compHom_faithfullyFlat`: `compHom f` is flat, and it is
  faithfully flat, since an integral injective map is surjective on prime spectra.
- `compHom_finitePresentation`: `compHom f` is of finite presentation for every
  `f`. Its composite with `C : k →+* k[X]` is `C`, which is of finite type over
  the field `k`, so `compHom f` is of finite type, and for the Noetherian source
  `k[X]` finite type gives finite presentation.

## Provenance

These are standard facts about polynomials over a field. The membership
criterion and the reduction of additivity to `f(X + Y) ∈ (f(X), f(Y))` are
derived for this formalization. They serve the proof that a nontrivial quotient
of `Ga` is isomorphic to `Ga` (Milne, *Algebraic Groups* (2017), 14.58 and
Exercise 14-3), where the kernel is cut out by an additive polynomial.
