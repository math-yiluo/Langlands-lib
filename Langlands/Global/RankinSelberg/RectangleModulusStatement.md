# The modulus of right multiplication on adelic rectangular matrices

`Langlands.Global.RankinSelbergGlobal.RectangleMeasureModulusStatement.{u}`
is a Prop-valued statement. No proof is supplied.

Provenance: derived. It is the special case `E = M_{k×m}(F)`,
`a = (x ↦ x g)` of Weil's computation of the module of an adelic linear
automorphism, in the Library's measure conventions.

## The statement

For every number field `F : Type u` with `CompactSpace (AdeleQuotient F)`,
all naturals `k`, `m` and every adelic point `g : Points F m` (an element of
`GL_m(𝔸)`), the pushforward of `rectangleMeasure F k m` under right
multiplication

`x ↦ x * g`, for `x : Matrix (Fin k) (Fin m) (Adeles F)`,

where `g` is turned into a matrix through
`GeneralLinearGroupPoints.adelicEquiv F m`, equals

`ENNReal.ofReal ((detNorm F m g ^ k)⁻¹) • rectangleMeasure F k m`.

Here `detNorm F m g` is the idelic norm `|det g|_𝔸 > 0` (published module
`UnequalIntegrals`), and `rectangleMeasure F k m` is the additive Haar
measure on `M_{k×m}(𝔸)` of the published module `WhittakerIntegrals`,
transported from the Library's covolume-one two-block unipotent Haar
measure. The matrices carry the Borel σ-algebra, as in `WhittakerIntegrals`.

In Jacobian form: `d(x g) = |det g|_𝔸^k dx`, that is,
`∫ f(x g⁻¹) dx = |det g|_𝔸^k ∫ f(x) dx`. When `k = 0` or `m = 0` both sides
are the same measure on a one-point space (`|det g|^0 = 1`, and `det g = 1`
when `m = 0`).

## Source

A. Weil, *Basic Number Theory*, 2nd edition (1973), source
`weil-1973-basic-number-theory`, Chapter IV §3, Proposition 3, printed p.73
(PDF p.90): for a finite-dimensional vector space `E` over `k` and an
invertible `a ∈ End(E)_𝔸`, "the module of the latter automorphism
[`e ↦ ae` of `E_𝔸`] is `|det(a)|_𝔸`". Weil's module (Chapter I §2,
formula (2)) is defined by `α(λ(X)) = mod(λ) α(X)` for a Haar measure `α`.

Apply this to `E = M_{k×m}(F)` (dimension `km`) and the linear map
`a = (x ↦ x g)`. On each of the `k` rows of `x` it acts by right
multiplication by `g`, so its determinant as an endomorphism of `E` is
`det(g)^k`, and its module is `|det g|_𝔸^k`. For the pushforward,
`(map a μ)(X) = μ(a⁻¹ X) = |det g|_𝔸^{-k} μ(X)`, which is the stated
formula. Weil's statement holds for every Haar measure on `E_𝔸`, so it
applies to the Library's normalization `rectangleMeasure`.

## Role

Task 6838 needs this Jacobian to prove the dual expansion E'
(`DualProjectionWhittakerExpansion`, published module `UnfoldingDual`).
There, the change of variables `x ↦ x γ h` on `M_{k×m}(𝔸)`, with
`k = n - m - 1`, produces the factor `|det h|^k` that matches the exponent
`|det h|^{k/2}` of the dual projection against the normalization of the
unfolded integral. The Library proves only the scaling of the additive Haar
measure of `𝔸` by positive real ideles, so this statement is routed as a
separate premise.
