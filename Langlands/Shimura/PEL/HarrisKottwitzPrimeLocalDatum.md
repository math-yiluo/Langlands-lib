# Kottwitz's prime-local PEL datum for the Harris trace-pairing input

The module `Langlands.Shimura.PEL.HarrisKottwitzPrimeLocalDatum` defines the
data of Kottwitz's integral PEL moduli problem at a prime `p`, before level
structure, for the Library's Harris input: the structure
`CentralSimpleUnitaryData.HarrisKottwitzPrimeLocalDatum D C p`.

## Source

Kottwitz, *Points on some Shimura varieties over finite fields*, J. Amer.
Math. Soc. 5 (1992), §5, printed pp.389–390 (PDF pp.17–18), source
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`. The list
of data there is: a simple `ℚ`-algebra `B` with positive involution `*`,
assumed such that `B_{ℚ_p} = B ⊗_ℚ ℚ_p` is a product of matrix algebras over
finite unramified extensions of `ℚ_p`; a `ℤ_(p)`-order `𝒪_B` preserved by `*` whose `p`-adic completion is a maximal
order of `B_{ℚ_p}`; a left `B`-module `V` with a nondegenerate alternating
form satisfying `(bv, w) = (v, b* w)`; a lattice `Λ₀` of `V_{ℚ_p}` that is
self-dual and preserved by `𝒪_B`; `C = End_B(V)` with the involution coming
from the form, which defines the group `G`; and, for a basis `α₁, …, α_t` of
`𝒪_B`, the polynomial `f(X₁, …, X_t) = det(X₁α₁ + ⋯ + X_tα_t ; V₁)` of the
`h`-eigenspace `V₁`, whose coefficients lie in `𝒪_E ⊗ ℤ_(p)`.

## The rational data in the existing Harris notation

The parameters are those of `HarrisReflexBase`: the totally real field `E`,
the CM field `K`, the central simple algebra `A` of `D` with its original
second-kind involution `σ = D.involution`, an imaginary quadratic `L` with
`j : L →+* K` and `τ₀`, and Harris signature charts `C` for the section
`harrisCMSection E j τ₀`; and a prime `p`.

* `B` is `A` with the **positive left involution**
  `τ = (D.harrisHodgePELAlgebra C).involution` of `HarrisHodgeInput`;
  `V` is `A` with left multiplication, and the form is the trace form
  `ψ = D.harrisHodgePELForm C`. `form_left` restates the adjoint identity
  `ψ(bx, y) = ψ(x, τ(b) y)` for order elements.
* The algebra `C = End_B(V)` acts by right multiplication, and its involution
  is the original Harris involution `σ`: `form_right` restates
  `ψ(xc, y) = ψ(x, y σ(c))` (published `harrisHodgePELForm_right`). This `σ`
  defines the Shimura group (`harrisHodgePELSimilitudesEquiv`), and is
  distinct from the left involution `τ` used for the order and the Rosati
  condition.

## The unramified hypothesis

These declarations are in `Langlands.Shimura`.

* `IsUnramifiedPadicExtension p F`, for a field `F` that is a `ℚ_p`-algebra
  and a `ℤ_p`-algebra compatibly, says that `F` is finite-dimensional over
  `ℚ_p` and that the integral closure of `ℤ_p` in `F` is a formally
  unramified `ℤ_p`-algebra (Mathlib's `Algebra.FormallyUnramified`, i.e.
  vanishing Kähler differentials). For the ring of integers of a finite
  extension of `ℚ_p` this is the usual condition that `p` generates the
  maximal ideal (ramification index one), the residue extension of finite
  fields being separable.
* `IsUnramifiedMatrixProductAt p B`, for a rational algebra `B`, says that
  there are a finite type `ι`, fields `F i` with
  `IsUnramifiedPadicExtension p (F i)` and sizes `n i` such that
  `ℚ_[p] ⊗[ℚ] B` is isomorphic as a `ℚ_p`-algebra to
  `Π i, Matrix (Fin (n i)) (Fin (n i)) (F i)`: Kottwitz's hypothesis on
  `B_{ℚ_p}`. The fields and the isomorphism are existential.
* `isUnramifiedPadicExtension_self`: `ℚ_p` is unramified over itself (the
  integral closure of `ℤ_p` in `ℚ_p` is `ℤ_p`, as `ℤ_p` is integrally
  closed). `isUnramifiedMatrixProductAt_of_split`: an algebra with
  `ℚ_p ⊗ B ≅ M_m(ℚ_p)` satisfies the hypothesis.

## The prime-local data

`Langlands.PrimeLocalIntegers.algebraOfRat` is a scoped instance making every
rational algebra a `ℤ_(p)`-algebra through `ℤ_(p) ⊆ ℚ`;
`smul_eq_toRat_smul` records the resulting scalar action. The structure has
the fields

* `unramified : IsUnramifiedMatrixProductAt p A`, the source's hypothesis
  that `B_{ℚ_p}` is a product of matrix algebras over finite unramified
  extensions of `ℚ_p`;
* `order : Subalgebra ℤ_(p) A`, with `rank` and a `basis` of the free
  `ℤ_(p)`-module (the source's `α₁, …, α_t`); `span_order`: the order spans
  `A` over `ℚ`; `involution_mem`: `τ` preserves it;
* `lattice : Submodule ℤ_[p] (ℚ_[p] ⊗[ℚ] A)`, finitely generated
  (`lattice_fg`) and spanning (`lattice_span`); `order_mul_mem_lattice`: the
  order preserves it; `lattice_selfDual`: `x ∈ Λ₀` exactly when `ψ(x, y)` is
  a `p`-adic integer for every `y ∈ Λ₀`, for the published extension
  `harrisHodgePELFormBaseChange C ℚ_[p]` of `ψ`;
* `order_maximal`: every finitely generated `ℤ_p`-subalgebra of
  `ℚ_[p] ⊗[ℚ] A` containing `1 ⊗ 𝒪_B` lies in the `ℤ_p`-span of `1 ⊗ 𝒪_B`,
  i.e. the completed order is maximal among orders containing it;
* `determinant`, a polynomial in the variables `Fin rank` with coefficients
  in `PrimeLocalRingOfIntegers K p`, and `determinant_map`: its image in
  `K` is the reflex determinant of the order basis transported to `K`.

The unramified hypothesis, the lattice, maximality and integral determinant
are explicit data with their defining conditions. The module does not
construct them from charts or prove that they exist for a given `p`.

### The determinant polynomial

`kottwitzReflexDeterminant` is the published descent to the cocharacter
reflex field of `kottwitzHodgeDeterminant`, the determinant on the identity
Hodge summand of the fixed Kottwitz homomorphism `h₀` (the source's `V₁`),
for a finite family of `A`. `determinant_map` uses its coefficient change
`kottwitzReflexDeterminantBaseChange` along `harrisReflexToCM`, the
published map from the reflex field to `K` determined by the distinguished
complex embedding; when `3 ≤ n` or there is a second real place it is the
equivalence `harrisReflexCMEquiv`. The polynomial is the full determinant in
the variables of the order basis, not a trace.

The coefficient ring `PrimeLocalRingOfIntegers K p` is Mathlib's
localization of `𝒪_K` at the image of the integers prime to `p`, the usual
model of `𝒪_K ⊗ ℤ_(p)`; `primeLocalRingOfIntegersToField` is its inclusion
in `K`, injective by `primeLocalRingOfIntegersToField_injective`
(`isUnit_algebraMap_of_mem_primeCompl` gives the unit condition). Hence
`determinant_eq_iff`: the integral polynomial is the unique one with the
given image in `K`. The module does not prove that the transported
coefficients lie in `𝒪_K ⊗ ℤ_(p)`; the published
`kottwitzIntegralHodgeDeterminantCoefficients` concerns families in the
integer order `harrisHodgePELIntegralOrder`.

## Derived declarations

* `orderInvolution` is `τ` restricted to the order (`coe_orderInvolution`).
* `coe_smul`: `ℤ_(p)`-scalars act on the order through `ℚ`.
* `linearIndependent_rat` and `span_rat`: the order basis is linearly
  independent over `ℚ` (clearing denominators with
  `IsLocalization.exist_integer_multiples` and using independence over
  `ℤ_(p)` and injectivity of `toRat`) and spans `A`; `ratBasis` is the
  resulting basis of `A` over `ℚ`, with `ratBasis_apply`.

## Scope

The unramified hypothesis is a field of the datum, so every datum, and every
tuple built on one, is in the source's setting at `p`. All arithmetic types
are in `Type`. No moduli functor,
level structure or representability is defined here.
