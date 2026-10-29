# An integral order for the actual positive Harris left involution

Worker 57. This module constructs a finite full integer order for the
positive auxiliary left involution of `HarrisHodgeInput`, restricts that
involution to the order, and gives a faithful left action on a concrete
finite full integer lattice in the rational regular module. The rational
form's adjoint identity holds for this same action and involution.

## Source and derived provenance

Kottwitz, *Points on Some Shimura Varieties over Finite Fields* (1992),
section 5, printed p.389 (PDF p.17), requires a finite-dimensional simple
rational algebra, a positive left involution preserving an order, and a
preserved lattice in a left module. The registered source is
`kottwitz-1992-points-shimura-finite-fields`, original SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
No source-specific errata note was found in the consulted project notes.

This is a derived specialization of the constructive `IntegralOrder`
module to the published positive auxiliary algebra from
`HarrisHodgeInput`. It uses that module's single fixed choice of skew unit
and positive left involution, and does not choose another positive twist.
The order is constructed by a lattice stabilizer and its involution-stable
core, rather than supplied as output data.

Kottwitz's full input is an order over `ℤ_(p)` whose completion is maximal,
and a self-dual preserved lattice over `ℤ_p`. The present construction is
a finite full integer order and an integer lattice. Prime-local extension,
maximality and self-duality remain separate mathematical obligations.
In particular, no claim that the rational alternating form takes integer
values on this chosen lattice is made.

## Inputs

The arithmetic types have independent universe levels:

```lean
{E : Type u} {K : Type v} {A : Type w}
[Field E] [NumberField E] [NumberField.IsTotallyReal E]
[Field K] [NumberField K] [NumberField.IsTotallyComplex K]
[Algebra E K] [Algebra.IsQuadraticExtension E K]
[Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
[Algebra ℚ A] [IsScalarTower ℚ E A]
{n : ℕ} {Φ : (E →+* ℝ) → (K →+* ℂ)}
(D : CentralSimpleUnitaryData E K A n)
(C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
```

`D` supplies an actual central simple CM algebra of dimension `n²` over
`K`, with `1 < n`, and its original second-kind involution `σ`. The charts
`C` concern that original involution and its Harris signature. The private
`rationalFinite` theorem obtains finite dimension over `E` from
`D.totallyRealBasis` and then finite dimension over the rationals by
transitivity. No additional finite-dimensionality assumption is imposed
on callers.

Let `β = D.harrisHodgePELUnit C`. The previously constructed auxiliary
algebra has left involution

```text
τ(a) = β σ(a) β⁻¹.
```

Its rational involution extended to the reals is positive by
`harrisHodgePELAlgebra_isPositive`. This is the involution used in the
order construction. The original right-adjoint involution and the fixed
Kottwitz complex action retain their existing definitions.

## The actual order and lattice

`harrisHodgePELLattice` is `PEL.basisLattice A` using the finite-dimensional
instance proved from `D`. It depends on `D` and the chosen rational basis;
it needs no signature chart. `harrisHodgePELLattice_isLattice` proves it
finite and rationally full, and `one_mem_harrisHodgePELLattice` proves
that it contains `1`.

`harrisHodgePELIntegralOrder` is `PEL.integralOrder A τ`, using the
rational restriction of the auxiliary left involution. The instances
`harrisHodgePELIntegralOrder_finite` and
`harrisHodgePELIntegralOrder_isLattice` prove finiteness over the integers
and full rational span. The theorem
`exists_int_multiple_mem_harrisHodgePELIntegralOrder` also proves that
every algebra element has a nonzero integer multiple in the order.
`involution_mem_harrisHodgePELIntegralOrder` states

```text
τ(a) ∈ O  ↔  a ∈ O.
```

`harrisHodgePELIntegralInvolution` is the integer-linear unital
multiplication-reversing involution on this actual order, and its
application formula is `τ(a)` after inclusion in `A`.

`harrisHodgePELIntegralAction` is a ring homomorphism

```text
O →+* Module.End ℤ Λ,    a ↦ (x ↦ a*x).
```

Its application formula and injectivity are proved. The latter follows
from the generic faithful lattice action, evaluated at `1`.
`harrisHodgePELIntegralOrder_mul_mem_lattice` states preservation directly
for elements of `A`. Finally `harrisHodgePELIntegralAction_adjoint`
specializes the rational trace-form theorem to order and lattice elements:

```text
ψ(a*x,y) = ψ(x,τ(a)*y).
```

Here `ψ = D.harrisHodgePELForm C` remains rational-valued; the theorem
asserts an equality of rational numbers, not an integral perfect pairing.
All the construction and property proofs specialize the generic order
and published positive-Harris modules. They do not assert a prime-local
PEL datum, abelian scheme, polarization morphism, determinant condition,
moduli representation or scheme level.
