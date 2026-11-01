# The full commutant of the regular PEL action

Worker 57. This internal derived construction identifies the full commutant
of the actual left regular algebra action with the opposite algebra. It
reuses Mathlib's regular endomorphism equivalence, constructs the comparison
with scalar-linear endomorphisms, and factors the existing Harris complex
homomorphism through that actual commutant. It also identifies the original
rational division condition with division of this commuting algebra.

## Generic algebra construction

In `Langlands.Algebra`, let `R : Type u` be a commutative ring and
`A : Type v` a ring with an `R`-algebra structure. The universes are
independent. No finite-dimensionality, central simplicity or nontriviality
is needed for the generic declarations.

`regularCommutant R A` is the actual subalgebra

```text
Subalgebra.centralizer R (Set.range (Algebra.lmul R A))
    <= Module.End R A.
```

Here `Algebra.lmul R A a` sends `x` to `a*x`, and multiplication of
endomorphisms is composition, with the right factor applied first.
`mem_regularCommutant_iff` proves that membership of an `R`-linear
endomorphism `f` is equivalent to

```text
forall a x : A, f(a*x) = a*f(x).
```

The proof evaluates each commutation equation at `x`; conversely, equality
on every `x` gives equality of the composed linear maps.

`regularEndEquivCommutant R A` is an `R`-algebra equivalence from
`Module.End A A` onto this subalgebra. Its forward map is precisely
`LinearMap.restrictScalars R`, with the algebra-linearity equation supplying
membership in the commutant. Its inverse keeps the scalar-linear map and
uses that membership equation to prove `A`-linearity. Extensionality proves
both inverse laws and the multiplication, addition and scalar laws. The
two `regularEndEquivCommutant` evaluation lemmas record these actual maps.

`regularOppositeEquivCommutant R A` composes Mathlib's
`AlgEquiv.moduleEndSelf R (A := A)` with that scalar-restriction
equivalence. It has type and formulas

```text
A^op ~=_R regularCommutant R A,
e(a)(x) = x * unop(a),
e^-1(f) = op(f(1)).
```

The forward and inverse formulas are definitional. In particular,
`regularCommutant_apply_eq` proves `f(x) = x*f(1)` by applying the
membership equation to `a=x` and the module element `1`.
Thus this is the full commutant, and each of its operators has the unique
right multiplier recovered at one. The opposite multiplication is
essential: composition of right multiplication by `b` with right
multiplication by `c` sends `x` to `(x*c)*b`.

`regularCommutant_division_iff` states

```text
(forall a : A, a != 0 -> IsUnit a) <->
  (forall f : regularCommutant R A, f != 0 -> IsUnit f).
```

The proof transports nonzeroness through the algebra equivalence and
transports units through its forward and inverse monoid maps, using
`IsUnit.op` and `IsUnit.unop` for the opposite algebra. This generic
unit property permits a zero ring; it is only called the division
condition in the actual nontrivial arithmetic specialization below.
No `DivisionRing` instance is installed.

## Existing complex action and actual Harris specialization

In `Langlands.Shimura.AlgebraInvolution.ComplexHom`, let `B` be a ring
with a real algebra structure, let `sigma` be a real algebra involution,
and let `h : ComplexHom sigma`. `rightRegularCommutant h` is the real
algebra homomorphism obtained by composing the existing
`h.rightRegular : C ->_R-alg Module.End B B` with
`regularEndEquivCommutant R B`. Its underlying scalar-linear operator is
exactly

```text
rightRegularCommutant(h)(z)(x) = x*h.hom(z).
```

The `rightRegularCommutant_opposite` equation shows that the inverse
commutant comparison sends this operator to `op(h.hom(z))`. This retains
the actual right action; the map into the opposite algebra is
multiplicative because the complex image commutes with itself.

For the arithmetic declarations in
`Langlands.Shimura.CentralSimpleUnitaryData`, `E : Type u` and
`K : Type v` are respectively totally real and totally complex number
fields, `K/E` is a quadratic algebra extension, and `A : Type w` is a
ring with `E`-, `K`- and rational algebra structures.
`D : CentralSimpleUnitaryData E K A n` retains the existing involution,
central simplicity, dimension `n^2` over `K`, and `1 < n`.

`isDivision_iff_regularCommutant` specializes the generic unit equivalence
to the rational scalar structure and the actual predicate `D.IsDivision`.
Its conclusion concerns `regularCommutant Q A`, not a commutant after
real scalar extension. The theorem requires the displayed arithmetic
structures and `[Algebra Q A]`, but omits `[NumberField E]` and both
scalar-tower instances `E/K/A` and `Q/E/A` because its proof does not use
them. The remaining existing datum supplies nontriviality of `A`, as
established in `DivisionCondition`.

For the complex homomorphism, the two scalar-tower instances are retained.
Take the existing normalized charts
`C : HarrisSignatureCharts D.toSecondKindInvolution n Phi`, where
`Phi : (E ->+* R) -> (K ->+* C)`. Put `T = R tensor_Q A` and
`h0 = (D.realPositiveKottwitzHom C).val`.
`kottwitzPELCommutantHom D C` is the actual real algebra homomorphism
from `C` into `regularCommutant R T` constructed by
`h0.rightRegularCommutant`. The equations
`kottwitzPELCommutantHom_val`, `kottwitzPELCommutantHom_apply` and
`kottwitzPELCommutantHom_opposite` prove, respectively, that

```text
inclusion(h(z)) = (D.kottwitzPELHom C z).restrictScalars R,
h(z)(x) = x*h0.hom(z),
regularOppositeEquivCommutant(R,T)^-1(h(z)) = op(h0.hom(z)).
```

These are equations of the existing operators and complex images. The
positive auxiliary involution, conjugate Hodge convention and all trace
normalizations remain those of `KottwitzRegular`. No new involution,
complex homomorphism or trace form is chosen.

## Sources, reuse and limits

Robert E. Kottwitz, *Points on some Shimura varieties over finite fields*,
JAMS 5 (1992), printed p.374 (one-based PDF p.2), specifies a left
`B`-module `V` and the homomorphism from the complex numbers into the
endomorphisms commuting with `B` after real scalar extension.
Printed p.392 (PDF p.20) imposes division of `End_B(V)` and uses
simplicity of `V` in the properness argument.
Registered source: `kottwitz-1992-points-shimura-finite-fields`,
SHA-256 `c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
This module proves the elementary regular-module comparison for that
commuting algebra and its complex action. It does not assert that the
source states the generic equivalence in this exact form.

Michael Harris and Richard Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), I.7, printed p.52 (PDF p.60), takes
the regular module `V=B` with its left `B` and right `B^op` actions
and defines the similitude group using units of `B^op` after scalar
extension. This motivates preserving the opposite algebra in the
comparison. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The general regular endomorphism equivalence is reused from pinned
Mathlib `Mathlib/Algebra/Algebra/Opposite.lean`, whose
`AlgEquiv.moduleEndSelf` extends
`RingEquiv.moduleEndSelf` in
`Mathlib/Algebra/Module/LinearMap/End.lean`. The actual left
representation is `Algebra.lmul` from
`Mathlib/Algebra/Algebra/Bilinear.lean`, and the centralizer is
`Subalgebra.centralizer` from
`Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`.
The new equivalence with this centralizer and the comparison with the
Library's chart-constructed complex action are internal derived
constructions. The environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

Division of the rational algebra need not survive real scalar extension;
no such assertion occurs here. No Neron model, torus, polarization
extension, properness, representability, scheme level, canonical-model
comparison or coefficient descent is constructed by this algebraic unit.
Those remain separate geometric obligations.
