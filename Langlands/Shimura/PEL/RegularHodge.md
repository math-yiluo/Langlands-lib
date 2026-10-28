# The Hodge summand of the regular PEL module

This module constructs the complex Hodge summand of the actual regular
PEL module, its left-algebra representation, and the characteristic
polynomials of that representation. It derives these objects from the
published complex homomorphism. Its inputs contain no output submodule,
representation, decomposition, or polynomial.

## Sources and provenance

The principal source is Robert E. Kottwitz, *Points on Some Shimura
Varieties over Finite Fields*, JAMS 5 (1992), registered as
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
Printed p.374 (PDF p.2) defines the decomposition of the complexified
left module by the identity and conjugate actions of the complex
homomorphism. Section 5, printed p.389 (PDF p.17), repeats this
construction, observes that both summands are modules for the
complexified algebra because its left action commutes with the
homomorphism, and introduces the homogeneous determinant polynomial.
Printed p.390 (PDF p.18) imposes its equality with the polynomial on
Lie algebra sections in the moduli problem.

The regular realization here is derived from the Library's
`KottwitzRegular` module and the fixed chart construction
`realPositiveKottwitzHom`. Kottwitz allows a general left module; the
present specialization uses the left regular module of the actual
rational central simple algebra. The elementary projector construction
and Mathlib characteristic-polynomial interface are the implemented
proof route, rather than a claim that the source gives these Lean
constructions.

For the downstream Harris specialization, Harris and Taylor, *The
Geometry and Cohomology of Some Simple Shimura Varieties* (2001),
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`,
III.1, printed pp.90–91 (PDF pp.98–99), gives Lie compatibility and the
moduli functor with its level structures. This is downstream motivation;
this module proves no equivalence with those Lie conditions. No
source-specific errata note was present in the project notes consulted.

## Generic construction and exact hypotheses

In namespace `Langlands.Shimura.RegularHodge`, the input telescope is

```lean
{B : Type u} [Ring B] [Algebra ℝ B] (h : ℂ →ₐ[ℝ] B)
```

There is no commutativity assumption on `B`. Write `W = ℂ ⊗[ℝ] B`.
The homomorphism `complexifiedHom h` sends `z` to `1 ⊗ h(z)`.
`action h` is the real algebra homomorphism into complex-linear
endomorphisms of `W` with formula

\[
H(z)x=x(1\otimes h(z)).
\]

Composition of right multiplications reverses the factors. The proof
of the multiplicative homomorphism law therefore uses commutativity
of the source `ℂ`, followed by multiplicativity of `h` and associativity
in `W`; it assumes no commutativity of `W`. `action_tmul` proves

\[
H(z)(c\otimes b)=c\otimes(bh(z)),
\]

so this is the complex-linear extension of the regular right action.
`action_I_sq` and `action_I_twice` prove `J² = -1` and `J(Jx) = -x`,
where `J = H(i)`.

The submodule `submodule h` is defined by the full condition

\[
V_1=\{x\in W:\ \forall z\in\mathbb C,\ H(z)x=zx\}.
\]

Thus the convention is precisely Kottwitz's identity-action summand.
`mem_submodule_iff_I` proves that membership is equivalent to
`Jx = ix`: decompose `z` into its real and imaginary parts and use
real algebra linearity. The proof explicitly uses the scalar-tower
identity for the actual real and complex tensor actions.
`submodule_eq_eigenspace` identifies this submodule with the
`i`-eigenspace of `J`.

`conjugateSubmodule h` applies the same definition to `h` composed
with complex conjugation. `action_conj` identifies its action with
`H(conj z)`, and `mem_conjugateSubmodule_iff_I` identifies its members
by `Jx = -ix`. Consequently this is the conjugate-action summand
`V₂` for the original homomorphism.

## Left action and decomposition

`mul_mem` proves that every element of the full tensor algebra `W`
preserves `V₁` by left multiplication: associativity gives
`(bx)(1 ⊗ h(z)) = b(x(1 ⊗ h(z)))`, and complex linearity gives
`b(zx) = z(bx)`. The algebra homomorphism

```lean
leftAction h : W →ₐ[ℂ] Module.End ℂ (submodule h)
```

restricts actual left multiplication, with underlying formula
`leftAction_apply`. Its unit, zero, addition, multiplication and scalar
laws follow by equality of the underlying vectors and the corresponding
ring identities. The same generic construction applied to the conjugate
homomorphism supplies the left action on `V₂`.

`isCompl` proves complementarity. If a vector belongs to both summands,
the two eigen-equations imply `(2i)x = 0`; since `2i` is nonzero in
`ℂ`, the vector is zero. For any `x ∈ W`, define

\[
x_+=\tfrac12(x-iJx),\qquad x_-=\tfrac12(x+iJx).
\]

Using `J² = -1`, the implemented proof verifies the eigen-equations
for `x₊` and `x₋`, normalizes the complex scalar identities with
`i² = -1`, and checks `x₊ + x₋ = x`. It then proves that the sum of
the two submodules is all of `W`. `decomposition` uses Mathlib's
`Submodule.prodEquivOfIsCompl` to obtain

```lean
(submodule h × conjugateSubmodule h) ≃ₗ[ℂ] W
```

whose forward map is addition, as proved by `decomposition_apply`.
These results require no finite-dimensionality hypothesis.

For the polynomial declarations only, the additional hypothesis is
`[FiniteDimensional ℝ B]`. Scalar extension and the submodule instance
make `V₁` finite dimensional over `ℂ`. `charpoly h b` is Mathlib's
characteristic polynomial of the constructed endomorphism
`leftAction h b`. `charpoly_monic` and `charpoly_natDegree` give
monicity and degree `Module.finrank ℂ (submodule h)`, directly from
Mathlib's characteristic-polynomial theorems. This also covers the
zero-dimensional case. No numerical dimension formula is claimed.

## Actual Harris–Kottwitz specialization

In namespace `Langlands.Shimura.CentralSimpleUnitaryData`, the full
ambient telescope, with three independent universes, is

```lean
{E : Type u} {K : Type v} {A : Type w}
[Field E] [NumberField E] [NumberField.IsTotallyReal E]
[Field K] [NumberField K] [NumberField.IsTotallyComplex K]
[Algebra E K] [Algebra.IsQuadraticExtension E K]
[Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
[Algebra ℚ A] [IsScalarTower ℚ E A]
{n : ℕ} (D : CentralSimpleUnitaryData E K A n)
{Φ : (E →+* ℝ) → (K →+* ℂ)}
(C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
```

Here `E` denotes the totally real field in the Library's existing
notation, not the reflex field called `E` in Kottwitz's article.
`K` is its totally complex quadratic extension; `D` supplies the
central simple algebra with its second-kind involution and finite
dimensionality, and `C` supplies the Harris signature charts.
All these conditions remain in the unapplied declaration types.

Take `B = ℝ ⊗[ℚ] A` and
`h = (D.realPositiveKottwitzHom C).val.hom`. In particular, this uses
the fixed conjugated Kottwitz homomorphism already constructed in the
Library. No inverse cocharacter convention is substituted.
`kottwitzHodgeModule` is the resulting submodule of
`ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)`. `kottwitzHodge_complexification` proves on pure
tensors that its defining complex action extends the published
`kottwitzPELHom` action. `kottwitzHodgeAction` restricts actual left
multiplication by this double tensor algebra to the constructed
submodule, and `kottwitzHodgeAction_apply` proves the underlying formula.

Finally,

```lean
kottwitzHodgeCharpoly D C : A → Polynomial ℂ
```

sends `a` to the characteristic polynomial of left multiplication by
`1 ⊗ (1 ⊗ a)` on that actual Hodge submodule. Its body obtains
`FiniteDimensional K A` from `D.finite`, derives finite dimensionality
over `ℚ`, and uses scalar extension for the real algebra. It has no
additional finite-dimensionality or polynomial input.

## Scope

This unit constructs the actual Hodge representation needed before
forming the determinant condition. Its polynomials are univariate
characteristic polynomials, not yet Kottwitz's homogeneous polynomial
in an order basis. It does not prove coefficient descent to the reflex
field, integrality, a signature dimension formula for this whole regular
module, or equality with a polynomial on scheme sections. Those remain
subsequent obligations. It also supplies no rational skew-unit with the
required Hodge sign, polarization, moduli representability, or canonical
model theorem. The fixed homomorphism and all forms retain their
previous Library conventions.

Worker 57 authored this derived module and its proofs. The full
unapplied generic and specialized types were inspected, with direct
assignments of the unapplied complementarity, left-action and actual
characteristic-polynomial constants. The inspected declarations use
only `propext`, `Classical.choice` and `Quot.sound`. Development
compilation and these inspections do not replace independent semantic
review and publication.
