# Actual positive Harris PEL input with the fixed Kottwitz Hodge sign

Worker 57. This derived construction selects one witness from the proved
`rationalHodgePolarizingTwistExists` theorem and constructs the auxiliary
positive algebra, rational alternating form and its scalar extensions.
For this same choice, the fixed Kottwitz action makes the real Hodge form
symmetric and strictly positive on every nonzero diagonal. No existence
proof or positive form is an input.

## Sources and provenance

Robert E. Kottwitz, *Points on Some Shimura Varieties over Finite Fields*,
JAMS 5 (1992), printed p.374 (PDF p.2), requires a positive left
involution, a nondegenerate alternating rational form, its adjoint identity,
and a complex homomorphism whose associated form `(v,h(i)w)` is positive
and symmetric. Printed p.375 (PDF p.3) distinguishes this homomorphism
from its inverse in the Shimura-datum convention. Section 5, printed
p.389 (PDF p.17), restates the algebraic PEL data before adding orders,
lattices and levels. The registered source is
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.

Michael Harris and Richard Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), section I.7, printed p.52 (PDF p.60),
uses the skew-unit trace form and its conjugated right adjoint. The
registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
No source-specific errata note was found in the consulted project notes.

This module is a derived specialization of `RationalHodgeTwistProof`,
`PositiveInput`, `TracePairingBaseChange`, `HodgeTraceForm`,
`TraceSimilitudesBaseChange` and `KottwitzRegular`. The existence proof
in the first of those modules is already proved separately. Here its
one chosen unit is used consistently for all the constructions and
their proved properties. The normalized trace is the Library's
`(1/n) Tr(L_a)`, with rational trace of left multiplication. No equality
with an unnormalized trace expression in the sources is asserted.

## Inputs and the single chosen witness

The inputs have independent universe levels:

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

`D` supplies the central simple CM algebra with its original involution
`σ`, finite dimension `n²` over `K` and `1 < n`. The charts `C` are for
that original involution. Let
`h₀ = (D.realPositiveKottwitzHom C).val.hom` and `T = ℝ ⊗[ℚ] A`.
The existing `D.kottwitzPELHom C` is the actual complex action
`h(z)(x) = x h₀(z)` on the left regular module.

`harrisHodgePELUnit` chooses `β : Aˣ` directly from
`D.rationalHodgePolarizingTwistExists C`.
`harrisHodgePELUnit_skew` extracts `σ(β) = -β`. The choice is not made
from the weaker auxiliary-positivity theorem: both positivity
conclusions must apply to this same unit. No equality with the
previous `harrisPositivePELUnit` is needed or asserted.

## Constructed algebra and form

`harrisHodgePELAlgebra` is the actual `skewTwist` by this unit:

```text
τ(a) = β σ(a) β⁻¹.
```

It retains the underlying number fields and algebra, central action,
simplicity, dimension and finiteness. Its rational involution extended
to `ℝ` is positive by `harrisHodgePELAlgebra_isPositive`, extracted from
the same existence theorem.

The inverse `γ = β⁻¹` is skew for `τ`
(`harrisHodgePEL_inverse_skew`). `harrisHodgePELForm` is the existing
normalized trace construction for this auxiliary datum and `γ`:

```text
ψ(x,y) = (1/n) Tr(L_(x γ τ(y)))
       = (1/n) Tr(L_(x σ(y) γ)).
```

Alternation and nondegeneracy follow from the published trace-pairing
theorems. `harrisHodgePELForm_left` gives `τ` as the adjoint of left
multiplication. `harrisHodgePEL_rightAdjoint` cancels the two inverse
skew twists and proves equality with the original rational involution
`σ`. Consequently `harrisHodgePELForm_right` gives `σ` as the adjoint
of right multiplication.

For every commutative rational algebra `S : Type z`,
`harrisHodgePELFormBaseChange` is literally `ψ.baseChange S`.
Its equality with the existing trace-pairing base change and its
pure-tensor formula are proved:

```text
ψ_S(s ⊗ x,t ⊗ y) = map_Q,S(ψ(x,y)) (s t).
```

The extended form is alternating and nondegenerate, and the extended
left and right adjoints are respectively `τ_S` and `σ_S`. These
theorems permit zero divisors and nilpotents in `S`; they do not
replace a section-ring assertion by a geometric-fibre calculation.
Nondegeneracy uses the existing finite-dimensional base-change theorem.

## The fixed action and its signed Hodge form

`harrisHodgePELPolarizationForm` constructs the real bilinear form

```text
H(x,y) = ψ_R(x,h(i)y) = ψ_R(x,y h₀(i)).
```

It is the existing `kottwitzTraceHodgeForm` specialized to this same
`β`. The application theorem is definitional. Its symmetry is the
published generic symmetry theorem. Its strict positive diagonal
(`harrisHodgePELPolarizationForm_pos`) is the signed positivity clause
of the existence proof for the chosen unit.

`harrisHodgePELHom_adjoint` and `harrisHodgePELHom_normSq` specialize
the proved regular-action identities:

```text
ψ_R(h(z)x,y) = ψ_R(x,h(conjugate z)y),
ψ_R(h(z)x,h(z)y) = normSq(z) ψ_R(x,y).
```

The second identity holds also at `z = 0`. The action is the original
fixed `h₀`, with no new choice of complex homomorphism or sign.

## Original Harris group

`harrisHodgePELSimilitudesEquiv` identifies the opposite original
rational Harris similitude group with the `A`-linear similitudes of
`ψ`. `harrisHodgePELBaseChangeSimilitudesEquiv` does the same over
every commutative rational algebra `S`. These are specializations
of the existing algebraic trace-similitude equivalence. The opposite
group is required for right multiplication. Application and multiplier
theorems prove, in both cases, that the action is `x ↦ xg` and the
multiplier equals the original one.

`harrisHodgePELHom_units_comparison` definitionally identifies the
constructed complex action on units with this same scalar-extended
similitude equivalence applied to the actual Kottwitz complex unit.

This unit constructs the rational algebra, form, action and positivity
prerequisites. The name “polarization form” refers to the real form
`H`; it does not supply a polarization morphism of an abelian scheme.
Orders, integral self-dual lattices, finite-place conditions, reflex
coefficient descent, the Lie-section determinant condition and a
representing PEL scheme remain separate obligations.
