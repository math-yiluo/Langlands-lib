# Fixed-Haar additive-character scaling for local-constant systems

Author: Worker 46.

`Langlands.LocalFactor.NonabelianSystem.AdditiveCharacterScalingStatement`
is the following Prop-valued assertion. For every prime `p`, finite p-adic
field `F`, supplied common-closure reciprocity family `e`, and assignment
`ε` satisfying the existing `IsSystem F e ε`, every finite intermediate
field `E`, additive character `ψ`, additive Haar measure `μ`, nonzero scalar
`a`, Weil element `w` with `reciprocityUnits F e E w = a`, and exact virtual
class `x` satisfy

```
ε(E, ψ(a·), μ, x)
  = det(x)(w) · |a|_E^(-dim(x)) · ε(E, ψ, μ, x).
```

The equality is in `ℂ`, after coercing the unit-valued system and determinant
values. The exponent is the negative of the actual integer-valued degree on
exact K₀. It therefore includes zero and negative virtual dimensions. The
normalized absolute value is the existing `fieldData F E` normalization on
the intermediate field itself, with its actual residue cardinality. No free
cardinality or norm is supplied. A unit `a` has strictly positive normalized
absolute value, so the integral power uses no singular evaluation.

The additive character is the existing `UnitaryAdditiveCharacter.scale`,
whose proved formula is `ψ.scale a t = ψ ((a : E.field) * t)`. Canonical
local-field instances are installed explicitly, preserving the topology in
`CommonClosure.AdditiveCharacter`. The measure `μ` is exactly the same on
both sides; it is neither rescaled nor required to be self-dual.

The determinant is `ExactGrothendieckGroup.determinantCharacter`, descended
through actual short exact relations using the published determinant
multiplicativity proof. Its input is the entire continuous exact virtual
class, not a supplied irreducible decomposition or a split class. The source
writes `det(x)(a)` through class-field reciprocity. Here a preimage `w` is
quantified explicitly rather than choosing an inverse of the Weil projection.
The projection to the topological abelianization is surjective and the
supplied reciprocity component is an equivalence, so such preimages cover
all field units. The conclusion is required for every such preimage. This
formulation does not assume a determinant-value function with the desired law.

`IsSystem` includes normalized coherent reciprocity, exact additivity,
positive Haar scaling, induction in degree zero, and actual rank-one
agreement. Additive-character scaling is a conclusion of the present
statement, not another condition silently added to `IsSystem`. The existing
`NonabelianSystem.Exists` and `Unique` remain the existence and uniqueness
targets; this file neither duplicates them nor assumes an existence theorem.

## Source correspondence

The primary source is Pierre Deligne, *Les constantes des equations
fonctionnelles des fonctions L* (1973), section 5, formula (5.4), retained
PDF/internal page 48 (printed page 548). Registered source ID:
`deligne-1973-local-constants`; SHA256:
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
The displayed original formula was visually checked: the exponent for the
unchanged measure is **negative** dimension. Formula (5.3) on the same page
is the separate positive measure-scaling law. The explanation on internal
page 51 derives (5.4) from section 4.8; the supplied system specification is
the common-closure version of section 4.1 documented in `NonabelianSystem`.
The retained original is
`/home/taskhub/central-library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`.

The statement specializes the source to finite extensions of `Q_p`, complex
coefficients, nontrivial unitary additive characters, the actual continuous
exact virtual group, and one fixed algebraic closure for each base `F`.
The field and carrier parameters remain independent; representation carriers
have the established size `max uF uV` used by `CommonClosure.Virtual`.
It makes no claim of global descent between different closures, no spectral
or half-shifted formula, and no duality assertion. The plus Fourier convention
and the Deligne fixed-Haar convention are inherited from the system's actual
rank-one expression. The self-dual and half-shifted scaling laws are separate
consequences with different normalization. No theorem proof is supplied here.

## Validation

The complete target compiles and returns `Prop` with only the environment's
permitted assumptions, importing the published `ExactDeterminant` construction.
The final normal-workspace check has no errors or warnings. Compilation checks
the declaration, not the asserted mathematical theorem; independent semantic
review and publication remain separate.
