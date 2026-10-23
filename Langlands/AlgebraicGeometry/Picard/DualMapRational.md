# Conditional rational dualization over a base scheme

`Langlands.AbelianScheme.dualHom0` extends actual dualization of
homomorphisms to the Library's rational Hom groups:

`Hom0 A B →ₗ[ℚ] Hom0 (dualAbelian B) (dualAbelian A)`.

It works over any base scheme `S`, with the explicit endpoint data and
proofs described below. The rational Hom groups are the existing
`Hom0 A B = ℚ ⊗[ℤ] (A ⟶ B)` from `Langlands.AbelianScheme.Rational`.
No rational Hom type or composition is redefined.

## Inputs and construction

For abelian schemes `A`, `B` over `S`, the construction uses:

- actual universal-family existence proofs `hA : HasDualScheme A` and
  `hB : HasDualScheme B`;
- the seven fixed-map tensor and pullback inputs of `DualMapAdditive`:
  `pullbackTensorComparisonIsIsoStatement`,
  `PullbackTensorCompositionStatement`,
  `PullbackTensorUnitCoherenceStatement`,
  `ExplicitPullbackTensorAssociativityStatement`,
  `TensorMonoidalLeftUnitorComparisonStatement`,
  `PullbackTensorSymmetryStatement`, and `PicardZeroPullbackStatement`;
- a proof of `DualSchemeMapAdditivity preservation stability A B hA hB`;
- an ordinary inverse line bundle for each Poincare family and its
  module-sheaf evaluation isomorphism;
- pointwise proofs `DualSchemeGeometry A hA` and
  `DualSchemeGeometry B hB`.

The endpoint objects `dualAbelian A` and `dualAbelian B` abbreviate
`dualAbelianSchemeFromEvaluation` with these inputs. They retain the
actual universal parameter schemes and constructed group operations.

The definition takes the existing `dualAbelianSchemeMapAddHom`,
regards it as a `ℤ`-linear map using `toIntLinearMap`, and applies
`LinearMap.baseChange ℚ`. Consequently its value on a pure tensor is

`q ⊗ f ↦ q ⊗ dualAbelianSchemeMapFromEvaluation f`.

This formula uses the actual integral dual map defined by Poincare
pullback. The input does not supply an arbitrary rational dual map.

## Implemented formulas and proofs

`dualHom0_tmul` proves the pure tensor formula directly from scalar
extension. `dualHom0_homToHom0` is its specialization to `q = 1`,
giving compatibility with the existing `homToHom0`.

`dualHom0_unique` states that a `ℚ`-linear map agreeing with this
integral dualization on every `homToHom0 f` is `dualHom0`. The proof
uses tensor-product induction: a pure tensor is a rational scalar
multiple of `homToHom0 f`, and addition is handled by linearity.
Thus the extension is unique.

`dualHom0_id` preserves the existing rational identity `id0`. It uses
the same endpoint representability, inverse/evaluation and geometry
data on both sides, and takes the pointwise additivity proof for
`(A,A)`. The proof rewrites `id0` as `1 ⊗ id`, applies the pure tensor
formula, and uses the existing integral identity law.

For a third abelian scheme `C` with the corresponding endpoint data,
`dualHom0_comp` gives

`dual0_AC (comp0 A B C f g) =
  comp0 dualC dualB dualA (dual0_BC g) (dual0_AB f)`.

Here `f : Hom0 A B` and `g : Hom0 B C`. The three rational maps use
explicit pointwise additivity proofs for `(A,B)`, `(B,C)` and `(A,C)`.
The common endpoint `B` uses the same representability,
inverse/evaluation and geometry data in both factors. The proof
uses tensor-product induction in each argument. The pure tensor
case applies the integral reversed-composition theorem and
commutativity of rational scalar multiplication; the addition cases
use bilinearity.

## Provenance and limits

This is a derived algebraic construction using the existing rational
Hom and composition and the actual additive dual maps. It extends the
argument in `FieldDualMapRational` to arbitrary bases with explicit
pointwise inputs, leaving that field interface unchanged.

The relative integral dual convention comes from Kai-Wen Lan,
*Arithmetic compactifications of PEL-type Shimura varieties*, thesis
revision March 14, 2021, Definition 1.3.2.9, printed p.75 (PDF p.103).
The dual and universal family are Theorem 1.3.2.3 and Definition 1.3.2.5,
printed p.74 (PDF p.102). Registered source
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
The rational extension here is the scalar-extension consequence of
integral additivity, not a separate quoted theorem of that source.

The source's quasi-separated convention is retained in the separate
global relative additivity and geometry targets. This module instead
requires their pointwise conclusions explicitly, so its conditional
construction is meaningful over any scheme. It proves neither those
theorems nor existence of the supplied inverse bundles or coherence
inputs. It does not yet construct polarizations, biduality, or the
Rosati involution.
