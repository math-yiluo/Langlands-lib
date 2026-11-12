# Proof of the Euler-characteristic square formula for the ample Mumford map

Lean module: `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleMumfordEulerSquareProof`.

Main theorem: `Langlands.AbelianScheme.algClosedFieldAmpleMumfordEulerSquare :
AlgClosedFieldAmpleMumfordEulerSquareStatement.{u}`. This is the exact target statement of
module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleMumfordEulerSquareStatement`.
The proof is unconditional and keeps the arbitrary universe `u`.

The target is the algebraically closed field case of J. S. Milne, *Abelian Varieties*,
Theorem 13.3 (a) (p.25), and of Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
Proposition 6.13 (iii) (printed p.123). The proof follows the outline in the statement's
Markdown. It also follows Edixhoven, van der Geer and Moonen, *Abelian Varieties*, proof of
(9.11), formulas (7)–(10), printed pp.131–132. The geometric work is in two published Library
theorems:

- `Langlands.AbelianScheme.algClosedFieldMumfordDualEuler :
  AlgClosedFieldMumfordDualEulerStatement.{u}` (module
  `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerProof`), the dual-side
  Euler characteristic `χ(A ×_K A, m^* N ⊗ snd^* M) = (-1)^g · f.left.finrank y`;
- `Langlands.AbelianScheme.algClosedFieldEulerInverseSymmetry :
  AlgClosedFieldEulerInverseSymmetryStatement.{u}` (module
  `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldEulerInverseSymmetryProof`), the identity
  `χ(M) = (-1)^g χ(N)` for an inverse `M` of a line bundle `N`.

This module combines them with other published Library results. The module first proves the
reduction to these two inputs as hypotheses, then applies it to the two published theorems.

## Notation

Fix the data of the target statement: `preservation`, `square`, an algebraically closed field
`K`, an abelian scheme `A` over `Spec K` with dual witness `hA`, a line bundle `L`, finiteness
`h` of its cohomology, normalization data `B`, `evaluationB`, `M`, `evaluation`, the Mumford
map `f` with `hf : f = mumfordSchemeMapOfLineBundle …`, the premises `IsFinite f.left` and
`Flat f.left`, and a point `y` of `dualScheme A hA`. The ampleness premise of `L` is not used
in this module; the dual-side input does not require it.

- `N` is the normalized line bundle
  `(RigidifiedLineBundle.forget (unitSection A)).obj (LineBundle.normalize preservation A.X.hom
  (unitSection A) (unitSection_comp A) L B evaluationB)`. Its underlying module is the carrier
  `L ⊗ π^* B` that appears in the target and in `evaluation`.
- `Q = m^* N ⊗ snd^* M` on the parameter-first self-product `mumfordProduct A`.
- `χ` is the Library's `eulerCharacteristic` of `relativeCohomology`.

## Declarations

### `Tate.exists_hasRelativeDimension` (imported from `TwoPowerTorsionDensityReduction`)

Every abelian scheme `A` over a field `K` satisfies `A.HasRelativeDimension g` for some
`g : ℕ`.

Proof. `A.X.hom` is geometrically connected over `Spec K`, so `A.X.left` is connected
(Mathlib's `GeometricallyConnected.connectedSpace_of_subsingleton`). `A.X.hom` is smooth.
The published `Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension` (a smooth
morphism with connected source has a constant relative dimension) gives `g`.

### `nonempty_normalize_carrier_iso`

Over a field, the carrier `L ⊗ π^* B` of the normalized bundle is isomorphic to `L`.

Proof. Every line bundle on `Spec K` is trivial (`fieldLineBundleTriviality`), so
`B ≅ 𝒪_{Spec K}`. Pulling back along `π = A.X.hom` and composing with `pullbackUnitIso` gives
`π^* B ≅ 𝒪_A`. Tensoring with `L` (`tensorFunctor`) and applying the right unitor
`tensorRightUnitor` gives `L ⊗ π^* B ≅ L ⊗ 𝒪_A ≅ L`.

### `algClosedFieldAmpleMumfordEulerSquare_of_dual_of_symmetry`

**Statement.** `AlgClosedFieldMumfordDualEulerStatement.{u} →
AlgClosedFieldEulerInverseSymmetryStatement.{u} →
AlgClosedFieldAmpleMumfordEulerSquareStatement.{u}`.

**Proof.** Introduce the target's data and choose `g` by
`Tate.exists_hasRelativeDimension` (imported from `TwoPowerTorsionDensityReduction`).

1. Finite cohomology. `N` and `M` are line bundles on the smooth proper `A`, so
   `smoothProperLineBundleFiniteCohomology` gives `hN` and `hM`. Then
   `hasFiniteCohomology_mumfordAddition_tensor_snd` gives finite cohomology `hQ` of `Q`.
2. Dual side. The hypothesis `dual`, applied to the target's data with `g` and `hQ`, gives
   `χ(Q) = (-1)^g · f.left.finrank y`.
3. Product side. The published `eulerCharacteristic_mumfordAddition_tensor_snd` (shear
   `(x, y) ↦ (x + y, y)` and Künneth) gives `χ(Q) = χ(N) · χ(M)`.
4. Inverse symmetry. `evaluation : N ⊗ M ≅ 𝒪_A`, so the hypothesis `symmetry` gives
   `χ(M) = (-1)^g χ(N)`.
5. Normalization. `nonempty_normalize_carrier_iso` and `eulerCharacteristic_eq_of_iso` give
   `χ(N) = χ(L)`.
6. Arithmetic in `ℤ`. Since `(-1)^g · (-1)^g = 1`,
   `χ(L)^2 = χ(N)^2 = (-1)^g · (χ(N) · (-1)^g χ(N)) = (-1)^g · χ(N) χ(M) = (-1)^g · χ(Q)
   = (-1)^g · (-1)^g · finrank = finrank`.

The left sides of steps 2 and 3 are the same Euler characteristic up to unfolding `N.obj` to
the carrier, so the comparison uses the definitional equality (`congrArg … e₁`).

### `algClosedFieldAmpleMumfordEulerSquare_of_dual`

**Statement.** `AlgClosedFieldMumfordDualEulerStatement.{u} →
AlgClosedFieldAmpleMumfordEulerSquareStatement.{u}`.

**Proof.** Apply `algClosedFieldAmpleMumfordEulerSquare_of_dual_of_symmetry` to the hypothesis
and to the published `algClosedFieldEulerInverseSymmetry`.

### `algClosedFieldAmpleMumfordEulerSquare`

**Statement.** `AlgClosedFieldAmpleMumfordEulerSquareStatement.{u}`.

**Proof.** Apply `algClosedFieldAmpleMumfordEulerSquare_of_dual` to the published
`algClosedFieldMumfordDualEuler`.

## Dependencies

The import closure contains neither the parent `CubicFibreCohomologyStatement` nor any other
module that mentions the target statement. Every result used is a published, proved Library
theorem. The target statement's Lean/Markdown pair and its imports are unchanged.

## Checks

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` over Library
`9c347c9e` (diagnostic `0ec5f56d-69b5-478c-9ee9-d788ccf65852`): 0 errors and 0 warnings. The
axioms of `algClosedFieldAmpleMumfordEulerSquare` are `propext`, `Classical.choice` and
`Quot.sound`.
