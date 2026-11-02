# Symmetry of the canonical cubic bundle under inversion

Module `Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleSymmetry`.

This module proves that the cubic bundle `M = a.cubicBundle` of a datum `a` is
symmetric: its pullback by multiplication by `-1` is isomorphic to `M`. This is the
symmetry hypothesis of the statement
`GroupScheme.FieldSymmetricMultiplicationPullbackStatement`, which then gives
`[n]^* M ≅ M^(n·n)`.

## Setting

The section `Poincare` uses the data of the Library module
`Picard.PoincareDiagonalClasses`: an abelian scheme `A` over `S` with a dual scheme
(`hA`, `geometryA`, `MA`, `evaluationA`) and the constructor hypotheses
`preservation`, `stability`, `composition`, `unitCoherence`, `associativity`,
`comparison`, `symmetry`. `DA` denotes `dualAbelianSchemeFromEvaluation …`, the dual
abelian scheme, whose underlying scheme is `dualScheme A hA`. `P` is the Poincaré
family and `[P(z, x)]` is `familyPointClass preservation A P z x` in the commutative
group `LineBundle.IsoClasses`. Inverses of points `Z ⟶ DA.X` and `Z ⟶ A.X` are the
inverses in the groups of sections of the group objects.

## Inversion of Poincaré classes

These lemmas use the bilinearity of Poincaré classes from `PoincareDiagonalClasses`,
`familyPointClass_poincareFamily_mul_left` and
`familyPointClass_poincareFamily_mul_right`. The `_right` lemmas use `stability`.

- `familyPointClass_poincareFamily_one_left`: `[P(1, x)] = 1`.
- `familyPointClass_poincareFamily_inv_left`: `[P(u⁻¹, x)] = [P(u, x)]⁻¹`.
- `familyPointClass_poincareFamily_one_right`: `[P(z, 1)] = 1`.
- `familyPointClass_poincareFamily_inv_right`: `[P(z, x⁻¹)] = [P(z, x)]⁻¹`.
- `familyPointClass_poincareFamily_inv_inv`: `[P(u⁻¹, x⁻¹)] = [P(u, x)]`.

In each case the proof is the same. Bilinearity gives `[P(1, x)] = [P(1, x)]·[P(1, x)]`,
so `[P(1, x)] = 1`. It also gives `[P(u⁻¹, x)]·[P(u, x)] = [P(1, x)] = 1`. The same
argument works in the second variable.

## Diagonal Poincaré bundles

`isoClass_pullback_neg_poincareDiagonalBundle` takes a homomorphism of group objects
`lam : A.toGrp ⟶ DA.toGrp`. Write `λ = lam.hom.hom` and `[-1] = multiplication A.toGrp (-1)`.
The theorem states that the line bundle `[-1]^* (1, λ)^* P` and the line bundle
`(1, λ)^* P` have the same class. Here `(1, λ)^* P` is `poincareDiagonalBundle A hA λ`.

Proof. Apply the Library lemma `isoClass_pullback_poincareDiagonalBundle` at the point
`[-1]`. It gives `[[-1]^* (1, λ)^* P] = [P([-1] λ, [-1])]`. Apply it again at the
identity point. Together with `LineBundle.pullbackHom_id`, this gives
`[(1, λ)^* P] = [P(𝟙 λ, 𝟙)]`. On sections, `[-1]` is the inverse `(𝟙 A.X)⁻¹` of the
identity (`GroupScheme.multiplication_hom`). Since `λ` is a monoid morphism,
`(𝟙)⁻¹ λ = (𝟙 λ)⁻¹` (Mathlib's `GrpObj.inv_comp`). The claim is then
`familyPointClass_poincareFamily_inv_inv` with `u = 𝟙 λ` and `x = 𝟙`.

## The datum's bundles

Let `a : Datum P S g d n`.

- `Datum.isoClass_pullback_neg_canonicalBundle`: `[[-1]^* L] = [L]` for the canonical
  bundle `L = a.canonicalBundle`. By definition, `L = (1, λ)^* P` with
  `λ = a.dualWitness.parameterMap P a.polarization = (groupHom a.polarization).hom.hom`.
  So this is the previous theorem with `lam = groupHom a.polarization`.
- `Datum.pullbackNegCubicBundleIso` (definition): an isomorphism `[-1]^* M ≅ M` of
  module sheaves, where `M = a.cubicBundle` is `L^⊗3`. `LineBundle.isoClass_eq_iff`
  turns the equality of classes above into the existence of an isomorphism
  `[-1]^* L ≅ L` of line bundles; the definition chooses one, `e`, with
  `Nonempty.some`. The isomorphism is the composite of `actualPullbackTensorPowIso`,
  the isomorphism `[-1]^* (L^⊗3) ≅ ([-1]^* L)^⊗3`, with `tensorPowIso e 3`, the cube
  of the underlying sheaf isomorphism of `e`. It depends on the choice of `e`; only its
  existence is used downstream.
- `Datum.nonempty_pullback_neg_cubicBundle_iso`: there is an isomorphism
  `[-1]^* M ≅ M`, namely `Datum.pullbackNegCubicBundleIso`.

## Scope and provenance

This is an internal lemma for the published target
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundStatement`
(Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed., Prop. 7.7). Mumford's
proof uses that `M` is symmetric, so that `[n]^* M` is `M^(n²)`. In the literature,
`(1, φ)^* P` is symmetric because `[-1]^∨ = [-1]` and `P` is bilinear. Here this is
derived directly from the Library's class-level bilinearity of the Poincaré family. No
hypothesis is added beyond those of the datum and its `Prerequisites`.
