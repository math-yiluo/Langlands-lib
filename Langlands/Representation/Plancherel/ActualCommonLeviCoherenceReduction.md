# Closed common-Levi coherence from V.3.1 and dense coefficient injectivity

Module `Langlands.Representation.Plancherel.ActualCommonLeviCoherenceReduction`.
The main declaration is the conditional theorem
`Langlands.Plancherel.ActualCommonLeviCoherence.closedCommonLeviCoherence_of_v31_of_dense_injective`.
Its conclusion is exactly the published target
`ClosedCommonLeviCoherenceStatement` of
`Langlands/Representation/Plancherel/ActualCommonLeviCoherenceStatement.lean`.
It assumes two inputs, both stated as explicit hypotheses:

1. `hV31`: the published closed pairwise target
   `ActualCommonLeviV3.ClosedV31Statement` for every ordered pair of
   structural parabolic presentations `P Q`.
2. `hdense`: under the actual split-center identification
   `IsActualSplitCenter χ C`, for every presentation `P`, the unitary
   parameters `z` at which the actual coefficient map
   `ActualCommonLeviV3.coefficientMap` of `P` at `z` is injective form a
   dense subset of the unitary parameter group.

The theorem does not prove either input. It shows that, given them, the
existence, identity, composition and inverse laws, and the
continued-presentation independence in the target all follow formally.

## Provenance

The target specializes Waldspurger, *La formule de Plancherel pour les
groupes p-adiques* (2003), Lemma V.3.1 and Lemma V.3.2 with `s = t = 1`,
printed p.295 / PDF p.61 (source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
Waldspurger proves V.3.2 through the composition rule IV.1(12) of standard
intertwining operators. This module does not use that route, and none of
its declarations is a definition or result printed in the source. It is a
derived formal reduction. Uniqueness comes from the coefficient identity
of V.3.1 at points where the coefficient map is injective. It extends to
all unitary points by continuity of the regular representatives of
V.3.1. The density input is expected to come from generic irreducibility
of unitary induction (compare Waldspurger IV.2.2(i), printed p.284) together
with injectivity of matrix-coefficient maps of irreducible admissible
representations. That deduction is not part of this module.

## Weakly continuous families (general part)

For a topological space `Z` and complex vector spaces `V`, `W`, `X`:

- `IsWeaklyContinuousFamily T` for `T : Z → V →ₗ[ℂ] W` says that for every
  fixed `x : V` and every algebraic linear functional `f : W →ₗ[ℂ] ℂ`, the
  scalar function `z ↦ f (T z x)` is continuous.
- `IsLocallyFiniteFamily T` says that every `z₀` and every fixed `x` have an
  open neighbourhood `O` of `z₀`, finitely many fixed vectors `v i : W` and
  scalar functions `c i`, each continuous on `O`, with
  `T z x = ∑ i, c i z • v i` for all `z ∈ O`.

Proved facts:

- `IsLocallyFiniteFamily.comp_weaklyContinuous`: if `T` is locally finite
  and `S : Z → W →ₗ[ℂ] X` is weakly continuous, then `z ↦ S z ∘ T z` is
  weakly continuous. Near `z₀`, `f (S z (T z x))` equals
  `∑ i, c i z * f (S z (v i))`, a finite sum of products of continuous
  functions.
- `IsLocallyFiniteFamily.weaklyContinuous`: take `S` to be the constant
  identity family.
- `IsWeaklyContinuousFamily.eq_of_eqOn_dense`: two weakly continuous
  families that agree on a dense set agree everywhere. For fixed `x` and
  every functional `f`, the two continuous scalar functions agree on a dense
  set, hence everywhere because `ℂ` is Hausdorff. Algebraic functionals
  separate the points of a complex vector space
  (`Module.forall_dual_apply_eq_zero_iff`).

## Fixed compact carriers

`continuous_unitaryParameter` proves that the inclusion
`ActualCommonLeviV3.unitaryParameter` of unitary parameters into all
unramified parameters is continuous for the subspace topologies.

`pairValue P Q T z` is `ActualCommonLeviV3.compactValue` for the
presentations `P`, `Q`. It is the comparison `T z`, conjugated by the
published `compactTensorEquiv` isomorphisms to the fixed compact
carriers `compactFiber`, which do not depend on `z`.
`presentationCoefficientMap P z` abbreviates the actual
`ActualCommonLeviV3.coefficientMap` of `P` at `z`, with the given compact
Haar probability and central data.

- `pairValue_apply`: `pairValue P Q T z (e_P v) = e_Q (T z v)`, where
  `e_P` and `e_Q` are the two compact tensor equivalences at the parameter.
- `eq_of_pairValue_eq` and `pairValue_congr`: at a fixed `z`, the value
  `pairValue P Q T z` determines `T z` and is determined by it. Both
  equivalences are bijective.
- `pairValue_eq_id_iff`: `T z v = v` for all `v` exactly when
  `pairValue P P T z` is the identity map.
- `pairValue_comp_eq_iff`: `T₁₂ z (T₀₁ z v) = T₀₂ z v` for all `v` exactly
  when the composite of the two carrier values equals the third.
- `isLocallyFinite_of_regularUnitaryExtension`: if `T` satisfies
  `IsRegularUnitaryExtension` for some continued pairs `p q`, then
  `pairValue P Q T` is locally finite. Near a unitary point the regular
  extension gives an ambient open set `U`, a polynomial numerator `N` and
  a regular denominator `b` nonvanishing on `U`. Every unitary `w` with
  parameter in `U` satisfies `pairValue P Q T w = (b w)⁻¹ • N w`. Polynomiality
  of `N` writes `N w x` as a finite sum of regular functions times fixed
  vectors. Regular functions are continuous
  (`continuous_unramifiedRegularFunction`), and `b` is nonzero on `U`. So
  the coefficients `(b w)⁻¹ * c i w` are continuous on the preimage of `U`,
  which is open by continuity of the unitary inclusion.

## Pointwise uniqueness

Let `T`, `S`, `T₀₁`, `T₁₂`, `T₀₂` satisfy `PreservesCoefficientsAndForms`:
each is bijective and preserves the actual coefficient maps at every
unitary point. Suppose the source coefficient map of `P` at `z` is
injective.

- `eq_of_preservesCoefficients`: `T z = S z`. For a source vector `v`,
  surjectivity of `S z` gives `u` with `S z u = T z v`. Then
  `c_P u = c_Q (S z u) = c_Q (T z v) = c_P v`, so `u = v` by injectivity.
- `eq_self_of_preservesCoefficients`: if `T` goes from `P` to `P`, then
  `c_P (T z v) = c_P v`, so `T z v = v`.
- `comp_eq_of_preservesCoefficients`: `T₁₂ z (T₀₁ z v) = T₀₂ z v`, by the
  same argument applied to `T₀₂ z` and the coefficient chain through `Q`
  and `R`.

## The reduction

Proof of `closedCommonLeviCoherence_of_v31_of_dense_injective`. Assume
`IsActualSplitCenter χ C` and let `D_P` be the dense injectivity set of `P`.

- Every comparison satisfying `IsActualNormalizedComparison` has a locally
  finite, hence weakly continuous, carrier value. This follows from its
  `IsRegularUnitaryExtension` witness. It also satisfies
  `PreservesCoefficientsAndForms`.
- Independence: for two such comparisons `T`, `S` from `P` to `Q`, the
  carrier values agree on `D_P` by pointwise uniqueness, hence everywhere by
  density. Then `T = S` by `eq_of_pairValue_eq` at every point.
- Existence: `closedV31_iff_exists` turns each `hV31 P Q` into some
  `T P Q` satisfying `IsActualNormalizedComparison`. A choice over all
  ordered pairs gives a `ComparisonSystem`.
- Identity: the carrier value of `T P P` and the constant identity family
  are weakly continuous and agree on `D_P`, so they agree everywhere.
  `pairValue_eq_id_iff` returns this to the fibers.
- Composition: the composite of the carrier values of `T P Q` and `T Q R` is
  weakly continuous by `comp_weaklyContinuous`, since the first factor is
  locally finite. It agrees on `D_P` with the carrier value of `T P R`, so it
  agrees everywhere. `pairValue_comp_eq_iff` returns this to the fibers.
- Inverse: the published `inverseLaw_of_identity_composition`.
