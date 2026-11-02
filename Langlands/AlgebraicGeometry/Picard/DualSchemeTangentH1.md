# The tangent space of the chosen dual at its origin

This module proves that, over every field `k`, the tangent space of the Library's chosen
dual `dualScheme A hA` at its origin `dualOrigin A hA` is `k`-linearly equivalent to
`H¹(A, 𝒪_A)`. It needs no finiteness hypothesis on the chosen dual. It is a helper for the
proof of `Langlands.AbelianScheme.AlgClosedFieldDualSchemeRelativeDimensionStatement`, where
it supplies the upper bound `dim_k T₀(dualScheme A hA) ≤ g` in the dimension count of
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Theorem (6.18).

## Main results

All declarations are in namespace `Langlands.AbelianScheme`, for a field `k : Type u`,
`A : AbelianScheme (Spec (CommRingCat.of k))` and `hA : HasDualScheme A`.

- `dualSchemeTangentH1 A hA` gives a linear equivalence
  `Langlands.Scheme.tangentSpaceAtPoint (dualScheme A hA) (dualOrigin A hA) ≃ₗ[k]
  (DerivedSections.relativeCohomology A.X.hom 1).obj (structureSheaf A.X.left)`.
  The statement is wrapped in `Nonempty`.
- `dualSchemeTangent_finrank_le A hA g hg` assumes `hg : A.HasRelativeDimension g`. It
  shows that this tangent space is finite-dimensional over `k` and that its `finrank` is at
  most `g`.

## Relation to the full universal family

The Library already proves the same comparison for a full universal rigidified family:
`fieldUniversalRigidifiedPicardTangentH1`, at the parameter `trivialParameter`. The chosen
dual only has the universal property `IsUniversalPicardZero A (poincareFamily A hA)`, which
classifies rigidified classes satisfying the geometric Picard-zero condition
`IsPicardZeroClass`. The only new input is therefore the following fact: every first-order
class satisfies that condition.

- `dualNumber_fieldPoint_factor`: a morphism `Spec K ⟶ Spec k[ε]`, with `K` a field, factors
  through the closed point `dualNumberAugmentation k`. Write the morphism as `Spec.map φ`.
  Since `φ(ε)² = φ(ε²) = 0` in a field, `φ(ε) = 0`, so `φ(a + bε) = φ(a)` for every `a + bε`.
- `isPicardZeroClass_of_closedPoint_trivial`: let `q` be a rigidified class over the
  dual-number test `dualNumberTest k` whose pullback along `dualNumberClosedPoint k` is the
  canonical trivial class. Then `IsPicardZeroClass A q`. The proof picks a representative
  `L` and applies the published detection criterion `picardZeroGeometricDetection`, so it
  suffices to check the pullback of `L` to each geometric point `s : Spec K ⟶ Spec k[ε]`.
  By the factorization, `Over.homMk s rfl` equals `h ≫ dualNumberClosedPoint k` for a map
  `h` to the base. The pullback class is then `classesPullback h` of the trivial class,
  hence trivial (`classesPullback_trivial`). The trivial family is Picard-zero
  (`isPicardZeroFamily_trivial`). Composition of class pullbacks uses the published pullback
  coherence `RigidifiedModule.pullbackCoherence`, through the private lemma
  `classesPullback_comp'`.

The check works on every geometric point of the actual dual-number test scheme. It does not
compare the chosen dual with any other parameter scheme. Only the Library's chosen
`dualScheme A hA`, its `poincareFamily A hA` and its classification maps `dualClassify` are
used.

## Construction of the equivalence

- `dualFirstOrderClassifyingEquiv A hA` is an equivalence between dual-number points
  `t : dualNumberTest k ⟶ dualScheme A hA` with `dualNumberClosedPoint k ≫ t = dualOrigin A hA`
  and `FirstOrderClasses`, the rigidified classes over `k[ε]` with trivial restriction.
  - **Forward map.** `t` is sent to its classifying class
    `classifyingMap … (poincareFamily A hA) (dualNumberTest k) t`. The restriction is
    trivial by `classifyingMap_comp` and `dualOrigin_spec`.
  - **Inverse map.** `q` is sent to `dualClassify A hA (dualNumberTest k) ⟨q.val, _⟩`, using
    the Picard-zero lemma above. Its restriction is `dualOrigin A hA` by `dualClassify_unique`.
  - **Inverse laws.** They follow from `dualClassify_unique` and `dualClassify_spec`.
- `dualTangentDeformationEquiv A hA preservation` composes the published equivalences
  `tangentSpaceAtPointDerivationEquiv`, `rationalStalkDerivationTangentEquiv` and
  `dualNumberTangentEquiv` with `dualFirstOrderClassifyingEquiv` and the published
  `firstOrderDeformationEquiv`. The result is an equivalence of the tangent module with the
  ordinary deformation classes `DeformationClasses preservation A.X.hom`. This is the same
  chain as the published `tangentDeformationEquiv`, with the classification of the full
  universal family replaced by that of the chosen dual.
- `dualTangentDeformationEquiv_add`: addition of tangent vectors goes to the product of
  deformation classes. Inside the proof the chosen dual is given its group scheme structure
  `dualCommGroupSchemeFromEvaluation`, as in the published `fieldDualSchemeSeparated`. The
  inverse line bundle is obtained from `locallyFreeRankOneIffTensorInvertible`, and all
  coherence inputs are published proofs. Its unit is `dualOrigin A hA`
  (`dualCommGroupSchemeFromEvaluation_one`, together with the terminality of
  `Over.mk (𝟙 _)`). The published `rationalStalkDerivationPoint_add_of_one_eq` therefore
  turns the sum of derivations into the product of dual-number points. The multiplicative
  equivalence `dualCommGroupSchemePointMulEquiv` turns that product into the tensor of the
  classified Picard-zero classes. Finally `underlyingDualNumberClassEquiv_tensor` gives the
  product of ordinary classes.
- `dualTangentDeformationEquiv_smul_val`: scalar multiplication by `c` is pullback along the
  epsilon scaling `scale A.X.hom c`. The proof uses the published lemmas
  `rationalStalkDerivationPoint_smul`, `classifyingMap_comp` and
  `underlyingDualNumberClassEquiv_scale`.
- `dualSchemeTangentH1` composes the resulting additive equivalence with the published
  `deformationH1AddEquiv` for the ordered affine cover `orderedAffineCoverOfQuasiCompact`.
  `k`-linearity comes from `deformationH1AddEquiv_scaleClass`.
- `dualSchemeTangent_finrank_le` transports finite-dimensionality and the dimension bound of
  the published `fieldStructureSheafH1DimensionBound` along this equivalence.

## Imports

The module imports the published tangent-to-H¹ development for the full universal family,
the chosen dual's group scheme construction, the detection and pullback stability of the
Picard-zero condition, the rank-one/tensor-invertible comparison and the H¹ dimension bound.
Its transitive Library imports contain no module on Mumford bundles or Euler
characteristics. In particular, it imports nothing downstream of
`AlgClosedFieldAmpleMumfordEulerSquareStatement` or `AlgClosedFieldMumfordDualEulerStatement`.
