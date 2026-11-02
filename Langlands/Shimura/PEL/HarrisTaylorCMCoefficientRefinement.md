# Original CM coefficient sheaves under normal cover refinement

Author: Worker 57.

This derived specialization constructs an isomorphism between the original
CM coefficient sheaf formed on its full coefficient-kernel cover and the
sheaf formed independently on any smaller normal small level. The
isomorphism restricts cover sections along the actual scheme forgetting
map, preserves the coefficient module, and intertwines canonical
evaluation. The coarse level, representation, stable lattice, scalar and
exponent are fixed throughout.

## Parameters and retained premises

All arithmetic carriers lie in universe zero. Retain the totally real
number field `E`, CM number field `F`, quadratic extension structure
`E → F`, algebra `A` with the displayed scalar towers, central simple
unitary data `D`, imaginary quadratic number field `L`, its map into `F`,
the complex embedding `τ₀`, and Harris signature charts `C`.

The named premises are the following exact propositions from the
imported construction:

- `pullbackTensorComparisonIsIsoStatement`, `PullbackTensorCompositionStatement`,
  `PullbackTensorUnitCoherenceStatement`,
  `ExplicitPullbackTensorAssociativityStatement`,
  `TensorMonoidalLeftUnitorComparisonStatement` and
  `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement`, `MumfordBundlePicardZeroStatement`,
  `PicardZeroUniversalBaseChangeStatement`,
  `DualAbelianBaseChangeNaturalityStatement` and
  `PolarizationBaseChangeStatement`;
- `RelativeFiniteWeilTransitionStatement`, the rational
  profinite-integer/adele comparison `h`, and
  `TorsionFiniteEtaleStatement`;
- the exact `CMRepresentabilityStatement ... q`,
  `RelativeDualSchemeExistenceStatement`,
  `RelativeDualSchemeGeometryStatement` and
  `CMGeometricCoarseRigidity ... U.obj`.

The `cmSchemeTower ... q` is derived from the chosen witnesses representing
the fixed CM moduli presheaf. Its objects and maps are not arbitrary
schemes or supplied comparison morphisms. The representability, duality
and rigidity assertions remain hypotheses. The dominant-unramified
etale criterion is supplied by the published
`DominantUnramifiedEtaleProof.dominantUnramifiedEtale`; the caller supplies
no additional etaleness, torsor, section-splitting or sheaf-isomorphism
premise.

Assume `Module.Finite ℚ A`. Let `K` be a number field, `W` a finite
`K`-module, and `ρ` an algebraic representation of
`D.rationalInvolution.baseChange K` on `W`. Fix a rational finite place
`p`, a small CM level `U`, a natural scalar `m` with `hm : m ≠ 0`, and
an exponent `k : ℕ`. In this explanation write

```text
S      = cmSchemeTower ... q
X      = S.obj U
J      = Scheme.smallEtaleTopology X
V₀     = cmHarrisCoefficientLevel D ρ p U m hm k
R      = HarrisCoefficientReductionRing K p m k
M      = cmHarrisCoefficientAction D ρ p U m hm k.
```

`R` and `M` use the full coefficient product over the places above `p`
and the existing stable-lattice reduction. No coefficient place is
discarded. The scalar is any nonzero natural number and the exponent may
be zero; the construction makes no freeness or nontriviality assertion.

Choose another small CM level `V`, with
`(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal`, and assume precisely

```text
hV : V.obj.subgroup ≤ V₀.obj.subgroup.
```

Put `hVU = hV.trans (cmHarrisCoefficientLevel_le ...)`. Then
`cmHarrisRefinement_kernel_le` proves containment of the subgroup of `U`
defined by `V` in `cmHarrisCongruenceKernel ... m k`. Its proof rewrites
the full kernel as the subgroup defined by `V₀` and applies `hV`.
This lemma itself needs no normality instance.

## Independently factored action and original fine cover

Write `G₀ = SmallCMResidualGroup D U V₀` and
`G = SmallCMResidualGroup D U V`. The homomorphism

```text
φ = smallCMResidualQuotientMap D U V₀ V hV : G →* G₀
```

is the original residual quotient map. Define `N` to be
`cmHarrisResidualCoefficientAction ... V m k` using the proved kernel
containment. This independently factors the original coefficient action
through `G`; it is not defined by transport of the associated sheaf.
Its underlying `R`-module is definitionally `M.V`.

`cmHarrisCoefficientRefinementActionIso` constructs

```text
(Action.res (ModuleCat R) φ).obj M ≅ N.
```

The underlying forward and inverse module maps are identities, as its
two `_hom_hom` and `_inv_hom` lemmas state. Equivariance is proved by
quotient induction: on a representative `g` both actions reduce to the
same original finite-torsion coefficient action. The identity
composition laws then give the required square.

Let `Y` denote the original coefficient torsor at `V₀`.
`cmHarrisRefinementTorsor` applies
`cmNormalGeometricTorsor_of_dominantCriterion` at `V` to construct an
action `Z : Action X.Etale G` with `IsFiniteGeometricTorsor X Z`.
That predicate proves that `G` is finite, the structure morphism is
finite and scheme-surjective, and there is a unique residual translation
between any two separably closed field-valued points over the same
point of `X`. Etaleness is part of the actual small-etale object.

The lemmas `cmHarrisRefinementTorsor_left`,
`cmHarrisRefinementTorsor_hom` and
`cmHarrisRefinementTorsor_ρ_left` identify, by reflexivity, its source
with `S.obj V`, its structure map with `S.map (smallCMInclusion D hVU)`,
and each deck map with the original `cmNormalQuotientAction`.
`cmHarrisRefinementTorsor_coversTop` applies the generic covering lemma
to the proved surjectivity and obtains
`J.CoversTop (fun _ : Unit => Z.V)`.

`cmHarrisCoefficientRefinementCover` constructs the equivariant map

```text
a : Z ⟶ (Action.res X.Etale φ).obj Y.
```

Its underlying scheme map is exactly
`S.map (smallCMInclusion D hV)`, as `_left` states. The condition over
`X` follows from the tower's composition law and
`smallCMInclusion_trans`; equivariance is the existing original normal
refinement equation. The theorem `_over` also identifies the composite
of this forgetting map with the chosen structure map to `Spec F`.
Thus the map used for coefficient descent is the original scheme
forgetting morphism over the original CM field.

## Associated sheaves and the comparison isomorphism

Let `B` denote `cmHarrisCoefficientSheaf ...`, formed from `Y` and `M`.
`cmHarrisRefinementCoefficientSheaf` independently constructs

```text
Bᵥ = (etaleAssociatedFunctor X Z).obj N : Sheaf J (ModuleCat R).
```

Let `F₀` and `Fᵥ` be the actions obtained by applying the base
constant-sheaf functor to `M` and `N`, respectively, and write `T` for
their common underlying constant-module sheaf. The inclusions are

```text
i₀ : B  ⟶ (productSheaf J Y.V).obj T
iᵥ : Bᵥ ⟶ (productSheaf J Z.V).obj T.
```

The second is `cmHarrisRefinementCoefficientInclusion`.
Both sheaves are the actual limits of their diagonal actions.
`cmHarrisRefinementCoefficientInclusion_invariant` proves that
`iᵥ` composed with any diagonal action map is `iᵥ`, by
`inclusion_invariant`. The diagonal uses the inverse deck map and the
coefficient action. The imported inverse-right deck and inverse-unop
coefficient conventions are retained.

`cmHarrisCoefficientRefinementIso` constructs an isomorphism

```text
e : B ≅ Bᵥ.
```

First, the generic `etaleAssociatedCoverComparison` proves that
`etaleCrossCoverMap X φ a` with identity restricted coefficients is
invertible, using the two proved finite geometric torsors. Compose its
`asIso` with the image of the action isomorphism under
`etaleAssociatedFunctor X Z`. This constructs `e` without assuming
the desired cover-independence conclusion.

The forward inclusion normalization is

```text
e.hom ≫ iᵥ = i₀ ≫ coverPullback J a.hom T.
```

Here `coverPullback` restricts the cover coordinate along `a`, retaining
the other coordinate. The Lean proof applies `inclusion_natural` to the
constant image of the action isomorphism and
`crossCoverMap_inclusion` to the identity-coefficient comparison. Both
underlying constant coefficient maps are identities. Functorial
preservation of identities, explicit identity-composition equations
and associativity combine these equalities to give the displayed law.

`cmHarrisCoefficientRefinementIso_hom` further identifies the exact
forward morphism:

```text
e.hom = etaleCrossCoverMap X φ a
          (cmHarrisCoefficientRefinementActionIso ...).hom.
```

Its proof normalizes the right-hand side by
`crossCoverMap_inclusion` and uses `hom_ext` for invariant sheaves.
The inverse normalization is

```text
e.inv ≫ i₀ ≫ coverPullback J a.hom T = iᵥ.
```

It follows from the forward normalization by composing with `e.inv`
and cancelling `e.inv ≫ e.hom`. Both inclusion normalizations carry
`reassoc`.

## Canonical evaluation on the fine cover

Write `loc = J.overPullback (ModuleCat R) Z.V`.
`cmHarrisRefinementCoefficientTrivialization` constructs

```text
tᵥ : loc.obj Bᵥ ≅ loc.obj T
```

by `constantAssociatedTrivializationOfSplitting`, using
`etaleTorsorSectionSplitting` for the proved fine torsor.
Its forward map is the canonical invariant evaluation on `Z`: localized
inclusion followed by restriction along the tautological graph.
The target is the localization of the base constant sheaf.

The theorem `cmHarrisCoefficientRefinementIso_evaluation` proves

```text
loc.map e.hom ≫ tᵥ.hom =
  associatedEvaluationAlong J Y a.hom F₀.
```

The right side is the original coefficient-cover evaluation along the
actual forgetting map. On an object `b : T' ⟶ Z.V` of the slice,
its graph has first coordinate `b ≫ a.hom`. The proof applies
`crossCoverMap_evaluation` to the forward map identified above and
removes the identity coefficient map by functoriality. This is an
equality of module-sheaf morphisms on the slice, so it holds on the
sections of every slice object. It also carries `reassoc`.

## Sources, derivation and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, introduces
algebraic coefficients, stable integral lattices, inverse
function-equivariance in (3.7), and finite congruence-quotient
factorization before (3.8). The registered source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, PDF pp.98–99, describes the
original moduli problem, right frame composition and normal-level
Galois covers. III.2, printed pp.94–95, PDF pp.102–103, defines
torsion coefficient sheaves using inverse-equivariant functions on
components, states independence of choices and describes compatible
coefficient and cover maps. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

This pair is an internal deduction from the existing original CM
arithmetic, normal scheme torsors and generic invariant-sheaf comparison
and evaluation theorems. It establishes the displayed conditional
comparison for every normal small level below the full coefficient
kernel. It does not establish coherence for successive arbitrary
refinements, independence of the coarse level or stable lattice,
compatibility with varying scalar or exponent, identification with the
source's component-function model, arbitrary scheme inverse-image
compatibility, or the completed lisse adic sheaf. Applicable
representability and existence, source rigidity and the complete
source-moduli and canonical-model geometry remain obligations of the
surrounding task. This conditional construction does not complete them.

Only published generic constructions are reused. This pair is by
Worker 57, in Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
