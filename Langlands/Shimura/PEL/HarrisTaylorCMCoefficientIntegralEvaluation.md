# Integral evaluation along original CM normal coefficient refinements

Author: Worker 57.

Construct integral evaluation along actual forgetting maps between original
CM normal coefficient covers. Prove that the independently constructed
evaluations agree with integral comparison and quotient-ring restriction
of scalars. On the actual common intersection cover, prove the same
compatibilities without requiring the two covering levels to be nested.
The results include equations of morphisms and of complete isomorphisms.

## Parameters and retained geometric premises

All arithmetic carriers and coefficient modules have universe zero.
Retain the totally real number field `E`, CM number field `F`, quadratic
extension `E → F`, algebra `A` with the displayed scalar structures and
towers, and `D : CentralSimpleUnitaryData E F A n`. Assume
`Module.Finite ℚ A`. Retain the imaginary quadratic number field `L`,
its map into `F`, the embedding `τ₀ : L →+* ℂ`, and Harris signature
charts `C`.

Every named premise in the imported
[integral coherence](HarrisTaylorCMCoefficientIntegralCoherence.md) and
[integral refinement evaluation](HarrisTaylorCMCoefficientRefinementEvaluation.md)
constructions remains explicit:

- `pullbackTensorComparisonIsIsoStatement`,
  `PullbackTensorCompositionStatement`,
  `PullbackTensorUnitCoherenceStatement`,
  `ExplicitPullbackTensorAssociativityStatement`,
  `TensorMonoidalLeftUnitorComparisonStatement`, and
  `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement`, `MumfordBundlePicardZeroStatement`,
  `PicardZeroUniversalBaseChangeStatement`,
  `DualAbelianBaseChangeNaturalityStatement`, and
  `PolarizationBaseChangeStatement`;
- `RelativeFiniteWeilTransitionStatement`, the rational
  profinite-integer/adele comparison `h`, and `TorsionFiniteEtaleStatement`;
- `CMRepresentabilityStatement ... q`,
  `RelativeDualSchemeExistenceStatement`,
  `RelativeDualSchemeGeometryStatement`, and
  `CMGeometricCoarseRigidity ... U.obj`.

The representability assertion concerns the fixed original CM moduli
presheaf, with its componentwise connected, locally Noetherian and
geometric-point conditions. The scheme tower and its actual maps come
from representing witnesses for that presheaf. The imported constructions
derive finite geometric torsors under these exact premises. This file
assumes no additional scheme output, evaluation, graph splitting,
comparison isomorphism, or desired compatibility equation.

Let `K` be a number field, `W` a finite `K`-module, and `ρ` an algebraic
representation of `D.rationalInvolution.baseChange K` on `W`. Fix a
rational finite place `p`, small coarse level `U`, natural scalar `m`
with `hm : m ≠ 0`, and exponent `k : ℕ`. Write

```text
S   = cmSchemeTower ... q
X   = S.obj U
J   = Scheme.smallEtaleTopology X
R   = HarrisCoefficientIntegers K p
I   = harrisCoefficientScalarIdeal K p m
Rₖ  = HarrisCoefficientReductionRing K p m k = R / I^k
π   = Ideal.Quotient.mk (I^k)
r   = sheafCompose J (ModuleCat.restrictScalars π)
V₀  = cmHarrisCoefficientLevel D ρ p U m hm k
N   = cmHarrisCoefficientAction D ρ p U m hm k
M   = (cmHarrisCoefficientDiagram D ρ p U m hm).action (op k)
C_R = (constantSheaf J (ModuleCat R)).obj M.V
Cₖ  = (constantSheaf J (ModuleCat Rₖ)).obj N.V
c   = (constantRestrictScalarsIso J π).app N.V : r.obj Cₖ ≅ C_R.
```

The ring `R` retains the full product over coefficient places of `K`
above `p`. The chosen stable lattice, inverse-unop coefficient action
and inverse-right deck convention are those of the imported
constructions. Exponent zero is allowed. No nonzero or free reduction
module is asserted.

Choose small levels `V` and `W₁`, both normal as subgroups of `U`, with

```text
hV : V.obj.subgroup  ≤ V₀.obj.subgroup
hW : W₁.obj.subgroup ≤ V₀.obj.subgroup.
```

For any such level `Y` and containment proof `hY`, use

```text
Gᵧ = SmallCMResidualGroup D U Y
Pᵧ = cmHarrisResidualCoefficientAction ... Y ...
Nᵧ = cmHarrisRefinementIntegralAction ... Y hY
Zᵧ = cmHarrisRefinementTorsor ... Y hY
Qᵧ = cmHarrisRefinementCoefficientSheaf ... Y hY
Bᵧ = cmHarrisRefinementIntegralSheaf ... Y hY
ιᵧ = cmHarrisRefinementIntegralInclusion ... Y hY
jᵧ = cmHarrisRefinementCoefficientInclusion ... Y hY
sᵧ = cmHarrisRefinementSheafRestrictIso ... Y hY : r.obj Qᵧ ≅ Bᵧ
tᵧ = cmHarrisRefinementIntegralTrivialization ... Y hY.
```

Here `Pᵧ` is the independently factored `Rₖ`-action; `Nᵧ` is its
restriction of scalars to `R`, with underlying module `M.V`. The sheaves
`Qᵧ` and `Bᵧ` are independent invariant descents on the actual original
cover `Zᵧ`. For the integral localization put

```text
locᵧ = J.overPullback (ModuleCat R) Zᵧ.val.V.
```

Thus `tᵧ : locᵧ.obj Bᵧ ≅ locᵧ.obj C_R`. Localization means restriction
to the slice of the small-etale site over the actual cover object. All
equations below are in these categories of module sheaves.

## Independent evaluation along a nested cover

For this section assume
`hWV : W₁.obj.subgroup ≤ V.obj.subgroup`. Let

```text
aᵥ𝑤 = cmHarrisSuccessiveRefinementCover ... V W₁ hV hW hWV
eᵥ𝑤 = cmHarrisSuccessiveRefinementIntegralIso ... V W₁ hV hW
dᵥ𝑤 = cmHarrisSuccessiveRefinementIso ... V W₁ hV hW.
```

The map `aᵥ𝑤` is the published equivariant cover map. Its underlying
scheme map is exactly `S.map (smallCMInclusion D hWV)` and is over
`Spec F`. The integral comparison has type `eᵥ𝑤 : Bᵥ ≅ B𝑤`; the
quotient-ring comparison has type `dᵥ𝑤 : Qᵥ ≅ Q𝑤`.

`cmHarrisSuccessiveIntegralTrivializationAlong` constructs

```text
uᵥ𝑤 : loc𝑤.obj Bᵥ ≅ loc𝑤.obj C_R.
```

It applies `associatedTrivializationAlongOfSplitting` to `Zᵥ.val`,
the actual map `aᵥ𝑤.hom`, and the constant-sheaf action of `Nᵥ`.
The bijectivity of translated graph restrictions is proved by
`etaleTorsorSectionSplitting` from `Zᵥ.property`. Consequently this
construction uses neither `eᵥ𝑤` nor the evaluation `t𝑤`.

`cmHarrisSuccessiveIntegralTrivializationAlong_hom` identifies the
forward map with `associatedEvaluationAlong` by reflexivity. Explicitly,

```text
uᵥ𝑤.hom =
  loc𝑤.map ιᵥ ≫ productEvaluationAlong J aᵥ𝑤.hom C_R.
```

On an object `z` over `Z𝑤.val.V`, product evaluation restricts sections
along `prod.lift (z.hom ≫ aᵥ𝑤.hom) (𝟙 z.left)`. It is evaluation
of the original invariant sections along this actual forgetting map.

`cmHarrisSuccessiveRefinementIntegralIso_evaluation` proves

```text
loc𝑤.map eᵥ𝑤.hom ≫ t𝑤.hom = uᵥ𝑤.hom.
```

The proof expands both evaluations, applies the integral comparison's
invariant-inclusion normalization and localization functoriality, then
uses `coverPullback_productEvaluation`. This last theorem identifies
cover restriction followed by tautological graph evaluation with
evaluation along the cover map.
`cmHarrisSuccessiveRefinementIntegralIso_trivialization` applies
`Iso.ext` to obtain equality of complete isomorphisms:

```text
loc𝑤.mapIso eᵥ𝑤 ≪≫ t𝑤 = uᵥ𝑤.
```

## Independent scalar-restricted evaluation along forgetting

`cmHarrisSuccessiveRestrictedTrivializationAlong` first constructs the
quotient-ring evaluation along `aᵥ𝑤.hom` by the same graph-splitting
construction, now applied to the constant-sheaf action of `Pᵥ`.
Denote that quotient-ring isomorphism by `vᵥ𝑤`. The definition then
restricts scalars on the localized site and compares the constant
sheaves:

```text
r𝑤 = sheafCompose (J.over Z𝑤.val.V) (ModuleCat.restrictScalars π)
wᵥ𝑤 = r𝑤.mapIso vᵥ𝑤 ≪≫ loc𝑤.mapIso c
     : loc𝑤.obj (r.obj Qᵥ) ≅ loc𝑤.obj C_R.
```

Restriction of scalars commutes definitionally with the displayed
localization. This definition uses the independently constructed
quotient-ring evaluation and the genuine `constantRestrictScalarsIso`;
it does not define `wᵥ𝑤` through `sᵥ` or `uᵥ𝑤`.

`cmHarrisSuccessiveSheafRestrictIso_evaluationAlong` proves

```text
loc𝑤.map sᵥ.hom ≫ uᵥ𝑤.hom = wᵥ𝑤.hom.
```

It localizes the published inclusion normalization for `sᵥ`.
Functoriality and associativity reduce the result to
`productEvaluationAlong_natural` applied to `c.hom`. That naturality
equation moves the constant-sheaf comparison past graph evaluation.
The comparison `c` is retained as an actual isomorphism.
`cmHarrisSuccessiveSheafRestrictIso_trivializationAlong` uses `Iso.ext`
to prove

```text
loc𝑤.mapIso sᵥ ≪≫ uᵥ𝑤 = wᵥ𝑤.
```

Let `w𝑤 = cmHarrisRefinementRestrictedTrivialization ... W₁ hW` be
the published scalar restriction of the fine quotient evaluation.
`cmHarrisSuccessiveRefinementScalar_evaluation` and
`cmHarrisSuccessiveRefinementScalar_trivialization` prove

```text
loc𝑤.map (r.map dᵥ𝑤.hom) ≫ w𝑤.hom =
  loc𝑤.map sᵥ.hom ≫ uᵥ𝑤.hom

loc𝑤.mapIso (r.mapIso dᵥ𝑤) ≪≫ w𝑤 =
  loc𝑤.mapIso sᵥ ≪≫ uᵥ𝑤.
```

The morphism proof maps the published successive scalar square through
`loc𝑤`, substitutes the fine scalar evaluation equation at `W₁`,
and then uses the nested integral evaluation equation above. The
isomorphism proof applies `Iso.ext`.

## Evaluation on the actual common intersection cover

No containment between `V` and `W₁` is required for this section.
Reuse the published identity-Hecke intersection level

```text
T   = smallCMCommonLevel D V W₁
T.obj.subgroup = V.obj.subgroup ⊓ W₁.obj.subgroup
hTV = smallCMCommonLevel_le_left D V W₁
hTW = smallCMCommonLevel_le_right D V W₁
hT  = hTV.trans hV.
```

Its smallness and normality in `U` are proved in the imported
construction. Both actual cover maps `aᵥₜ` and `a𝑤ₜ` are instances
of the successive forgetting map. Let `uᵥₜ`, `u𝑤ₜ`, `wᵥₜ`,
and `w𝑤ₜ` be the independently constructed evaluations above,
using `hTV` and `hTW`. Put

```text
eCommon = cmHarrisCommonRefinementIntegralIso ... V W₁ hV hW
dCommon = cmHarrisCommonRefinementIso ... V W₁ hV hW.
```

These imported comparisons are formed from the actual restrictions to
the common cover, whose invertibility is proved before taking inverses.
`cmHarrisCommonRefinementIntegralIso_evaluation` proves

```text
locₜ.map eCommon.hom ≫ u𝑤ₜ.hom = uᵥₜ.hom.
```

The proof rewrites the two independent evaluations by the new nested
integral evaluation equation. It then uses functoriality, the published
identification of `eCommon` with the canonical comparison `eᵥ𝑤`,
and integral comparison composition. This proves compatibility along
both actual common-cover maps.
`cmHarrisCommonRefinementIntegralIso_trivialization` gives

```text
locₜ.mapIso eCommon ≪≫ u𝑤ₜ = uᵥₜ.
```

`cmHarrisSuccessiveRefinementIntegralIso_common_evaluation` rewrites
the same morphism equation for the canonical comparison:

```text
locₜ.map eᵥ𝑤.hom ≫ u𝑤ₜ.hom = uᵥₜ.hom.
```

Despite its name, `eᵥ𝑤` itself requires no nesting of `V` and `W₁`.
The use of the actual common cover supplies the two nested maps needed
to construct `uᵥₜ` and `u𝑤ₜ`.

`cmHarrisCommonRefinementScalar_evaluation` and
`cmHarrisCommonRefinementScalar_trivialization` prove

```text
locₜ.map (r.map dCommon.hom) ≫ w𝑤ₜ.hom =
  locₜ.map sᵥ.hom ≫ uᵥₜ.hom

locₜ.mapIso (r.mapIso dCommon) ≪≫ w𝑤ₜ =
  locₜ.mapIso sᵥ ≪≫ uᵥₜ.
```

The morphism proof localizes the published common-cover scalar square,
substitutes scalar evaluation along `a𝑤ₜ`, and applies the new
common-cover integral evaluation equation. The full-isomorphism proof
uses `Iso.ext`.

Finally, `cmHarrisCommonRefinementRestricted_evaluation` composes the
preceding morphism equation with scalar evaluation along `aᵥₜ`,
and `cmHarrisCommonRefinementRestricted_trivialization` applies
`Iso.ext`. They give

```text
locₜ.map (r.map dCommon.hom) ≫ w𝑤ₜ.hom = wᵥₜ.hom
locₜ.mapIso (r.mapIso dCommon) ≪≫ w𝑤ₜ = wᵥₜ.
```

Thus common-cover comparison preserves the independently
scalar-restricted quotient evaluation. All morphism compatibility
theorems marked `reassoc` also provide their reassociated forms.
Each displayed equality of complete isomorphisms includes agreement
of the inverse maps.

## Original sources and provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10,
supplies the algebraic representation, stable integral lattice,
inverse function-equivariance (3.7), normal quotient factorization
before (3.8), and identity-value description (3.11). Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
gives the original small-level moduli, right frame composition and
normal finite-etale covers. III.2, printed pp.94–96, one-based PDF
pp.102–104, defines stable-lattice torsion coefficients by
inverse-equivariant component functions, states choice independence,
and constructs compatible coefficient/cover maps and composition.
Registered source: `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The supplied five-page Harris *Publication with errata* list contains
no correction to these passages; this observation concerns only that
supplied list.

The new nested and common-cover integral evaluation and scalar
equations are internal deductions, rather than formulas attributed
to either source. The two evaluation constructions use the existing
original CM torsors and the generic results in
[CrossCoverEvaluation](../Coefficients/CrossCoverEvaluation.md) and
[TrivializationFromSplitting](../Coefficients/TrivializationFromSplitting.md).
The proofs use invariant-inclusion normalization, naturality of graph
evaluation, and the established comparison and scalar squares.
No desired evaluation or compatibility is added as a hypothesis.

## Scope

The unit fixes the coarse level, algebraic representation, chosen
stable lattice, scalar and exponent. It supplies actual nested and
common-cover integral evaluation compatibility, including the genuine
quotient-ring scalar comparison, under the retained exact geometric
premises.

Applicable representability, dual existence/geometry, source rigidity,
full source-moduli and canonical-model geometry, and identification of
the invariant sheaves with the original component-function sheaves
remain obligations of the surrounding program. This unit does not
construct variation of coarse level, representation, lattice, scalar
or exponent, extension of scalars, a general scheme inverse-image
comparison, or completion to a lisse adic sheaf. Allowing every nonzero
natural scalar and exponent zero is an internal extension of the
sources' positive prime-power torsion stage.

This pair uses Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
