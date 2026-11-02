# Common normal covers for original CM coefficient sheaves

Author: Worker 57.

For two small levels normal in a fixed coarse CM level and contained in
the full coefficient kernel, construct their actual common intersection
level. Restriction from either cover to this common cover is invertible
on the independently constructed coefficient sheaves. Their quotient
comparison equals the canonical comparison through the coefficient-kernel
sheaf, is uniquely normalized by actual restriction, and preserves
evaluation on the common cover. The two levels need not be nested.

## Parameters and retained premises

The arithmetic carriers have universe zero. Retain the totally real
number field `E`, CM number field `F`, quadratic extension `E → F`,
algebra `A` with its displayed scalar towers, central simple unitary data
`D`, imaginary quadratic number field `L` with its map into `F`, complex
embedding `τ₀`, and Harris signature charts `C`.

The following exact premises are retained from
[HarrisTaylorCMCoefficientRefinementCoherence](HarrisTaylorCMCoefficientRefinementCoherence.md):

- `pullbackTensorComparisonIsIsoStatement`,
  `PullbackTensorCompositionStatement`,
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
- `CMRepresentabilityStatement ... q`,
  `RelativeDualSchemeExistenceStatement`,
  `RelativeDualSchemeGeometryStatement` and
  `CMGeometricCoarseRigidity ... U.obj`.

The scheme tower is constructed from chosen witnesses representing the
fixed CM moduli presheaf. The finite geometric torsors and the
coefficient-kernel comparisons used below are derived by the imported
construction under these premises. No additional torsor, splitting,
desired sheaf isomorphism or compatibility equation is supplied here.
Representability, duality existence and geometry, and source rigidity
remain hypotheses.

Assume `Module.Finite ℚ A`. Let `K` be a number field, `W` a finite
`K`-module, and `ρ` an algebraic representation of
`D.rationalInvolution.baseChange K` on `W`. Fix a rational finite place
`p`, a small CM level `U`, a natural scalar `m` with `hm : m ≠ 0`,
and an exponent `k : ℕ`. Write

```text
S   = cmSchemeTower ... q
X   = S.obj U
J   = Scheme.smallEtaleTopology X
V₀  = cmHarrisCoefficientLevel D ρ p U m hm k
R   = HarrisCoefficientReductionRing K p m k
M   = cmHarrisCoefficientAction D ρ p U m hm k.
```

The full product over coefficient places above `p` and the stable-lattice
reduction are retained. The exponent may be zero. No freeness or
nontriviality assertion is made.

Choose small levels `V` and `W₁`, each normal as a subgroup of `U`, and
assume

```text
hV : V.obj.subgroup  ≤ V₀.obj.subgroup
hW : W₁.obj.subgroup ≤ V₀.obj.subgroup.
```

Write `S = cmSchemeTower ... q`, `X = S.obj U`, and use the following
notation for every small level `Y` normal in `U` and contained in `V₀`:

```text
Gᵧ = SmallCMResidualGroup D U Y
Nᵧ = cmHarrisResidualCoefficientAction ... Y ...
Zᵧ = cmHarrisRefinementTorsor ... Y hY
Bᵧ = cmHarrisRefinementCoefficientSheaf ... Y hY
eᵧ𝓏 = cmHarrisSuccessiveRefinementIso ... Y Z hY hZ.
```

Each `Nᵧ` has underlying module `M.V`. Each `Bᵧ` is constructed
independently as the invariant sheaf for the original residual action on
the cover `Zᵧ`, with the inherited inverse-right deck and inverse-unop
coefficient conventions. The comparison `eᵧ𝓏` from the imported coherence
unit is defined through the original coefficient-kernel sheaf, without
requiring a containment between `Y` and `Z`.

## The actual common normal level

`smallCMCommonLevel D V W₁` is the already constructed identity-Hecke
level `smallCMHeckeLevel D V W₁ 1`. Thus it is an actual compact open
level with the inherited smallness certificate. It is not a supplied
common-refinement witness. Write it as `T`.

`smallCMCommonLevel_subgroup` proves the exact equality

```text
T.obj.subgroup = V.obj.subgroup ⊓ W₁.obj.subgroup.
```

The proof unfolds the identity-Hecke conjugation and simplifies
multiplication and inversion by one. The theorems
`smallCMCommonLevel_le_left` and `_le_right` give the two containments
`hTV : T ≤ V` and `hTW : T ≤ W₁`, in subgroup notation. The instance
`smallCMCommonLevel_normal` proves that `T.obj.subgroup.subgroupOf
U.obj.subgroup` is normal: after rewriting the subgroup equality, it is
the intersection of the two given normal subgroups of `U`.

For the coefficient-kernel containment use `hT = hTV.trans hV`. This is
only a choice of proof of containment; the common level itself is the
identity-Hecke construction. All coefficient objects below use that same
proof, and no new containment premise is required.

Apply the published successive-refinement constructions to obtain

```text
φᵥₜ : Gₜ →* Gᵥ
φ𝑤ₜ : Gₜ →* G𝑤

aᵥₜ : Zₜ.val ⟶ (Action.res X.Etale φᵥₜ).obj Zᵥ.val
a𝑤ₜ : Zₜ.val ⟶ (Action.res X.Etale φ𝑤ₜ).obj Z𝑤.val.
```

Here `aᵥₜ` and `a𝑤ₜ` are `cmHarrisSuccessiveRefinementCover` for
`hTV` and `hTW`. Their underlying scheme maps are exactly
`S.map (smallCMInclusion D hTV)` and
`S.map (smallCMInclusion D hTW)`, respectively. The imported construction
proves that these are equivariant morphisms of the actual small-etale
objects over `X`, and that the underlying scheme morphisms are over
`Spec F`. Thus `Zₜ` is the constructed original CM common cover under the
retained exact geometric premises.

## Actual restriction maps and comparison

Let `cᵥₜ` and `c𝑤ₜ` be the published
`cmHarrisSuccessiveRefinementActionIso` for these containments. They
identify restriction of each independently factored coefficient action
with `Nₜ`, using the identity on the underlying module. Define the
following notation for actual module-sheaf maps:

```text
rᵥₜ = etaleCrossCoverMap X φᵥₜ aᵥₜ cᵥₜ.hom : Bᵥ ⟶ Bₜ
r𝑤ₜ = etaleCrossCoverMap X φ𝑤ₜ a𝑤ₜ c𝑤ₜ.hom : B𝑤 ⟶ Bₜ.
```

`cmHarrisCommonRefinementLeftMap_isIso` and
`cmHarrisCommonRefinementRightMap_isIso` prove that both maps are
isomorphisms. Each proof uses the exact published
`cmHarrisSuccessiveRefinementIso_hom` identification to rewrite the
actual cross-cover map as `eᵥₜ.hom` or `e𝑤ₜ.hom`. Invertibility then
follows from the already constructed comparison isomorphism; it is not
assumed for the actual cross-cover maps.

The main definition is

```text
eCommon = cmHarrisCommonRefinementIso ... V W₁ hV hW
        = asIso rᵥₜ ≪≫ (asIso r𝑤ₜ).symm : Bᵥ ≅ B𝑤.
```

The inverse proofs are installed explicitly when forming `asIso`.
`cmHarrisCommonRefinementIso_hom_comp` proves the normalization

```text
eCommon.hom ≫ r𝑤ₜ = rᵥₜ
```

by inverse cancellation. It has a `reassoc` variant.

`cmHarrisCommonRefinementIso_eq_successive` proves

```text
eCommon = eᵥ𝑤.
```

Its proof compares forward maps after composing with the invertible
`r𝑤ₜ`, uses the normalization above, rewrites both actual restriction maps
as the corresponding comparison homs, and applies the published
comparison composition law. Consequently,
`cmHarrisSuccessiveRefinementIso_common_comp` gives the exact equation

```text
eᵥ𝑤.hom ≫ r𝑤ₜ = rᵥₜ.
```

`cmHarrisCommonRefinementIso_hom_unique` proves that this normalization
characterizes the forward map: for every module-sheaf morphism
`f : Bᵥ ⟶ B𝑤`, if `f ≫ r𝑤ₜ = rᵥₜ`, then
`f = eCommon.hom`. The proof cancels the invertible right restriction
map. This is an equality of the original sheaf morphisms, not merely of
their underlying coefficient-module maps.

## Evaluation on the common cover

Write

```text
locₜ = J.overPullback (ModuleCat R) Zₜ.val.V
tₜ   = cmHarrisRefinementCoefficientTrivialization ... T hT.
```

The forward map of `tₜ` is the canonical invariant evaluation on this
actual cover. Let `Fᵥ` and `F𝑤` be the images of `Nᵥ` and `N𝑤` under
the corresponding base constant-sheaf action functors. Then
`cmHarrisCommonRefinementIso_evaluation` proves

```text
locₜ.map eCommon.hom ≫
    associatedEvaluationAlong J Z𝑤.val a𝑤ₜ.hom F𝑤
  = associatedEvaluationAlong J Zᵥ.val aᵥₜ.hom Fᵥ.
```

This is an equality of module-sheaf morphisms on the slice over `Zₜ`.
The proof rewrites each evaluation along forgetting using the published
successive evaluation law, obtaining
`locₜ.map e𝑤ₜ.hom ≫ tₜ.hom` and
`locₜ.map eᵥₜ.hom ≫ tₜ.hom`. Functoriality of `locₜ`, the identification
`eCommon = eᵥ𝑤`, and comparison composition then give the equation.

`cmHarrisSuccessiveRefinementIso_common_evaluation` states the same law
directly for the canonical comparison `eᵥ𝑤`. Both evaluation theorems
have `reassoc` variants. No equality of evaluation maps is a premise.

## Sources, derivation and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, supplies
the algebraic representation, stable-lattice coefficients, inverse
function-equivariance in (3.7), and finite normal quotient factorization
before (3.8). Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, PDF pp.98–99, gives the
original small-level moduli, right frame composition, and normal
finite-etale covers. III.2, printed pp.94–96, PDF pp.102–104, gives
torsion coefficients as inverse-equivariant component functions,
independence of choices, compatible coefficient and cover maps, and
composition. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The new common-cover construction and equations are internal deductions
from the published identity-Hecke intersection, normal subgroup,
original CM coefficient refinement and coherence constructions. The
sources provide the geometric and coefficient context and conventions;
this file does not attribute its Lean common-cover formulas directly to
the printed text. The construction proves independence of the two
normal kernel-contained covering levels at fixed coarse level,
representation, stable lattice, scalar and exponent, with the actual
common-cover restriction and evaluation normalizations described above.

Applicable representability and existence theorems, source rigidity,
full source-moduli and canonical-model geometry, identification with the
source's component-function sheaf, variation of coarse level or
coefficient data, arbitrary scheme inverse-image compatibility, and
completion to a lisse adic sheaf remain obligations of the surrounding
program. This focused unit does not discharge those obligations.

Only published dependencies are imported. This pair is by Worker 57,
in Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
