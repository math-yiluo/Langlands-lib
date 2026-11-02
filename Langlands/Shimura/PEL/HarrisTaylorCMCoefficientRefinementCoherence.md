# Coherence of original CM coefficient normal refinements

Author: Worker 57.

For a fixed coarse CM level and fixed torsion coefficients, this derived
construction compares the independently formed coefficient sheaves at
any two normal small levels below the full coefficient kernel. If the
second level is contained in the first, the forward comparison is exactly
restriction along the original scheme forgetting map. These comparisons
satisfy identity and composition laws, including an equation for the
actual cross-cover maps, and preserve canonical evaluation.

## Parameters and retained premises

The arithmetic carriers have universe zero. Retain the totally real
number field `E`, CM number field `F`, quadratic extension `E → F`,
algebra `A` with its displayed scalar towers, central simple unitary data
`D`, imaginary quadratic number field `L` with its map into `F`, complex
embedding `τ₀`, and Harris signature charts `C`.

The following exact premises are retained from
[HarrisTaylorCMCoefficientRefinement](HarrisTaylorCMCoefficientRefinement.md):

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

For an actual forgetting map also assume
`hWV : W₁.obj.subgroup ≤ V.obj.subgroup`. Normality is in `U`; no
separate normality instance in `V` is required. Write `Gᵥ` and `G𝑤`
for `SmallCMResidualGroup D U V` and `SmallCMResidualGroup D U W₁`,
and

```text
φᵥ𝑤 = smallCMResidualQuotientMap D U V W₁ hWV : G𝑤 →* Gᵥ.
```

For each level `T` below `V₀`, write `Zₜ` for
`cmHarrisRefinementTorsor ... T hT`, `Nₜ` for its independently factored
`cmHarrisResidualCoefficientAction`, `Bₜ` for
`cmHarrisRefinementCoefficientSheaf ... T hT`, and `eₜ : B₀ ≅ Bₜ`
for `cmHarrisCoefficientRefinementIso`. Here `B₀` is the original
coefficient-kernel sheaf. All `Nₜ` have underlying module `M.V`.

## Independent actions and actual forgetting

`cmHarrisSuccessiveRefinementActionIso` constructs

```text
cᵥ𝑤 : (Action.res (ModuleCat R) φᵥ𝑤).obj Nᵥ ≅ N𝑤.
```

Its forward and inverse underlying module maps are identities, as
`_hom_hom` and `_inv_hom` state. Equivariance is proved by quotient
induction: on a representative in `U`, both quotient actions reduce to
the same original finite-torsion coefficient action.

`cmHarrisSuccessiveRefinementCover` constructs

```text
aᵥ𝑤 : Z𝑤.val ⟶ (Action.res X.Etale φᵥ𝑤).obj Zᵥ.val.
```

The theorem `_left` identifies its underlying scheme map with
`S.map (smallCMInclusion D hWV)`. The condition over `X` follows from
the scheme tower's composition law; equivariance follows from the
original `cmNormalRefinement` equation. Thus both actions and the map
belong to the original CM scheme tower.

Write `a₀ₜ` for `cmHarrisCoefficientRefinementCover ... T hT`. The
theorem `cmHarrisSuccessiveRefinementCover_triangle` proves

```text
aᵥ𝑤.hom ≫ a₀ᵥ.hom = a₀𝑤.hom.
```

It reduces the underlying scheme maps to the tower functor's composition
law and `smallCMInclusion_trans`. The theorem `_over` also proves

```text
aᵥ𝑤.hom.left ≫ (chosen representation at V).base.obj.hom
  = (chosen representation at W₁).base.obj.hom,
```

so forgetting is over the original `Spec F`.

## Comparison and inclusion normalizations

The main definition is

```text
eᵥ𝑤 = cmHarrisSuccessiveRefinementIso ... V W₁ hV hW
     = eᵥ.symm ≪≫ e𝑤 : Bᵥ ≅ B𝑤.
```

This definition needs no containment `hWV`: both levels are compared
through their canonical comparisons with `B₀`. Its interpretation as a
map along actual forgetting uses `hWV`.

Let `T` be the common base constant-module sheaf, and let
`iₜ : Bₜ ⟶ (productSheaf J Zₜ.val.V).obj T` be
`cmHarrisRefinementCoefficientInclusion`. These are the actual invariant
inclusions, with the imported inverse-right deck and inverse-unop
coefficient conventions. The forward normalization is

```text
eᵥ𝑤.hom ≫ i𝑤
  = iᵥ ≫ coverPullback J aᵥ𝑤.hom T.
```

`cmHarrisSuccessiveRefinementIso_hom_inclusion` proves this from the
original comparison's forward inclusion law, the cover triangle,
`coverPullback_comp`, and the original inverse inclusion law.
The inverse normalization is

```text
eᵥ𝑤.inv ≫ iᵥ ≫ coverPullback J aᵥ𝑤.hom T = i𝑤.
```

Its proof composes the forward equation with the inverse and cancels the
isomorphism. Both theorems have `reassoc` variants.

The theorem `cmHarrisSuccessiveRefinementIso_hom` proves the exact
identification

```text
eᵥ𝑤.hom = etaleCrossCoverMap X φᵥ𝑤 aᵥ𝑤 cᵥ𝑤.hom.
```

It applies the generic `crossCoverMap_inclusion` to the constant-sheaf
image of `cᵥ𝑤.hom`, removes its identity underlying coefficient map by
functoriality, and uses `hom_ext` for the invariant sheaf. Thus the
comparison through `B₀` is proved to be the original cross-cover map;
that identification is not a premise.

`cmHarrisSuccessiveRefinementIso_triangle` additionally proves
`eᵥ.hom ≫ eᵥ𝑤.hom = e𝑤.hom`, by associativity and inverse
cancellation.

## Identity and composition

`cmHarrisSuccessiveRefinementCover_refl` proves that the underlying site
morphism for `V = W₁` and reflexive containment is the identity. It uses
`smallCMInclusion_refl` and functorial preservation of identities.
`cmHarrisSuccessiveRefinementIso_refl` proves that the comparison of
`Bᵥ` with itself is `Iso.refl Bᵥ`.

Let `V₂` be a third small level normal in `U`, with `h₂ : V₂ ≤ V₀`
(in subgroup notation). Independently of nesting, the comparison laws
are

```text
eᵥ𝑤 ≪≫ e𝑤₂ = eᵥ₂
eᵥ𝑤.hom ≫ e𝑤₂.hom = eᵥ₂.hom.
```

The first is `cmHarrisSuccessiveRefinementIso_comp`, proved by
cancelling the intermediate `e𝑤.hom ≫ e𝑤.inv`. The second is its
image under `Iso.hom`, named `_hom_comp`.

If `h₂W : V₂ ≤ W₁` and `hWV : W₁ ≤ V`, the theorem
`cmHarrisSuccessiveRefinementCover_comp` proves
`a𝑤₂.hom ≫ aᵥ𝑤.hom = aᵥ₂.hom`, where the direct map uses
`h₂W.trans hWV`. The proof again uses the actual tower's composition
law. Finally, `cmHarrisSuccessiveCrossCoverMap_comp` proves

```text
etaleCrossCoverMap X φᵥ𝑤 aᵥ𝑤 cᵥ𝑤.hom ≫
    etaleCrossCoverMap X φ𝑤₂ a𝑤₂ c𝑤₂.hom
  = etaleCrossCoverMap X φᵥ₂ aᵥ₂ cᵥ₂.hom.
```

It rewrites each actual cross-cover map as the corresponding comparison
hom and applies `_hom_comp`. No unproved generic composition theorem
or equality of comparison maps is assumed.

## Evaluation

Let `loc𝑤 = J.overPullback (ModuleCat R) Z𝑤.val.V`, and let
`t𝑤 = cmHarrisRefinementCoefficientTrivialization ... W₁ hW`. Its
forward map is canonical invariant evaluation on the finer cover. Write
`Fᵥ` for the base constant-sheaf action associated to `Nᵥ`.
The theorem `cmHarrisSuccessiveRefinementIso_evaluation` proves

```text
loc𝑤.map eᵥ𝑤.hom ≫ t𝑤.hom
  = associatedEvaluationAlong J Zᵥ.val aᵥ𝑤.hom Fᵥ.
```

The right-hand side evaluates the intermediate-cover invariant sheaf
along actual forgetting from the finer cover. The proof applies
`crossCoverMap_evaluation`, removes the identity constant coefficient
map by functoriality, and uses the exact forward-map identification.
This is an equality of module-sheaf morphisms on the slice over the
finer cover, with a `reassoc` variant.

## Sources, derivation and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, supplies
the algebraic coefficient and stable-lattice setup, inverse
function-equivariance in (3.7), and finite normal quotient factorization
before (3.8). Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, PDF pp.98–99, describes
the original small-level moduli, right frame composition, and normal
finite-etale covers. III.2, printed pp.94–96, PDF pp.102–104,
describes torsion coefficients by inverse-equivariant component
functions, independence of choices, compatible cover and coefficient
maps, and their composition. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The implemented comparisons and their equations are internal deductions
from the published CM normal-refinement and generic invariant-sheaf
constructions. They concern fixed coarse level, representation, stable
lattice, scalar and exponent. They do not construct common normal
refinements, vary the coarse level or coefficient data, identify the
sheaves with the source's component-function model, construct arbitrary
scheme inverse-image compatibility, or complete the lisse adic sheaf.
The applicable representability and existence theorems, source
rigidity, and full source-moduli and canonical-model geometry remain
obligations of the surrounding task.

Only published generic work is imported. This pair is by Worker 57, in
Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
