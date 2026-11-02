# Integral coherence for original CM normal coefficient covers

Author: Worker 57.

Construct comparisons between the integral coefficient sheaves independently
descended on two original CM normal covers below the full coefficient kernel.
Prove identity, composition, normalization by actual cover restriction, and
compatibility with quotient-ring scalar restriction. Construct a second
comparison from the actual common intersection cover and prove that it equals
the first comparison and is uniquely determined by its restriction equation.
The two normal covering levels need not be nested.

## Parameters and exact geometric premises

The arithmetic carriers have universe zero. Retain the totally real number
field `E`, CM number field `F`, quadratic extension `E → F`, algebra `A` with
its displayed scalar structures and towers, central simple unitary data `D`,
imaginary quadratic number field `L` mapping into `F`, complex embedding `τ₀`,
and Harris signature charts `C`. Assume `Module.Finite ℚ A`.

All the following premises of the imported
[common-refinement](HarrisTaylorCMCoefficientCommonRefinement.md) and
[integral scalar/refinement](HarrisTaylorCMCoefficientRefinementScalars.md)
constructions remain explicit:

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

The representability assertion concerns the fixed CM moduli presheaf with its
componentwise connected, locally Noetherian and geometric-point conditions.
The scheme tower is constructed from representing witnesses for that
presheaf. The imported constructions derive its normal finite geometric
torsors and the original coefficient-kernel comparison under these premises.
No new scheme, torsor, splitting, desired coefficient comparison, or desired
compatibility equation is a premise of this file. Applicable representability,
duality existence and geometry, and source rigidity remain hypotheses.

Let `K` be a number field, `W` a finite `K`-module, and `ρ` an algebraic
representation of `D.rationalInvolution.baseChange K` on `W`. Fix a rational
finite place `p`, small coarse level `U`, natural scalar `m` with `hm : m ≠ 0`,
and exponent `k : ℕ`. Use the notation

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
M   = (cmHarrisCoefficientDiagram D ρ p U m hm).action (op k)
B₀  = (cmHarrisCoefficientSystem ... m hm ...).obj (op k)
ι₀  = cmHarrisCoefficientSystemInclusion ... (op k)
C₀  = (constantSheaf J (ModuleCat R)).obj M.V.
```

`R` retains the full product over coefficient places of `K` above `p`.
The published stable-lattice reduction, inverse-unop coefficient action,
and inverse-right deck convention are retained. The exponent may be zero.
No freeness or nonzero assertion about a reduction module is added.

Choose small levels `V` and `W₁`, both normal as subgroups of `U`, with

```text
hV : V.obj.subgroup  ≤ V₀.obj.subgroup
hW : W₁.obj.subgroup ≤ V₀.obj.subgroup.
```

For any such level `Y` and containment proof `hY`, write

```text
Gᵧ = SmallCMResidualGroup D U Y
Nᵧ = cmHarrisRefinementIntegralAction ... Y hY
Zᵧ = cmHarrisRefinementTorsor ... Y hY
Bᵧ = cmHarrisRefinementIntegralSheaf ... Y hY
ιᵧ = cmHarrisRefinementIntegralInclusion ... Y hY
bᵧ = cmHarrisCoefficientRefinementCover ... Y hY
iᵧ = cmHarrisRefinementIntegralIso ... Y hY : B₀ ≅ Bᵧ.
```

Here `Nᵧ` is restriction of scalars of the independently factored residual
`Rₖ`-module action. Its underlying `R`-module is `M.V`. The sheaf `Bᵧ`
is its invariant descent on the original cover `Zᵧ`; it is constructed
independently of `iᵧ`. The map `ιᵧ` is the monomorphism into
`(productSheaf J Zᵧ.val.V).obj C₀`.

## Integral actions and comparisons

When `hZY : Z.obj.subgroup ≤ Y.obj.subgroup`, let

```text
φᵧ𝓏 = smallCMResidualQuotientMap D U Y Z hZY : G𝓏 →* Gᵧ
aᵧ𝓏 = cmHarrisSuccessiveRefinementCover ... Y Z hY hZ hZY.
```

The published cover map `aᵧ𝓏` is equivariant for `φᵧ𝓏`. Its underlying
scheme map is exactly `S.map (smallCMInclusion D hZY)` and is over `Spec F`.
This file reuses that construction.

`cmHarrisSuccessiveRefinementIntegralActionIso` constructs

```text
cᵧ𝓏 : (Action.res (ModuleCat R) φᵧ𝓏).obj Nᵧ ≅ N𝓏.
```

Its forward and inverse underlying module maps are identities, as proved by
`_hom_hom` and `_inv_hom`. Equivariance is proved by induction on the
residual quotient: for a representative in `U`, both actions reduce to the
same action of `cmHarrisTorsionSystem` at `op k`. Only identity composition
then remains.

`cmHarrisRefinementIntegralIso_inv_inclusion` proves

```text
iᵧ.inv ≫ ι₀ ≫ coverPullback J bᵧ.hom C₀ = ιᵧ.
```

It uses the published forward inclusion normalization and inverse
cancellation. The new comparison is

```text
eᵧ𝓏 = cmHarrisSuccessiveRefinementIntegralIso ... Y Z hY hZ
     = iᵧ.symm ≪≫ i𝓏 : Bᵧ ≅ B𝓏.
```

This definition needs no containment between `Y` and `Z`.
For nested levels, `cmHarrisSuccessiveRefinementIntegralIso_hom_inclusion`
and `_inv_inclusion` prove

```text
eᵧ𝓏.hom ≫ ι𝓏 = ιᵧ ≫ coverPullback J aᵧ𝓏.hom C₀
eᵧ𝓏.inv ≫ ιᵧ ≫ coverPullback J aᵧ𝓏.hom C₀ = ι𝓏.
```

The forward proof combines the original integral inclusion equation,
the triangle for the original cover maps, functoriality of cover
restriction, and the inverse inclusion equation above. The inverse
formula follows by cancellation.

`cmHarrisSuccessiveRefinementIntegralIso_hom` identifies the forward
comparison with the actual cross-cover morphism:

```text
eᵧ𝓏.hom = etaleCrossCoverMap X φᵧ𝓏 aᵧ𝓏 cᵧ𝓏.hom.
```

The proof applies the generic cross-cover inclusion formula. The constant
sheaf and product functors carry the identity coefficient map to identities.
The preceding inclusion normalization then gives equality after the target
invariant inclusion, whose monomorphism proves equality of the original
module-sheaf maps.

`cmHarrisSuccessiveRefinementIntegralIso_triangle`, `_refl`, `_comp`,
and `_hom_comp` prove

```text
iᵧ.hom ≫ eᵧ𝓏.hom = i𝓏.hom
eᵧᵧ = Iso.refl Bᵧ
eᵧ𝓏 ≪≫ e𝓏𝓌 = eᵧ𝓌
eᵧ𝓏.hom ≫ e𝓏𝓌.hom = eᵧ𝓌.hom.
```

The third and fourth equations concern any three normal levels contained
in the same coefficient kernel; no nesting is required. Their proofs
expand the canonical comparisons and cancel adjacent inverse maps.
For actual nested levels `W₂ ≤ W₁ ≤ V`,
`cmHarrisSuccessiveIntegralCrossCoverMap_comp` rewrites the three actual
cross-cover maps by the established hom identification and obtains

```text
(etaleCrossCoverMap X φᵥ𝑤 aᵥ𝑤 cᵥ𝑤.hom) ≫
    (etaleCrossCoverMap X φ𝑤₂ a𝑤₂ c𝑤₂.hom)
  = etaleCrossCoverMap X φᵥ₂ aᵥ₂ cᵥ₂.hom.
```

The direct map uses the composite subgroup containment. These are equations
of actual sheaf morphisms on `J`.

## Scalar restriction for arbitrary normal covering levels

Write `Qᵧ` for `cmHarrisRefinementCoefficientSheaf ... Y hY`,
`qᵧ` for its comparison from the coefficient-kernel `Rₖ`-sheaf,
`dᵧ𝓏 = cmHarrisSuccessiveRefinementIso ... Y Z hY hZ`, and

```text
sᵧ = cmHarrisRefinementSheafRestrictIso ... Y hY : r.obj Qᵧ ≅ Bᵧ.
```

These objects and scalar comparisons come from published constructions.
`cmHarrisSuccessiveRefinementScalar_square` proves

```text
r.map dᵥ𝑤.hom ≫ s𝑤.hom = sᵥ.hom ≫ eᵥ𝑤.hom.
```

The levels need not be nested. To prove it, precompose with the invertible
`r.map qᵥ.hom`. The quotient comparison triangle replaces
`qᵥ.hom ≫ dᵥ𝑤.hom` by `q𝑤.hom`. The published scalar/refinement
square at `W₁` replaces the resulting composite by the coarse scalar map
followed by `i𝑤.hom`. The integral comparison triangle and the published
square at `V` rewrite this as the precomposed right side. Cancellation of
the invertible precomposition proves the equation.

`cmHarrisSuccessiveRefinementScalar_iso` then applies `Iso.ext` to prove
equality of the complete isomorphisms:

```text
r.mapIso dᵥ𝑤 ≪≫ s𝑤 = sᵥ ≪≫ eᵥ𝑤.
```

The scalar comparison is the genuine invariant-descent/constant-sheaf
comparison; the proof does not replace it by an identity.

## Integral comparison through the actual common cover

Reuse `T = smallCMCommonLevel D V W₁`, the published identity-Hecke
intersection level, with

```text
T.obj.subgroup = V.obj.subgroup ⊓ W₁.obj.subgroup
hTV : T.obj.subgroup ≤ V.obj.subgroup
hTW : T.obj.subgroup ≤ W₁.obj.subgroup
hT  = hTV.trans hV.
```

Its smallness and normality in `U` are already proved. Use the original
maps `aᵥₜ`, `a𝑤ₜ` and the new integral action isomorphisms to form

```text
rᵥₜ = etaleCrossCoverMap X φᵥₜ aᵥₜ cᵥₜ.hom : Bᵥ ⟶ Bₜ
r𝑤ₜ = etaleCrossCoverMap X φ𝑤ₜ a𝑤ₜ c𝑤ₜ.hom : B𝑤 ⟶ Bₜ.
```

`cmHarrisCommonRefinementIntegralLeftMap_isIso` and
`cmHarrisCommonRefinementIntegralRightMap_isIso` prove these actual
restriction maps invertible, by identifying them with `eᵥₜ.hom` and
`e𝑤ₜ.hom`. The new definition is

```text
eCommon = cmHarrisCommonRefinementIntegralIso ... V W₁ hV hW
        = asIso rᵥₜ ≪≫ (asIso r𝑤ₜ).symm : Bᵥ ≅ B𝑤.
```

Thus this comparison is formed from actual common-cover maps after
proving their invertibility.
`cmHarrisCommonRefinementIntegralIso_hom_comp` gives

```text
eCommon.hom ≫ r𝑤ₜ = rᵥₜ.
```

The proof cancels the inverse of the right restriction map.
`cmHarrisCommonRefinementIntegralIso_eq_successive` proves

```text
eCommon = eᵥ𝑤.
```

It compares the forward maps after postcomposition with invertible
`r𝑤ₜ`, applies the normalization above, identifies the two restriction
maps with comparison homs, and uses comparison composition.
`cmHarrisSuccessiveRefinementIntegralIso_common_comp` states the
restriction equation directly for `eᵥ𝑤`.

`cmHarrisCommonRefinementIntegralIso_hom_unique` proves uniqueness:
for every morphism `f : Bᵥ ⟶ B𝑤`, if `f ≫ r𝑤ₜ = rᵥₜ`, then
`f = eCommon.hom`. It cancels the invertible right restriction map.

Finally, let `dCommon = cmHarrisCommonRefinementIso ... V W₁ hV hW`
be the independently constructed quotient-ring common-cover comparison.
`cmHarrisCommonRefinementScalar_square` and `_iso` prove

```text
r.map dCommon.hom ≫ s𝑤.hom = sᵥ.hom ≫ eCommon.hom
r.mapIso dCommon ≪≫ s𝑤 = sᵥ ≪≫ eCommon.
```

The first proof rewrites both common-cover comparisons by their proved
canonical identifications and applies the arbitrary-cover scalar square.
The second applies `Iso.ext`. Thus scalar restriction preserves the actual
common-cover comparison as a complete isomorphism. The inclusion,
triangle, hom-composition and square theorems marked `reassoc` also supply
their reassociated equations.

## Original sources and internal derivation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, supplies
the algebraic representation, stable integral lattice, inverse
function-equivariance in (3.7), and normal quotient factorization before
(3.8). The identity-value description in (3.11) explains the source's
invariant-function model. Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
gives the original small-level moduli, right frame composition, and
normal finite-etale covers. III.2, printed pp.94–96, PDF pp.102–104,
defines stable-lattice torsion coefficients by inverse-equivariant
component functions, states choice independence, and constructs
compatible coefficient/cover maps and their composition. Registered
source: `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The supplied five-page Harris *Publication with errata* list was checked;
it contains no correction to these coefficient passages. This observation
is limited to that supplied list.

The sources supply the arithmetic, geometric and coefficient conventions.
The new integral comparison formulas, their normalization and coherence,
and the scalar/common-cover equations are internal deductions from the
published original CM torsors, integral refinement and scalar squares,
quotient refinement coherence and actual identity-Hecke intersection.
They are not attributed as printed formulas in either source. The
integral action proof reduces representatives to the original torsion
action; the sheaf-map identification uses invariant inclusions; the
remaining equations follow from the established comparisons and
categorical cancellation. All imported dependencies are published. The
separate integral refinement-evaluation module is not imported.

## Scope

This focused unit establishes independence of the two normal covering
levels at fixed coarse level, algebraic representation, chosen stable
lattice, scalar and exponent, together with actual common-cover
restriction normalization and quotient-ring scalar compatibility.

It does not prove the retained applicable representability, duality
existence/geometry or rigidity assertions, full source-moduli and
canonical-model geometry, or identification of the invariant sheaf with
the source's component-function sheaf. Variation of coarse level,
representation, lattice, scalar or exponent, extension of scalars,
arbitrary scheme inverse-image compatibility, integral evaluation
compatibility on the common cover, and completion to a lisse adic sheaf
remain separate obligations. The source uses rational-prime powers;
allowing any nonzero natural scalar and exponent zero is an internal
extension of this torsion stage, not an extra source claim.

This pair is written in Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
