# Finite original CM normal projections from residual point orbits

This module constructs the residual orbit map into each underlying point fiber
of the original CM normal forgetting morphism. It proves that map surjective,
that every underlying point fiber is finite, and that the same original
forgetting morphism is locally quasi-finite and finite. The conclusions are
conditional on the existing exact representing witnesses and named
infrastructure, including the two relative-dual assertions described below.
Neither original-projection etaleness nor coarse-object rigidity is a premise.

## Arithmetic and infrastructure inputs

All declarations are in `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.
The parameters are a totally real number field `E`, a CM number field `F`
quadratic over `E`, a central simple unitary datum
`D : CentralSimpleUnitaryData E F A n`, an imaginary quadratic CM field `L`
mapping to `F`, and a complex embedding `τ₀` of `L`. The Harris signature
charts `C` use the constructed Harris CM section. All algebra and
scalar-tower instances in the Lean context remain explicit. The inherited
moduli retain the normalized Harris–Taylor reflex structure, positive
auxiliary involution, polarization and Weil-pairing conventions.

The named infrastructure premises are pullback-tensor preservation,
composition, unit coherence, associativity, left-unitor comparison and
symmetry; Picard-zero pullback stability, the Mumford-bundle assertion and
universal base change; dual-abelian base-change naturality; polarization
base-change stability; relative finite Weil-transition compatibility; the
actual rational/profinite-integer/adele comparison; and torsion finite
etaleness. Their exact proposition types appear in the Lean binders.
They are inherited inputs.

The point-fiber map and its value formula need only this infrastructure
and the representing witnesses. Every translation, surjectivity and
finiteness theorem additionally takes
`RelativeDualSchemeExistenceStatement` and
`RelativeDualSchemeGeometryStatement`, both at universe zero. These assert
existence of universal dual schemes and smoothness, properness and
geometric connectedness of the duals, respectively. The preceding
kernel-comparison surjectivity theorem uses them to admit the actual
algebraically closed field-test spectra through
`admissibleCMBase_iff_dualGeometry`. They assert no property of the
forgetting morphism or residual kernel comparison themselves.

## Original represented schemes and residual maps

`R` supplies the existing `CMLevelRepresentation` witness at every
`SmallCMLevel D`. Such a witness contains an actual admissible scheme over
`Spec F`, smoothness, projectivity and a representing natural isomorphism
for the fixed small-level class presheaf. This is the presheaf on
`ComponentwiseAdmissibleCMBaseCategory`, the existing locally Noetherian
bases with admissibility on their actual connected-component schemes.
Its connected factors use the unpointed compatible class towers.
The rational-isogeny quotient retains a representative satisfying the
determinant and numerical dimension conditions jointly; this construction
does not require dimension invariance under arbitrary rational isogenies.

Write `X_V` and `X_U` for the fine and coarse objects of
`representedCMSchemeTower ... R`, with explicit inclusion
`hVU : V.obj.subgroup ≤ U.obj.subgroup`. The original forgetting morphism
and residual group are

```
p = representedCMNormalProjection ... R U V hVU : X_V ⟶ X_U,
Q = SmallCMResidualGroup D U V.
```

Here `p` is the tower map at `smallCMInclusion D hVU`, and `Q` is the actual
quotient of `U.obj.subgroup` by `V.obj.subgroup.subgroupOf U.obj.subgroup`.
Normality is required for that subgroup of `U`. The finite quotient
theorem `smallCMResidualGroup_finite` is already proved from the existing
compact-open level data.

Let `ρ = representedCMNormalQuotientAction ... R U V hVU`. This is the
original action by scheme morphisms. It retains inverse-right frame
transport: a representative `g` acts through the transporter with element
`g⁻¹`. The underlying Harris opposite-group convention is unchanged.
Each `ρ(g)` preserves `p`.

The proof also uses the exact existing objects and map

```
Y = representedCMNormalCopies ... R U V = ∐ (fun _ : Q => X_V),
K = representedCMNormalKernelPair ... R U V hVU = X_V ×[X_U] X_V,
κ = representedCMNormalKernelComparison ... R U V hVU : Y ⟶ K.
```

On summand `g`, `κ` is the original graph `(identity, ρ(g))`.
The published `representedCMNormalKernelComparison_surjective` supplies
surjectivity of this same `κ` under the displayed relative-dual premises.
No isomorphism or injectivity of `κ` is used here.

## Constructed point-fiber map and transitivity

For every underlying point `x : X_V`,
`representedCMNormalPointFiberMap` is the function

```
Q → {z : X_V // p z = p x},    g ↦ ρ(g)(x).
```

The subtype proof uses the original projection-invariance equation.
`representedCMNormalPointFiberMap_val` is the reflexive equality identifying
its value with the underlying point map of the original `ρ(g)`.
The Lean expression uses `Scheme.Hom.toLRSHom` and its `.base` to expose
that actual point map.

`representedCMNormalPoint_exists_translate` starts with underlying
scheme points `x,y` satisfying `p x = p y`.
`Scheme.Pullback.exists_preimage_pullback` produces an actual point `z`
of the scheme pullback `K` with projections `x,y`. It is enough that the
map from points of the scheme pullback to the topological fiber product
is surjective; no identification of those spaces is assumed.

Surjectivity of the original `κ` gives a point `w : Y` above `z`.
The existing `sigmaMk` surjectivity theorem writes `w` as an actual point
`t` in a summand `g : Q`. The exact summand formula for `κ` identifies
the graph of `g` at `t` with `z`. Its first projection proves `t = x`,
and its second proves `ρ(g)(x) = y`. This establishes residual
transitivity on the underlying point fiber.

`representedCMNormalPointFiberMap_surjective` applies this result to
each point of the displayed subtype and uses subtype extensionality.
The conclusion is surjectivity of the constructed original orbit map.
Neither uniqueness of `g` nor freeness of this action on underlying
points is asserted.

## Finite point fibers and finiteness of the original morphism

`representedCMNormalProjection_finite_preimage_singleton` proves

```
∀ y : X_U, (p ⁻¹' {y}).Finite.
```

For an empty fiber this is immediate. Otherwise choose `x` in the fiber.
Every other point in that fiber is an original translate of `x` by the
preceding theorem. The fiber is therefore contained in the range of
`g ↦ ρ(g)(x)`. The already proved finiteness of `Q` makes that range
finite. This argument does not require a uniform choice of fiber points,
a proof of surjectivity of `p`, or injectivity of the orbit map.

`representedCMNormalProjection_locallyQuasiFinite_of_dualGeometry`
applies Mathlib's `LocallyQuasiFinite.of_finite_preimage_singleton`.
Its additional `LocallyOfFiniteType p` requirement is available from
properness of the original morphism. That properness was proved in
`HarrisTaylorCMFiniteEtale`: each representing scheme's actual
projective-space closed-immersion witness proves properness over the CM
field, and the tower's equation over that field proves properness of its
transitions.

Finally `representedCMNormalProjection_isFinite_of_dualGeometry` applies
`IsFinite.of_isProper_of_locallyQuasiFinite` to the same `p`.
Thus finiteness is proved before etaleness. The earlier
`representedCMNormalProjection_isFinite` instance in
`HarrisTaylorCMFiniteEtale` obtained finiteness under an `Etale p`
assumption; this theorem supplies a separate interface using the two
named relative-dual assertions and the derived point-fiber argument.
Neither theorem is replaced.

## Identical chosen tower

For `q : CMRepresentabilityStatement ...`, the final declarations
substitute precisely `chosenCMLevelRepresentation ... q` for `R`.
This is the family defining the existing `cmSchemeTower ... q` and
`cmNormalQuotientAction ... U V hVU q`; no second selection of
representing witnesses or transition morphisms is made.

`cmNormalPointFiberMap` explicitly has target the underlying point fiber
of
`(cmSchemeTower ... q).map (smallCMInclusion D hVU)`.
`cmNormalPointFiberMap_val` identifies its value reflexively with the
point map of the existing chosen residual action.
`cmNormalPoint_exists_translate` and
`cmNormalPointFiberMap_surjective` give the same two translation and
surjectivity conclusions on this exact chosen tower.

`cmNormalProjection_finite_preimage_singleton`,
`cmNormalProjection_locallyQuasiFinite_of_dualGeometry` and
`cmNormalProjection_isFinite_of_dualGeometry` then state the finite
point-fiber, local quasi-finiteness and finiteness conclusions directly
for that original chosen forgetting morphism.
The explicit `q` and the named relative-dual assertions remain inputs.

## Source, provenance and scope

The source is Harris and Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
This passage defines sufficiently small full-adelic levels and the
component product, specifies the polarized CM frame-orbit moduli up to
isogeny with rational polarization multiplier, and gives the right
frame-composition transitions. It separately asserts smooth projective
representability, finite-etale forgetting and the normal-level Galois
cover with group `U/V`.

This module's contribution is an internal deduction of the finiteness
part under the explicit formal premises. Its implemented route uses
the proved original comparison-surjectivity theorem, actual pullback
points and coproduct summands to establish point-fiber transitivity,
then finite residual ranges and Mathlib's local quasi-finiteness and
properness criteria. This argument is not attributed as the source's
proof of its complete covering theorem. The supplied five-page Harris
publication/errata list was read in full; no entry in that supplied list
corrects this passage.

The exact representing test category remains restricted as described
above. Applicable representability under the required division/global
hypotheses, comparison with the full source moduli problem, the source
smallness implication to actual coarse-object rigidity, and etaleness of
the original forgetting morphism remain obligations. This module does
not assert a free residual action, invertibility of the kernel comparison,
or the source's complete Galois-cover assertion from these inputs alone.
The inherited torsion finite-etaleness premise does not establish
etaleness of `p`. Canonical-model comparisons, uniformization and actual
coefficient-system descent also remain separate obligations.

All code and prose in this pair are by Worker 57. The pinned environment
is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
