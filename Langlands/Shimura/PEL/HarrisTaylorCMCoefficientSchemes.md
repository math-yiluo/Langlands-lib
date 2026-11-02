# Original CM coefficient scheme and small-etale diagrams

Author: Worker 57.

This derived specialization constructs the equivariant inverse diagram of the
original CM schemes at the full coefficient-kernel levels. It also constructs
the diagram in the actual small-etale category of the original coarse scheme.
The arithmetic residual groups, scheme transitions and deck actions are the
existing original ones. All functor, equivariance and projection laws are
proved from the existing tower and normal refinements.

## Data and exact premises

The universe-zero parameters are the central-simple unitary data
`D : CentralSimpleUnitaryData E F A n`, with E totally real and F CM,
totally complex and quadratic over E, the displayed algebra structures
and scalar towers, an imaginary quadratic field L embedded in F, its chosen
complex embedding `τ₀`, and the CM-compatible Harris signature charts `C`.
The algebraic coefficient data consist of `Module.Finite ℚ A`, a number
field K, a finite K-module W, an algebraic representation `ρ` of
`D.rationalInvolution.baseChange K` on W, an actual rational finite place p,
a small CM level U, and a natural scalar m with `hm : m ≠ 0`. Every
nonnegative exponent is permitted.

The scheme construction retains all the named prerequisites displayed in the
Lean variables: pullback-tensor comparison preservation, composition, unit,
associativity, unitor comparison and symmetry; Picard-zero pullback,
Mumford-square and universal base change; duality naturality, polarization
base change and relative finite Weil transitions; the rational
profinite-integer/adele comparison h; and the torsion finite-etale statement
htor. The exact input

```text
q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor
```

remains a premise. It supplies the original smooth projective representation
witness at each small level, representing the fixed CM moduli presheaf on
`ComponentwiseAdmissibleCMBaseCategory`. That category and its inherited
componentwise connected, locally Noetherian and geometric-point conditions
are unchanged. No representation assertion on every F-scheme is added.
Write T for `cmSchemeTower ... q`, R for `chosenCMLevelRepresentation ... q`,
and X for `T.obj U`. The original tower maps are recovered by the fully
faithful Yoneda construction from that fixed presheaf's maps.

The small-etale part additionally retains
`RelativeDualSchemeExistenceStatement.{0}`,
`RelativeDualSchemeGeometryStatement.{0}`, and
`CMGeometricCoarseRigidity ... U.obj`, named `existence`, `geometry`
and `hRigid`. The published construction of `cmHarrisCoefficientTorsor`
discharges the generic dominant-unramified etaleness criterion using its
published proof. No extra etaleness, scheme surjectivity, torsor,
kernel-pair comparison or local trivialization premise is introduced here.
Applicable representability and the stated geometric premises remain
obligations of the surrounding development.

## Scheme diagram and coarse projection

Put

```text
V_k = cmHarrisCoefficientLevel D ρ p U m hm k,
Q_k = SmallCMResidualGroup D U V_k.
```

These are the actual small normal coefficient-kernel levels and original
residual groups. They come from the full coefficient product over all places
of K above p, as in `HarrisTaylorCMCoefficientReduction`. Let B be the level
functor `cmHarrisCoefficientLevels D ρ p U m hm` and G the group functor
`cmHarrisCoefficientGroups D ρ p U m hm`. If `f : i ⟶ j` in `ℕᵒᵖ`,
then `j.unop ≤ i.unop`, so the proved kernel antitonicity gives the
inclusion `V_i ≤ V_j`.

`cmHarrisCoefficientSchemeDiagram` is an `EquivariantDiagram G Scheme`.
Its underlying functor is exactly `B ⋙ T`, its action at k is
`cmNormalQuotientAction ... U V_k ... q`, and its transition is the
T-image of the original identity-element inclusion `V_i ⟶ V_j`.
The group transition `Q_i → Q_j` is the already constructed residual map
which keeps the same U-representative. The equivariance field is precisely
the `comm` proof of `cmNormalRefinement` at these levels. Identity and
composition are the laws of the composite functor; no arbitrary scheme
maps or desired compatibility proofs are inputs.

`cmHarrisCoefficientSchemeDiagram_obj` and `_map` identify the underlying
functor and each transition. The `_map_refinement` equation identifies
each transition with the underlying morphism of that original equivariant
normal refinement. The `_map_over` equation proves

```text
T.map(V_i ⟶ V_j) ≫ (R V_j).base.obj.hom =
  (R V_i).base.obj.hom.
```

Thus the map preserves the original structure morphism to `Spec F`.
This equation reuses `representedCMNormalRefinement_over`.
The representative formula `_action_mk` says that the class of
`g : U.obj.subgroup` acts by the T-image of
`smallCMNormalInverseArrow D U V_k ... g`. This arrow has transporter
element `g⁻¹`; it is the existing inverse-right action in the original
opposite CM group.

`cmHarrisCoefficientSchemeProjection` is a natural transformation from this
scheme diagram to the constant diagram at X. Its component at k is the
original forgetting map `T.map (smallCMInclusion D (V_k ≤ U))`.
Naturality follows by applying T to the composition law for those
identity-element inclusions. The `_app` equation identifies the component,
and `_over` proves that it also preserves the original maps to `Spec F`.
The theorem `_invariant` reuses
`representedCMNormalProjection_invariant` to show that every `Q_k` deck
action fixes this projection.

## Diagram on the original small-etale site

Let `Y_k = cmHarrisCoefficientTorsor ... q U existence geometry hRigid
ρ p m hm k`. This is the already constructed original action on an object
of `X.Etale`, paired with its finite geometric torsor proof.

`cmHarrisCoefficientEtaleTower : ℕᵒᵖ ⥤ X.Etale` has object `Y_k.val.V`.
Its transition has underlying scheme morphism exactly the transition of
`cmHarrisCoefficientSchemeDiagram`. The coarse-projection naturality
equation supplies the required equality over X. Faithful extensionality for
morphisms in this actual over category reduces identity and composition
to the scheme diagram's functor laws.

`cmHarrisCoefficientEtaleDiagram` puts the exact actions `Y_k.val.ρ` on
this functor over the same G. Its equivariance proof uses the same
extensionality and the already proved scheme equivariance.
`cmHarrisCoefficientEtaleDiagram_action` identifies each whole action with
`Y_k.val`, and `_obj_left` identifies its source scheme with `T.obj V_k`.
The theorem `_isFiniteGeometricTorsor` is the existing property of `Y_k`.
Here the predicate means finite acting group, finite and scheme-surjective
structural morphism, and unique residual translation between any two
separably closed field-valued points over the same point of X. Etaleness
is part of the small-etale object itself.

The theorem `_coversTop` applies the existing coefficient-torsor
covering result: at every k the singleton cover consisting of this object
covers the final object of `Scheme.smallEtaleTopology X`.
The equations `_map_left` and `_action_mk_left` identify every small-etale
transition with the original forgetting map and every representative
deck map with the same inverse-right transporter image. These
identifications are reflexive; the intermediate over-category construction
has not replaced the original scheme maps or actions.

## Sources, derivation and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, supplies
the motivating algebraic representation, stable integral lattice,
inverse-equivariant function formula (3.7), and normal congruence
quotient factorization before (3.8). The registered source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
defines the small-level moduli functor, gives right frame composition and
states the normal-level finite-etale Galois-cover assertion. III.2,
printed pp.94–95, PDF pp.102–103, constructs compatible torsion
coefficient sheaves using inverse-equivariant functions on varying finite
covers. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The supplied five-page author errata list was checked; it identifies no
correction to these passages. This observation is limited to that list.

The exact coefficient-kernel exponent diagram here is an internal
categorical deduction from `HarrisTaylorCMCoefficientDiagram`,
`HarrisTaylorCMNormalRefinement` and `HarrisTaylorCMCoefficientSheaf`.
The parameters m and k extend the positive prime-power parameters in the
motivating sources to a nonzero natural scalar and arbitrary nonnegative
exponent, using the existing arithmetic constructors. The module proves
the scheme and small-etale diagram compatibilities described above.
Associated-sheaf transition maps, comparison with the source's function
description or a different representation normalization, independence of
choices, arbitrary scheme inverse-image compatibility, freeness, trivial
kernel intersection and the full lisse adic construction remain separate.
Source-moduli comparison, applicable existence, rigidity and canonical-model
geometry are not proved by this conditional specialization.

The code and prose in this pair are by Worker 57, using published generic
interfaces. The pinned environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
