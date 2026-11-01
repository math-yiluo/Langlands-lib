# Surjectivity of the original residual CM kernel comparison

This module constructs a lift of every algebraically closed field-valued
morphism into the original CM forgetting kernel pair through its existing
residual-action comparison. It proves the exact composition equation,
surjectivity on those Hom sets and surjectivity on scheme points. These are
conditional results for the actual representing schemes and original maps.
Representability and the two named relative-dual assertions remain premises.

## Arithmetic and infrastructure inputs

All declarations are in `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.
The arithmetic data are a totally real number field `E`, a CM number field
`F` quadratic over `E`, a central simple unitary datum
`D : CentralSimpleUnitaryData E F A n`, an imaginary quadratic CM field `L`
mapping to `F`, and a complex embedding `τ₀` of `L`. The actual Harris
signature charts `C` use the constructed Harris CM section. The algebra
and scalar-tower instances remain explicit. The inherited moduli functors
retain their normalized Harris–Taylor reflex structure, positive auxiliary
involution, polarization and Weil-pairing conventions.

The named infrastructure premises are pullback-tensor preservation,
composition, unit coherence, associativity, left-unitor comparison and
symmetry; Picard-zero pullback stability, the Mumford-bundle assertion and
universal base change; dual-abelian base-change naturality; polarization
base-change stability; relative finite Weil-transition compatibility; the
actual rational/profinite-integer/adele comparison; and torsion finite
etaleness. The Lean binders give their precise proposition types. These
premises are inherited, rather than proved by this module.

`RelativeDualSchemeExistenceStatement` and
`RelativeDualSchemeGeometryStatement` are additional explicit premises of
each lift and surjectivity result. They assert the existence of universal
dual schemes and smoothness, properness and geometric connectedness of
the duals, respectively. The preceding geometric-translation theorem uses
them to admit the actual field-test spectrum through
`admissibleCMBase_iff_dualGeometry`. Neither premise asserts transitivity,
a residual lift or any geometric property of the comparison considered here.

## The identical schemes, residual action and comparison

`R` is a family of the existing `CMLevelRepresentation` witnesses for every
`SmallCMLevel D`. Each witness contains an actual admissible scheme over
`Spec F`, smoothness, projectivity and an isomorphism from lifted Yoneda
to the original small-level class presheaf. That presheaf is defined on
`ComponentwiseAdmissibleCMBaseCategory`: the existing locally Noetherian
schemes with admissibility on their actual connected-component schemes.
Its connected factors are the original unpointed class towers on connected,
locally Noetherian admissible bases. The rational-isogeny quotient retains
representatives satisfying the determinant and numerical dimension conditions
jointly. No dimension invariance under every rational isogeny is asserted.

The actual scheme tower is `representedCMSchemeTower ... R`. Its maps are
the existing Yoneda preimages of the fixed moduli transitions. Write `X_V`
and `X_U` for its fine and coarse objects, where `hVU` explicitly states
`V.obj.subgroup ≤ U.obj.subgroup`. Set

```
p = representedCMNormalProjection ... R U V hVU : X_V ⟶ X_U,
Q = SmallCMResidualGroup D U V,
Y = representedCMNormalCopies ... R U V = ∐ (fun _ : Q => X_V),
K = representedCMNormalKernelPair ... R U V hVU = X_V ×[X_U] X_V.
```

The map `p` is the original forgetting map at `smallCMInclusion D hVU`.
The group `Q` is the actual quotient of `U.obj.subgroup` by
`V.obj.subgroup.subgroupOf U.obj.subgroup`. Normality is assumed only for
that subgroup of `U`, not in the entire finite-adelic group. The original
action `ρ = representedCMNormalQuotientAction ... R U V hVU` uses the
existing inverse-right convention: a representative `g` acts through the
transporter with element `g⁻¹`. The original opposite Harris group remains
unchanged.

The existing morphism

```
κ = representedCMNormalKernelComparison ... R U V hVU : Y ⟶ K
```

is the coproduct descent of the residual-action graphs. On summand `g`,
its first pullback projection is the identity and its second projection
is `ρ(g)`. The coproduct, pullback, graph maps and `κ` are exactly those
constructed in `HarrisTaylorCMNormalKernelPair`; no new comparison map
is substituted.

## Constructed geometric lift and exact composition

For an algebraically closed field `Ω`, let `Z = Spec Ω` and take an actual
morphism `c : Z ⟶ K`. The private lemma `kernelPoint_coarse_eq` applies the
pullback condition and associativity to show that

```
a = c ≫ pullback.fst p p,
b = c ≫ pullback.snd p p
```

satisfy `a ≫ p = b ≫ p`. This lemma itself does not require normality.
The preceding `representedCMGeometricTranslation` then supplies an element
`g : Q` with the proved equality `a ≫ ρ(g) = b`. Its existence was derived
from the original class-fiber translation through natural evaluation,
component and exact representing isomorphisms. It is not a new hypothesis.

`representedCMNormalKernelGeometricLift` is the actual scheme morphism

```
a ≫ Sigma.ι (fun _ : Q => X_V) g : Z ⟶ Y.
```

`representedCMNormalKernelGeometricLift_comp` proves that this morphism
followed by the exact `κ` equals `c`. Pullback extensionality reduces the
proof to the two projections. The existing summand and graph formulas
give `a` for the first projection and `a ≫ ρ(g)` for the second. The
proved translation equation identifies the latter with `b`. The generated
reassociated simplification lemma records the same composition after a
further morphism.

The lift uses the preceding noncanonical choice of a translating residual
element. No naturality in `c` or `Ω`, uniqueness of `g`, or global section
of `κ` is asserted.

## Two surjectivity conclusions and the chosen tower

`representedCMNormalKernelComparison_geometricHom_surjective` proves
surjectivity of

```
(Z ⟶ Y) → (Z ⟶ K),    d ↦ d ≫ κ
```

for every algebraically closed field `Ω`. Its preimage of `c` is the
constructed lift, and its required equation is exactly the composition
theorem.

`representedCMNormalKernelComparison_surjective` proves
`Function.Surjective κ` on underlying scheme points. For each point `y`
of `K`, it takes `HarrisGeometricPoint.ofResidue K y`, whose source is the
spectrum of an algebraic closure of the residue field at `y`. Lift that
actual morphism by the preceding construction and evaluate it at a point
of its nonempty field spectrum. Evaluation of the exact composition
equation gives an image equal to the chosen geometric morphism evaluated
there. `Scheme.fromSpecResidueField_apply` identifies this image with `y`.
The argument uses actual scheme morphisms before passing to their points.

For `q : CMRepresentabilityStatement ...`, the four final declarations
substitute exactly `chosenCMLevelRepresentation ... q` for `R`:
`cmNormalKernelGeometricLift`, `cmNormalKernelGeometricLift_comp`,
`cmNormalKernelComparison_geometricHom_surjective` and
`cmNormalKernelComparison_surjective`. Their comparison is the existing
`cmNormalKernelComparison ... U V hVU q`. This is the identical chosen
family defining `cmSchemeTower ... q`, its original forgetting map,
coproduct and kernel pair; the specialization makes no second selection
of representing witnesses.

## Original source, provenance and remaining obligations

The source is Harris and Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage specifies small levels and the connected-component product,
defines polarized CM quadruples with invariant pairing-compatible adelic
frame orbits and rational-isogeny equivalence, and gives right
frame-composition transitions. It separately asserts smooth projective
representability, finite-etale forgetting and the normal-level Galois-cover
property with group `U/V`.

This module is an internal deduction relevant to that last assertion.
The implemented proof passes from the pullback condition to the already
proved residual translation, inserts the first projection into its summand,
and checks both pullback projections. The field-valued and scheme-point
surjectivity conclusions then follow as described above. This route and
its conditional scope are the provenance of the contribution; it is not
presented as the source's proof of the full cover theorem. The supplied
five-page Harris publication/errata list was previously read in full;
no entry in that supplied list corrects this passage.

The represented test category remains restricted as specified above.
Applicable existence under the exact division/global hypotheses,
comparison with the complete source moduli problem, uniqueness of
residual transport and freeness, etaleness of the original projection,
and invertibility of the exact `κ` remain open. The proofs use neither
an `Etale p` premise nor an `IsIso κ` premise. The named torsion
finite-etaleness input is an earlier moduli prerequisite and does not
establish etaleness of `p`. Point surjectivity alone supplies no
comparison-isomorphism conclusion. Canonical-model comparisons,
uniformization and coefficient descent also remain separate obligations.

All code and prose in this pair are by Worker 57. The pinned environment
is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
