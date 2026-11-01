# The original CM kernel comparison is invertible under original etaleness

This module proves invertibility of the existing residual-action kernel
comparison from etaleness of the same original forgetting map, explicit
coarse-object rigidity, the two named relative-dual assertions and the
inherited infrastructure and exact representability witnesses. It constructs
an actual scheme isomorphism whose forward morphism is exactly the original
comparison. Its inverse on algebraically closed field-valued morphisms is
the previously constructed geometric lift. Etaleness of original forgetting
remains an input.

## Objects and hypotheses

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic data are
the existing central simple unitary datum `D` over the CM quadratic
extension `F/E`, with `E` totally real; the specified imaginary quadratic
CM field `L` in `F`; the specified complex embedding; and the
CM-compatible Harris signature charts `C`. The scalar towers, positive
auxiliary involution, normalized Harris–Taylor reflex structure and
opposite finite adelic group conventions are retained.

Fix the existing family `R` of `CMLevelRepresentation` witnesses and small
levels `V ≤ U`, with `V.obj.subgroup.subgroupOf U.obj.subgroup` normal in
`U.obj.subgroup`. Each witness contains an actual admissible scheme over
`Spec F`, smoothness and projectivity witnesses, and the representing
natural isomorphism for the fixed disconnected CM class presheaf on
`ComponentwiseAdmissibleCMBaseCategory`. Its actual connected-component
tests retain local Noetherianity and connected admissibility. The
rational-isogeny class condition still uses a single representative
satisfying the determinant and numerical conditions jointly. No dimension
invariance under arbitrary rational isogenies is assumed.

Use the following names for the pre-existing constructions:

```
X_U = (representedCMSchemeTower ... R).obj U,
X_V = (representedCMSchemeTower ... R).obj V,
Q = SmallCMResidualGroup D U V,
p = representedCMNormalProjection ... R U V hVU : X_V ⟶ X_U,
Y = representedCMNormalCopies ... R U V = ∐ (fun _ : Q => X_V),
K = representedCMNormalKernelPair ... R U V hVU = X_V ×[X_U] X_V,
κ = representedCMNormalKernelComparison ... R U V hVU : Y ⟶ K.
```

Here `Q` is the original quotient
`U.obj.subgroup ⧸ V.obj.subgroup.subgroupOf U.obj.subgroup`.
The projection is the tower map at `smallCMInclusion D hVU`. On summand
`g`, `κ` is the original graph with first projection identity and second
projection the existing inverse-right residual action `ρ(g)`. Thus the
underlying action still uses the transporter with representative `g⁻¹`.

All named infrastructure premises remain explicit: tensor pullback
preservation, composition, unit coherence, associativity, left-unitor
comparison and symmetry; Picard-zero pullback stability, the Mumford-bundle
assertion and universal base change; dual-abelian base-change naturality;
polarization base-change stability; relative finite Weil transitions;
the rational/profinite-integer/adele comparison; and torsion finite
etaleness.

The injectivity and isomorphism results also take
`RelativeDualSchemeExistenceStatement` and
`RelativeDualSchemeGeometryStatement`. These assert universal Picard-zero
dual-scheme existence and smoothness, properness and geometric
connectedness of the actual duals. The preceding geometric-action results
use them to admit the actual algebraically closed field spectra in the
restricted test category.

`hRigid : CMGeometricCoarseRigidity ... U.obj` is the existing object-level
condition at each admitted algebraically closed field spectrum over
`Spec F`. It quantifies over actual positive polarized representatives
satisfying both tests, their compatible coarse orbits, rational-unit
polarization multipliers and actual equivariant rational self-isogenies.
A self-isogeny fixing its coarse orbit must be the identity. This premise
does not supply freeness of the residual action or an inverse of `κ`.
Its implication from the source's smallness condition remains open.
All fields and schemes tested by the new geometric arguments have
universe zero.

## Etaleness of the original comparison

`representedCMNormalGraph_etale` assumes `Etale p`. The first projection
`K ⟶ X_V` is etale by base change of this same `p`. The composite of
each original graph with that first projection is the identity, hence
is etale. Mathlib's `Etale.of_comp`, using local finite type and formal
unramifiedness of the first projection, proves that the graph itself is
etale.

`representedCMNormalKernelComparison_etale` applies
`IsZariskiLocalAtSource.sigmaDesc` to those graphs. It proves `Etale κ`
for the actual coproduct comparison. These two results require neither
the relative-dual assertions nor `hRigid`; their extra geometric premise
is exactly `Etale p`.

## From geometric injectivity to an actual scheme isomorphism

The private lemma `diagonal_surjective_of_geometricHom_injective` works
for any morphism `f : X ⟶ Z` of type-zero schemes. It assumes injectivity
of postcomposition with `f` on actual morphisms from every algebraically
closed field spectrum. For a point `y` of `X ×[Z] X`, the construction
`HarrisGeometricPoint.ofResidue` supplies an algebraic closure of its
residue field and an actual geometric morphism `c` over `y`. The two
composites of `c` with the pullback projections become equal after `f`,
so the injectivity premise makes them equal. Pullback extensionality
then proves the actual morphism factorization

```
(c ≫ pullback.fst f f) ≫ pullback.diagonal f = c.
```

Evaluating at a point of the nonempty field spectrum and using the
residue-field point formula gives a preimage of `y` under the diagonal.
This proves scheme surjectivity of the diagonal, including when the
schemes have nilpotents.

`representedCMNormalKernelComparison_universallyInjective` applies that
lemma to the previously proved
`representedCMNormalKernelComparison_geometricHom_injective` and then
uses `UniversallyInjective.iff_diagonal`. This conclusion needs the
relative-dual and rigidity premises but no etaleness premise.

`representedCMNormalKernelComparison_mono` additionally assumes
`Etale p`. The new etaleness theorem makes `κ` etale, so its diagonal
is an open immersion. Universal injectivity makes that diagonal
surjective. The private helper `isIso_of_surjective_openImmersion`
turns underlying surjectivity into an epimorphism of topological spaces
and uses `IsOpenImmersion.isIso` to prove invertibility of the scheme
diagonal. The criterion `pullback.isIso_diagonal_iff` yields `Mono κ`.

`representedCMNormalKernelComparison_isIso` combines `Etale κ` and
`Mono κ`. Etaleness supplies flatness and local finite presentation;
Mathlib's `IsOpenImmersion.of_flat_of_mono` makes `κ` an open immersion.
The previously proved
`representedCMNormalKernelComparison_surjective`, with the same two
relative-dual premises, proves surjectivity of this actual `κ`. The
same surjective-open-immersion helper now proves `IsIso κ`. Thus the
scheme conclusion uses actual etale geometry in addition to geometric
Hom injectivity and surjectivity.

## Constructed isomorphisms and original maps

`representedCMNormalKernelIso` constructs `Y ≅ K` by `asIso κ` after
proving the required `IsIso` instance. It does not take that instance or
an inverse as input. `representedCMNormalKernelIso_hom` identifies its
forward morphism with `κ` by reflexivity.

For an actual `c : Spec Omega ⟶ K`, with `Omega` algebraically closed,
`representedCMNormalKernelIso_inv_geometricHom` proves

```
c ≫ (representedCMNormalKernelIso ...).inv =
  representedCMNormalKernelGeometricLift ... c.
```

The proof applies the preceding injectivity theorem to both sides.
After composition with `κ`, the left side reduces to `c` by the scheme
isomorphism law, and the right side reduces to `c` by the original
geometric-lift composition theorem. The inverse therefore agrees with
the original lift into the proved residual summand.

For `q : CMRepresentabilityStatement ...`, the declarations
`cmNormalKernelComparison_etale`, `_universallyInjective`, `_mono` and
`_isIso` specialize these theorems to exactly
`chosenCMLevelRepresentation ... q`. These are the identical witnesses
used to define the existing `cmSchemeTower` and
`cmNormalKernelComparison`; no additional representation is chosen.
The entry `cmNormalKernelIso` constructs the actual chosen scheme
isomorphism. `cmNormalKernelIso_hom` identifies its hom with the original
chosen comparison by reflexivity, and
`cmNormalKernelIso_inv_geometricHom` identifies its geometric inverse
with the original `cmNormalKernelGeometricLift`.

## Original sources, provenance and remaining obligations

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99, is
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage supplies the full-adelic smallness, connected-component
product, polarized CM frame-orbit moduli, rational-isogeny and right
frame-composition conventions. It separately asserts smooth projective
representability, finite-etale forgetting and the normal `U/V`
Galois-cover property.

Kottwitz, *Points on some Shimura varieties over finite fields*, JAMS 5
(1992), §6, printed p.392, one-based PDF p.20, is registered as
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
Its prime-to-p no-automorphism restriction motivates the inherited
object-rigidity hypothesis. Its different level and isogeny conventions
are not identified with Harris's full-adelic smallness condition.
The retained original passages and all five pages of the supplied
Harris publication/errata list were read during this development, and
the source hashes were checked. That supplied list contains no
correction of this passage; this observation is limited to that list.

The proof here is an internal deduction using the original graph
equations, the preceding geometric-action freeness and lift results,
algebraic closures of residue fields, and the pinned Mathlib diagonal,
etale and flat-monomorphism criteria. It is not attributed verbatim to
either source. In particular, it does not prove original `Etale p`
from the geometric Hom statements.

The exact representability proposition, applicable existence under the
source's division/global hypotheses, comparison with its complete
moduli functor, original-projection etaleness, and rigidity from source
smallness remain obligations. Canonical-model comparisons,
uniformization and coefficient descent are not proved here. The
conditional isomorphism discharges the exact kernel-comparison
invertibility premise when all the displayed inputs hold; it does not
complete the source cover theorem or the host task.

All code and prose in this pair are by Worker 57. The pinned environment
is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
