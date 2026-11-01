# Original CM kernel lifts on connected scheme tests

Author: Worker 57.

This module transfers the original CM class-fiber translation theorem to all
connected admissible scheme tests. Under the two named relative-dual assertions,
it constructs actual lifts of morphisms from any connected locally Noetherian
scheme to the original residual-action kernel pair. Sources may be nonreduced.
The lift is a morphism of the original schemes, and its composite with the
original comparison is proved to equal the given morphism.

## Parameters, tests and original maps

All declarations lie in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic inputs are the
universe-zero totally real number field `E`, its quadratic CM extension `F`,
the central simple unitary datum `D : CentralSimpleUnitaryData E F A n`, an
imaginary quadratic CM number field `L` with the displayed algebra map to `F`,
and its complex embedding `τ₀`. The signature charts `C` use exactly
`harrisCMSection E (algebraMap L F) τ₀`. All algebra and scalar-tower instances
remain explicit. The imported class towers retain their normalized conjugated
Harris–Taylor reflex structure, positive auxiliary involution, polarizations,
Weil pairings and rational-isogeny equivalence with an actual rational inverse.
The determinant and numerical conditions still hold on one common
representative; this module assumes no dimension invariance under arbitrary
rational isogenies.

The named infrastructure inputs remain tensor-pullback comparison preservation,
composition, unit coherence, associativity, left-unitor comparison and symmetry;
Picard-zero pullback, the Mumford-bundle assertion and universal base change;
dual-abelian base-change naturality; polarization base-change stability; relative
finite Weil transition; the actual rational/profinite-integer/adele comparison;
and torsion finite etaleness. Their concrete proposition binders are unchanged.

`AdmissibleCMBaseCategory` is the existing full subcategory of schemes over
`Spec F` whose underlying schemes are connected, locally Noetherian and
quasi-separated, with the original torsion units, finite-etale roots of unity,
Lie naturality, positive-pair additivity and constrained dual-data existence
conditions. Connectedness includes nonemptiness. The category retains all
actual morphisms over `Spec F`; it restricts neither to flat maps nor to reduced
schemes. `ComponentwiseAdmissibleCMBaseCategory` is the existing locally
Noetherian componentwise-admissible category. Its tower is the product over the
actual connected open component schemes of the unpointed tower.

For the represented results, `R` is a family of the existing
`CMLevelRepresentation` witnesses, one at each `SmallCMLevel D`. Each contains
an actual componentwise-admissible scheme over `Spec F`, smoothness, an actual
projective-space closed-immersion witness and a natural isomorphism from lifted
Yoneda to the fixed small-level class presheaf. This module uses that actual
representing isomorphism. It does not assume arbitrary supplied transitions or
construct applicable representability.

Fix small original levels `V ≤ U`, with explicit subgroup inclusion `hVU` and
normality of `V.obj.subgroup.subgroupOf U.obj.subgroup` in `U.obj.subgroup`.
Write `X_V`, `X_U`, `p` and `Q` for the original represented fine and coarse
schemes, `representedCMNormalProjection R U V hVU`, and
`SmallCMResidualGroup D U V`. Thus `p` is the existing represented tower map at
`smallCMInclusion D hVU`, and `Q` is the original residual quotient. Write
`ρ` for `representedCMNormalQuotientAction R U V hVU`. Its left action retains
the inverse-right frame convention: a representative `g` acts by the existing
normal-inverse transporter, whose translating element is `g⁻¹`.

The original copies scheme is the coproduct of `X_V` indexed by `Q`, and the
original kernel pair is `X_V ×[X_U] X_V`. The comparison is precisely
`representedCMNormalKernelComparison R U V hVU`; on summand `g` it is the
original graph `(identity, ρ(g))`. No replacement action, coproduct, kernel
pair or comparison is introduced.

## Transfer on connected admissible schemes

The private lemma `exists_translate_of_naturalIso` transfers existence of a
translation through a natural isomorphism of level functors. Naturality sends
the coarse equality into the target functor. Its translation theorem supplies
an element there. Naturality at the same endomorphism and injectivity of the
fine component give the desired equality in the source functor.

`unpointed_exists_normalTranslate` chooses a point of the nonempty connected
base and uses `HarrisGeometricPoint.ofResidue` to obtain the actual spectrum of
an algebraic closure of its residue field, with its morphism to that base.
The proved `HarrisGeometricPoint.finiteFibers` supplies the required finite
fibers; they are not an extra premise. Applying the transfer lemma to the
existing `unpointedClassTowerEvaluationIso` reduces the assertion to
`classMap_exists_normalTranslate`. That preceding theorem applies at an
arbitrary quasi-separated base, not just a field spectrum. The admissibility
witness supplies the required torsion units and pair additivity. Its actual
frame-orbit and rational-isogeny argument produces an element of the original
`U.subgroup`. The chosen residue point is used only within this proof.

`disconnected_connected_exists_normalTranslate` applies the same transfer to
`disconnectedClassTowerConnectedIso` at an actual component of the connected
base. It keeps the exact inclusion and normal-inverse arrows. Both the
componentwise base object and its connected admissibility witness are explicit.

`representedCMConnectedHom_exists_normalTranslate` evaluates the exact fine
representing isomorphism on two actual over-category morphisms. The existing
`representedCMBaseTower_map_classes` equation sends equality of their coarse
composites to equality of the original coarse class values. The preceding
theorem gives a translating `g : U.obj.subgroup`. The existing
`representedCMNormalQuotientBaseAction_mk_classes` equation identifies that
class translation with postcomposition by the actual residual action at
`QuotientGroup.mk g`. Injectivity of the representing equivalence and of
`ULift.up` returns equality of the actual over-category morphisms.

## Admission and actual scheme morphisms

`representedCMConnectedMap_exists_normalTranslate` starts with actual maps
`a,b : T ⟶ X_V`, for any connected locally Noetherian scheme `T`, satisfying
`a ≫ p = b ≫ p`. It sets the actual structural map to
`a ≫ (R V).base.obj.hom`. The existing tower equation over `Spec F` proves that
`b` has that identical structural map. The proof bundles both maps into the
same full over-category before applying the preceding theorem, then forgets
only the categorical wrappers. The conclusion is the scheme-morphism equality

```text
∃ g : Q, a ≫ ρ(g) = b.
```

Admission uses both explicit hypotheses
`RelativeDualSchemeExistenceStatement.{0}` and
`RelativeDualSchemeGeometryStatement.{0}`. The former supplies an actual
universal Picard-zero dual for every abelian scheme over any quasi-separated
base. The latter gives smoothness, properness and geometric connectedness of
each such chosen dual. The existing `admissibleCMBase_iff_dualGeometry` and
`componentwiseAdmissibleCMBase_of_relativeDual` assemble the required test-base
witnesses, using local Noetherianity for quasi-separatedness and the proved
characteristic-zero torsion and Lie conditions. These are substantive named
premises, not assumptions of translation, kernel invertibility or etaleness.
The scheme `T`, including its nilpotents, is retained throughout.

## The constructed original kernel lift

For `c : T ⟶ X_V ×[X_U] X_V`,
`representedCMNormalKernelConnectedTranslation` chooses a residual element
from the proved translation theorem applied to `c ≫ pullback.fst` and
`c ≫ pullback.snd`. Their coarse equality is the actual pullback condition.
`representedCMNormalKernelConnectedTranslation_action` is the corresponding
`Classical.choose_spec` equation. It states

```text
(c ≫ pullback.fst) ≫ ρ(translation c) = c ≫ pullback.snd.
```

`representedCMNormalKernelConnectedLift` is literally

```text
(c ≫ pullback.fst) ≫ Sigma.ι (fun _ : Q => X_V) (translation c).
```

This is an actual morphism into the existing coproduct, using its original
summand inclusion. `representedCMNormalKernelConnectedLift_comp` compares both
kernel-pair projections. On the first projection the existing graph equation
gives the identity; on the second it gives the displayed translation equation.
Pullback extensionality proves that the lift followed by the exact original
comparison is `c`. Its reassociated equality is generated as a simp theorem.
`representedCMNormalKernelComparison_connectedHom_surjective` supplies this
lift for every `c`, proving surjectivity of postcomposition with the original
comparison on actual scheme Hom sets for every connected locally Noetherian
source.

`cmConnectedMap_exists_normalTranslate`, `cmNormalKernelConnectedLift`,
`cmNormalKernelConnectedLift_comp` and
`cmNormalKernelComparison_connectedHom_surjective` substitute precisely
`chosenCMLevelRepresentation q` for `R`. This is the identical family already
used by `cmSchemeTower q`, `cmNormalQuotientAction q` and
`cmNormalKernelComparison q`. The entry definition is
`cmNormalKernelConnectedLift`. Its value theorem
`cmNormalKernelConnectedLift_eq` is reflexive equality with the original first
projection followed by the original summand inclusion at the constructed
translation. No independent family of representing witnesses is selected.

## Source and scope

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99, is registered
as `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Page 90 defines local torsion-free smallness of full-adelic compact-open levels
and the product over connected components. Page 91 defines polarized CM
quadruples with invariant compatible adelic-frame orbits, their equivalence by
isogeny with rational polarization multiplier, canonical geometric-point
independence and right frame composition. It asserts smooth projective
representability, finite-etale forgetting and the normal `U/V` Galois cover.
These are the source conventions retained by the imported constructions.

The new result is derived internally from the existing arbitrary-base class
translation theorem and the constructed evaluation, component and representing
isomorphisms. Its proof route is the transfer, admission and explicit summand
lift described above. It is not attributed to the book as a proof of the full
cover theorem. In particular, the earlier geometric-field-only transfer is
extended to connected scheme tests by using the same already proved
arbitrary-base class theorem. The supplied Harris publication/errata list was
previously read in full; no entry in that supplied list corrects this passage.

The construction uses no original-projection etaleness, coarse-object rigidity,
comparison `IsIso`, residual freeness or finite point-fiber assumption. It
claims no uniqueness or naturality for its classical choice, and constructs no
section of the original projection. Source-smallness rigidity, applicable
representability, comparison with the complete source moduli problem,
etaleness of the original projection, a full scheme inverse for the kernel
comparison, canonical-model comparisons, uniformization and coefficient
local-system descent remain separate obligations. The conclusions here are
conditional actual scheme lifts, not completion of those source assertions or
of the host task.
