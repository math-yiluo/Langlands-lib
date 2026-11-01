# Geometric fibers of the original CM residual action

Worker 57 constructs an equivalence from the original residual group to the exact geometric Hom fiber of the represented Harris CM forgetting map, under explicit coarse-object rigidity. The forward map is the existing residual action on the existing scheme. Injectivity is derived through the actual class, evaluation, component and representing isomorphisms; transitivity is the preceding implemented theorem. Neither conclusion is supplied as a field of a new record.

## Objects and retained hypotheses

The arithmetic datum and charts are the existing `CentralSimpleUnitaryData E F A n` and `HarrisSignatureCharts C`. Here `E` is totally real, `F/E` is CM quadratic, and `L` is the specified imaginary quadratic CM field embedded in `F`. The normalized determinant condition still uses `harrisTaylorReflexStructure`. The positive auxiliary involution and scalar-extension comparison with the original opposite Harris group are unchanged.

The named tensor premises are pullback preservation, composition, unit coherence, associativity, the left-unitor comparison and symmetry. The Picard premises are pullback stability, the Mumford-square assertion and universal base change. Dual-abelian base-change naturality, polarization base-change stability, relative finite Weil transitions, the rational/profinite-integer/adele comparison and torsion finite etaleness are also retained. These remain actual Lean arguments, not newly established assertions.

`AdmissibleCMBaseCategory` is the existing category of connected, locally Noetherian admissible schemes over `Spec F`. `ComponentwiseAdmissibleCMBaseCategory` is the existing category with componentwise admissibility. Their respective towers are `unpointedClassTower` and `disconnectedClassTower`. The latter is the existing product over actual connected-component schemes. The rational-isogeny class subtype retains a representative satisfying the determinant and numerical conditions jointly, including the prescribed geometric relative dimension and central Lie trace. The argument never assumes dimension invariance under all rational isogenies.

For the represented results, `R` is an explicit family of `CMLevelRepresentation` witnesses for all `SmallCMLevel D`. These existing witnesses contain actual admissible schemes, smoothness, projective embeddings and representing natural isomorphisms on the specified full test category. This module uses their representing isomorphisms. Write `X_V` for `(representedCMSchemeTower ... R).obj V`, `pi : X_V → X_U` for the original `representedCMNormalProjection`, and `action` for the original `representedCMNormalQuotientAction`. The explicit inclusion is `hVU : V.obj.subgroup ≤ U.obj.subgroup`, and normality is of `V.obj.subgroup.subgroupOf U.obj.subgroup` inside `U.obj.subgroup`.

The group `SmallCMResidualGroup D U V` is exactly that original subgroup quotient, conventionally `U/V`. A representative `g` acts through `normalInverseArrow`, with transporter `g⁻¹`, and through the existing Hodge scalar-extension map. No replacement quotient, action or projection is introduced.

## Explicit fieldwise rigidity

`CMGeometricCoarseRigidity U` is a proposition. For every `Type 0` algebraically closed field `Omega`, every actual structural morphism `p : Spec Omega → Spec F`, and every connected admissibility witness for `Over.mk p`, it requires `CoarseLevelHasNoAutomorphisms U` at the identity geometric point of `Spec Omega`. Its roots-of-unity finiteness and etaleness, torsion invertibility and pairing additivity are those supplied by this witness. Finite fibers are supplied by the existing `HarrisGeometricPoint.finiteFibers` theorem.

The underlying rigidity condition quantifies over actual positive polarized objects satisfying both original representative tests, compatible coarse orbits, rational-unit multipliers and actual equivariant rational self-isogenies with their polarization compatibility. A self-isogeny preserving that coarse orbit must equal the identity. It assumes neither a class-level stabilizer conclusion nor a geometric action conclusion. Proving this condition from `LevelSufficientlySmall` remains open; the small-level witnesses in `U` and `V` do not discharge it here.

## Transfer of the exact equality criterion

The private `translate_eq_iff_of_naturalIso` transfers an equality criterion for two specified endomorphisms through a natural isomorphism of functors to `Type 1`. Naturality moves the translated values across the isomorphism, and componentwise injectivity returns equality in the original functor.

`unpointed_identityPoint_normalTranslate_eq_iff` applies this to the existing `unpointedClassTowerEvaluationIso` at the actual identity point of `Spec Omega`. The preceding `classMap_normalTranslate_eq_iff` identifies equality of the two original class translations by `g,k : U.subgroup` with membership of `g*k⁻¹` in the fine subgroup. `QuotientGroup.eq_iff_div_mem` identifies this with equality of their classes in the original residual quotient.

`disconnected_identityPoint_normalTranslate_eq_iff` transfers this result through `disconnectedClassTowerConnectedIso`, using an actual connected component of the nonempty connected field spectrum. It keeps both the connected and componentwise admissibility witnesses explicit. `cmGeometricTestBase_normalTranslate_eq_iff` then constructs the connected witness for the existing `cmGeometricTestBase ... existence geometry p` using `admissibleCMBase_iff_dualGeometry`. The named `RelativeDualSchemeExistenceStatement` supplies universal dual schemes, and `RelativeDualSchemeGeometryStatement` supplies the required smoothness, properness and geometric connectedness. These substantial dual assertions are hypotheses, not conclusions of this module.

`representedCMGeometricHom_normalTranslate_eq_iff` applies `(R V).represents.hom.app` to actual morphisms from this same geometric test object. The existing `representedCMNormalQuotientBaseAction_mk_classes` formula sends the two action composites to exactly the two disconnected class translations just considered. Hence equality of these actual morphism composites implies equality of the residual quotient classes. The reverse implication follows by rewriting equal residual classes. Quotient induction gives `representedCMGeometricHom_normalTranslate_injective` for arbitrary elements of the residual quotient.

`representedCMGeometricPoint_normalTranslate_injective` starts with an actual scheme map `a : Spec Omega → X_V`. Set `p = a ≫ (R V).base.obj.hom` and bundle `a` as a morphism over `Spec F` from the same admitted test base. Equality of two translated scheme morphisms lifts to equality in that full over-category by extensionality. The preceding theorem proves injectivity of

`g ↦ a ≫ action.ρ g`.

This conclusion concerns equality of actual scheme morphisms, not just equality of underlying topological points.

## The exact geometric Hom fiber

`representedCMGeometricFiberEquiv` constructs

`U/V ≃ { b : Spec Omega → X_V // b ≫ pi = a ≫ pi }`.

Its forward function sends `g` to `a ≫ action.ρ g`. The existing projection-invariance equation places this morphism in the displayed exact fiber. The preceding injectivity theorem proves injectivity of that function. For surjectivity, the existing `representedCMGeometricPoint_exists_normalTranslate` applies to the symmetric fiber equality and supplies an original residual element translating `a` to `b`. Subtype extensionality gives the required preimage equality. `Equiv.ofBijective` constructs the inverse from these proofs. `representedCMGeometricFiberEquiv_apply` records the original action formula by reflexivity. In particular, no fiber inverse or action freeness is assumed, and no representative of a residual coset is chosen by the forward map.

`cmGeometricPoint_normalTranslate_injective`, `cmGeometricFiberEquiv` and `cmGeometricFiberEquiv_apply` substitute exactly `chosenCMLevelRepresentation ... q` for `R`, for the existing `CMRepresentabilityStatement q`. This is the identical family defining `cmSchemeTower ... q` and `cmNormalQuotientAction ... q`. The fiber uses the actual chosen tower map at `smallCMInclusion D hVU`; there is no second choice of schemes or action.

## Original sources and remaining scope

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99, registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`, supplies the full-adelic moduli and transition conventions. Page 90 defines sufficiently small levels and the connected-component product. Page 91 specifies compatible polarized CM quadruples with invariant pairing-compatible adelic-frame orbits, rational-isogeny equivalence, right frame composition, representability, finite-etale forgetting and the normal-level Galois-cover assertion.

Kottwitz, *Points on some Shimura varieties over finite fields*, JAMS 5 (1992), §6, printed p.392, one-based PDF p.20, registered as `kottwitz-1992-points-shimura-finite-fields`, SHA-256 `c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`, restricts the prime-to-p levels to moduli objects without nontrivial automorphisms before asserting the etale and normal-level Galois coverings. This motivates the isolated rigidity premise; its different level and isogeny conventions are not identified with the full-adelic Harris condition.

Both retained original passages were read for this construction. The five-page supplied Harris publication/errata list was also read in full; it contains no correction of this Harris–Taylor passage. This is a bounded observation about that list. No source-specific errata note was found among the available project/current Library note filenames.

The implemented transfer and fiber-equivalence proof is an internal deduction from the previously constructed actual class maps and natural isomorphisms. It does not claim to reproduce a source proof of the complete Galois-cover theorem. The result needs a supplied fine geometric point and proves a fiber equivalence on geometric Hom sets. Rigidity from Harris smallness, applicability of the representability theorem under the exact division/global hypotheses, comparison with the full source moduli problem, etaleness of the original projection, invertibility of the exact residual kernel comparison, canonical-model comparisons, uniformization and coefficient descent remain open. No scheme isomorphism or etaleness conclusion is inferred from this Hom fiber equivalence.
