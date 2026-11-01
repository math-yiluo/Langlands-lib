# Geometric Hom equivalence for the original CM kernel comparison

This module proves that postcomposition by the existing residual-action kernel comparison is bijective on actual scheme morphisms from every algebraically closed field spectrum, under explicit fieldwise coarse-object rigidity and the existing named infrastructure premises. It constructs the equivalence with the original comparison as its forward function and the previously constructed geometric lift as its inverse. These conclusions are proved from the original maps; they are not premises of a new interface.

## Objects and explicit hypotheses

All declarations are in `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic data remain `CentralSimpleUnitaryData E F A n` and its actual Harris signature charts `C`: `E` is a totally real number field, `F/E` is CM quadratic, and `L` is the specified imaginary quadratic CM field embedded in `F`, with the specified complex embedding. The scalar-tower instances, normalized Harris–Taylor reflex structure, positive auxiliary involution and original opposite-group conventions are unchanged.

The named tensor premises are pullback preservation, composition, unit coherence, associativity, left-unitor comparison and symmetry. The Picard premises are pullback stability, the Mumford-bundle assertion and universal base change. Dual-abelian base-change naturality, polarization base-change stability, relative finite Weil transitions, the rational/profinite-integer/adele comparison and torsion finite etaleness remain explicit Lean arguments. They are not proved in this module.

`R` is the existing family of `CMLevelRepresentation` witnesses for every `SmallCMLevel D`. Each witness contains an actual admissible scheme over `Spec F`, its smoothness and projectivity witnesses, and the representing natural isomorphism on `ComponentwiseAdmissibleCMBaseCategory`. This is the existing locally Noetherian test category with admissibility on actual connected-component schemes, whose factors use the connected unpointed class towers. The underlying rational-isogeny class subtype retains a representative satisfying the determinant and numerical conditions jointly. No invariance of dimension under every rational isogeny is used.

Let `X_V` and `X_U` be the fine and coarse objects of `representedCMSchemeTower ... R`. The inclusion `hVU : V.obj.subgroup ≤ U.obj.subgroup` is explicit. Normality is assumed for `V.obj.subgroup.subgroupOf U.obj.subgroup` inside `U.obj.subgroup`. Write

```
Q = SmallCMResidualGroup D U V,
p = representedCMNormalProjection ... R U V hVU : X_V ⟶ X_U,
Y = representedCMNormalCopies ... R U V = ∐ (fun _ : Q => X_V),
K = representedCMNormalKernelPair ... R U V hVU = X_V ×[X_U] X_V,
κ = representedCMNormalKernelComparison ... R U V hVU : Y ⟶ K.
```

These are the original residual quotient, forgetting map, scheme coproduct, pullback and comparison from `HarrisTaylorCMNormalKernelPair`. The original residual action `ρ = representedCMNormalQuotientAction ... R U V hVU` uses inverse-right transport: a representative `g` acts through the transporter with element `g⁻¹`. On summand `g`, the graph defining `κ` has first projection the identity and second projection `ρ(g)`. No replacement action or comparison is introduced.

Every geometric injectivity, bijectivity and equivalence result takes `RelativeDualSchemeExistenceStatement` and `RelativeDualSchemeGeometryStatement`. These are the existing assertions of universal dual-scheme existence and the duals' smoothness, properness and geometric connectedness. The preceding action theorem uses them to admit the actual field spectrum in the test category. They do not assume a kernel-comparison conclusion.

The additional premise is the previously defined proposition `CMGeometricCoarseRigidity ... U.obj`. It requires `CoarseLevelHasNoAutomorphisms` at the identity point of every admitted algebraically closed field spectrum over `Spec F`. This quantifies over actual positive polarized objects satisfying both representative tests, compatible coarse orbits, rational-unit multipliers and equivariant rational self-isogenies. Such a self-isogeny preserving its coarse orbit must be the identity. It is an object-rigidity condition, rather than an assumption of residual freeness or of the equivalence constructed here. Its implication from Harris smallness remains open. All geometric fields and schemes in this module are in universe zero.

## Factorization through an actual coproduct summand

`specFieldHom_factor_coproduct` is independent of the arithmetic data and needs only a field `Omega`, a type-zero family `X : I → Scheme`, and an actual morphism

`d : Spec Omega ⟶ ∐ X`.

It proves the existence of an index `i` and an actual scheme morphism `a : Spec Omega ⟶ X i` such that `a ≫ Sigma.ι X i = d`. Algebraic closure is unnecessary for this lemma.

The implemented proof evaluates `d` at a point of the nonempty field spectrum. Mathlib's `AlgebraicGeometry.sigmaMk` identifies a point of the coproduct with a point in one summand, and `sigmaMk_mk` expresses it through the original summand inclusion. Since the spectrum of a field is a singleton, the entire topological image of `d` lies in that same summand. The universal property `IsOpenImmersion.lift` then gives the scheme morphism `a`; `IsOpenImmersion.lift_fac` proves the required equality of scheme morphisms. The conclusion is stronger than a factorization of point functions alone.

## Injectivity of the original comparison

`representedCMNormalKernelComparison_geometricHom_injective` considers two actual morphisms `d,e : Spec Omega ⟶ Y` whose composites with `κ` are equal. Factor them by the preceding lemma:

```
d = a ≫ Sigma.ι _ g,
e = b ≫ Sigma.ι _ k.
```

Postcomposing the given equality with the first pullback projection, the original summand and graph formulas reduce it to `a = b`. Postcomposing with the second projection and substituting that equality gives

`a ≫ ρ(g) = a ≫ ρ(k)`.

The preceding `representedCMGeometricPoint_normalTranslate_injective`, with the same relative-dual and coarse-rigidity premises, yields `g = k`. Substitution into the two actual factorizations proves `d = e`. Thus injectivity is derived for the exact original map

`(Spec Omega ⟶ Y) → (Spec Omega ⟶ K), d ↦ d ≫ κ`.

`representedCMNormalKernelComparison_geometricHom_bijective` pairs this theorem with the existing `representedCMNormalKernelComparison_geometricHom_surjective`. The latter uses the previously constructed actual geometric lift. No etaleness premise is introduced.

## Constructed equivalence and the identical chosen tower

`representedCMNormalKernelGeometricHomEquiv` constructs

`(Spec Omega ⟶ Y) ≃ (Spec Omega ⟶ K)`.

Its forward function is `d ↦ d ≫ κ`. Its inverse is exactly `representedCMNormalKernelGeometricLift ... existence geometry`. The existing lift-composition theorem proves the right inverse equation. To prove the left inverse equation, the new injectivity theorem reduces equality of the lifted composite with `d` to equality after `κ`, where the same lift-composition theorem applies. The two `_apply` and `_symm_apply` lemmas record these functions by reflexivity. No new inverse-selection operation is used.

For an existing `q : CMRepresentabilityStatement ...`, the final declarations substitute exactly `chosenCMLevelRepresentation ... q` for `R`. These are `cmNormalKernelComparison_geometricHom_injective`, `cmNormalKernelComparison_geometricHom_bijective`, `cmNormalKernelGeometricHomEquiv` and its two computation lemmas. The forward function is precisely `cmNormalKernelComparison ... U V hVU q`, and the inverse is precisely the preceding `cmNormalKernelGeometricLift ... U V hVU q`. This is the identical representation family defining `cmSchemeTower ... q`; there is no second choice of schemes.

## Original sources, provenance and remaining scope

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99, registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`, supplies the full-adelic smallness, connected-component product, polarized CM frame-orbit moduli, rational-isogeny equivalence and right frame-composition conventions. Page 91 separately asserts representability, finite-etale forgetting and the normal-level Galois-cover property with group `U/V`.

Kottwitz, *Points on some Shimura varieties over finite fields*, JAMS 5 (1992), §6, printed p.392, one-based PDF p.20, registered as `kottwitz-1992-points-shimura-finite-fields`, SHA-256 `c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`, restricts prime-to-p levels to objects without nontrivial automorphisms before asserting the etale and normal-level Galois coverings. This motivates the inherited object-rigidity premise only. Its different level and isogeny conventions are not identified with Harris's full-adelic condition.

Both retained original passages and all five pages of the supplied Harris publication/errata list were read for this construction; source hashes were checked. That supplied list contains no correction of this Harris–Taylor passage. This is a bounded observation about the list. No source-specific project errata note was available at the configured errata-note locations.

The implemented proof is an internal deduction from the existing actual coproduct and pullback graph formulas, the preceding conditional residual freeness theorem and the preceding actual lift. It is not presented as a source proof of the complete Galois-cover theorem. It establishes a bijection of geometric Hom sets under the listed premises. It does not establish `IsIso κ`, etaleness of the original projection, or a scheme torsor. Rigidity from Harris smallness, applicable representability under the exact division/global hypotheses, comparison with the complete source moduli functor, canonical-model comparisons, uniformization and coefficient descent remain separate obligations. In particular, no scheme-isomorphism conclusion is inferred from these Hom bijections.

All code and prose in this pair are by Worker 57. The pinned environment is Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
