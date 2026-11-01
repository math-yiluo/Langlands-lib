# The original CM finite geometric torsor under coarse-object rigidity

This module constructs the existing finite geometric torsor input for
coefficient descent from the original CM normal-level action. It combines
the kernel-isomorphism result in `HarrisTaylorCMKernelIsomorphism` with the
adapter in `HarrisTaylorCMNormalTorsor`. The resulting theorem takes
etaleness of the same original projection, the explicit coarse-object
rigidity condition and the two named relative-dual assertions. It requires
no additional `IsIso` premise for the residual kernel comparison.

## Original objects and explicit hypotheses

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. Fix the existing central
simple unitary datum `D` for the CM quadratic extension `F/E`, with `E`
totally real; the imaginary quadratic CM field `L` in `F`; the specified
complex embedding; and the CM-compatible Harris signature charts `C`.
The existing scalar towers, positive auxiliary involution, normalized
Harris–Taylor reflex structure and opposite finite adelic group
conventions are retained.

Let `R` be a family of the existing `CMLevelRepresentation` witnesses.
Each witness contains an actual admissible scheme over `Spec F`,
smoothness and projectivity witnesses, and a natural isomorphism from
lifted Yoneda to the exact disconnected CM class presheaf on
`ComponentwiseAdmissibleCMBaseCategory`. The tests use the existing
connected-component admissibility conditions, including local
Noetherianity. The class condition retains one representative satisfying
the determinant and numerical tests jointly; no invariance of dimension
under arbitrary rational isogenies is assumed.

Fix small levels `V ≤ U` and normality of
`V.obj.subgroup.subgroupOf U.obj.subgroup` inside `U.obj.subgroup`. Write

```
X_U = (representedCMSchemeTower ... R).obj U,
X_V = (representedCMSchemeTower ... R).obj V,
Q = SmallCMResidualGroup D U V,
p = representedCMNormalProjection ... R U V hVU : X_V ⟶ X_U,
κ = representedCMNormalKernelComparison ... R U V hVU.
```

The group `Q` is exactly
`U.obj.subgroup ⧸ V.obj.subgroup.subgroupOf U.obj.subgroup`.
The projection `p` is the map at `smallCMInclusion D hVU` in the
original tower. The comparison `κ` maps the actual scheme coproduct of
`Q` copies of `X_V` to the actual self-pullback of `p`; on summand `g`
its projections are identity and the original residual translation.
The action remains inverse-right: a representative `g` uses the
transporter for `g⁻¹`, with the existing opposite-group convention.

The inherited named inputs remain tensor pullback preservation,
composition, unit coherence, associativity, left-unitor comparison and
symmetry; Picard-zero pullback stability, the Mumford-bundle assertion
and universal base change; dual-abelian base-change naturality;
polarization base-change stability; relative finite Weil transitions;
the rational/profinite-integer/adele comparison; and torsion finite
etaleness.

Every new construction additionally takes:

- `existence : RelativeDualSchemeExistenceStatement.{0}`;
- `geometry : RelativeDualSchemeGeometryStatement.{0}`;
- `hRigid : CMGeometricCoarseRigidity ... U.obj`;
- `Etale p`.

The first assertion supplies actual universal Picard-zero dual schemes
over quasi-separated bases. The second asserts smoothness, properness
and geometric connectedness of every actual dual witness. They are used
by the preceding geometric lifting and freeness results to admit the
actual field-spectrum tests in the restricted test category.

The rigidity condition concerns actual positive polarized objects on
admitted algebraically closed field spectra over `Spec F`, at the
identity geometric point. Such an object satisfies both determinant
and numerical tests on the same representative. An actual equivariant
rational self-isogeny with a valid rational-unit polarization multiplier,
fixing its compatible coarse orbit, must equal the identity. The
condition does not supply action freeness, a fiber inverse or a scheme
isomorphism. Its derivation from Harris's smallness condition remains a
separate obligation. All schemes and field tests here have universe zero.

## Implemented torsor deduction

`representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_rigidity`
first applies `representedCMNormalKernelComparison_isIso` to the exact
original `κ`. This uses `Etale p`, the two relative-dual assertions and
`hRigid`. The preceding result derives etaleness of `κ` from the original
graphs, proves its monomorphism from the surjective open diagonal using
the established geometric Hom injectivity, and combines the flat
monomorphism criterion with the proved original-comparison surjectivity.
It proves `IsIso κ` for this same map.

The new proof installs that derived result as a local instance and
applies
`representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_dualGeometry`.
That existing adapter derives finiteness of `p` from projectivity and
etaleness, derives scheme surjectivity by lifting actual geometric
classes and using algebraic closures of residue fields, and uses
`IsIso κ` to obtain unique residual transport on separably closed
field-valued points. The acting group is already proved finite.
Consequently the conclusion is precisely

```
Coefficients.IsFiniteGeometricTorsor X_U
  (representedCMNormalEtaleAction ... R U V hVU).
```

This existing coefficient predicate requires a finite acting group,
a finite and scheme-surjective structural map, and unique residual
translation between separably closed field-valued points with the same
projection. Etaleness is part of its action's small etale category.
Neither finiteness, scheme surjectivity, unique transport nor
invertibility of `κ` is an extra input to the new theorem.

`representedCMNormalGeometricTorsorOfRigidity` constructs the subtype

```
{Y : Action X_U.Etale Q // Coefficients.IsFiniteGeometricTorsor X_U Y}.
```

Its value is the existing original small etale action; its property is
the preceding theorem. It accepts no arbitrary action or torsor proof.
The four reflexive identifications with suffixes `_val`, `_left`,
`_hom` and `_ρ_left` identify its action, source, structural map and
individual action maps with the original action, `X_V`, `p` and the
original residual translations, respectively.

## Identical chosen tower

For `q : CMRepresentabilityStatement ...`,
`cmNormalEtaleAction_isFiniteGeometricTorsor_of_rigidity` and
`cmNormalGeometricTorsorOfRigidity` specialize to exactly
`chosenCMLevelRepresentation ... q`. These are the same witnesses
defining the original `cmSchemeTower` and `cmNormalEtaleAction`.
The entry definition returns the torsor subtype over that tower's
actual coarse scheme. No additional representing witnesses are chosen.

The chosen `_val`, `_left`, `_hom` and `_ρ_left` lemmas are also proved
by reflexivity. They identify the value with `cmNormalEtaleAction`,
the source with the original chosen fine scheme, the structural map
with `cmSchemeTower.map (smallCMInclusion D hVU)`, and the action maps
with the original `cmNormalQuotientAction`. Thus the reduced hypotheses
give a coefficient-torsor input on the precise existing tower.

## Original sources, provenance and remaining scope

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
is registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage specifies the full-adelic smallness condition, the
connected-component product, polarized CM frame-orbit classes up to
rational isogeny, and right frame composition. It states smooth
projective representability, finite etale forgetting and the normal
`U/V` Galois-cover assertion.

Kottwitz, *Points on some Shimura varieties over finite fields*, JAMS 5
(1992), §6, printed p.392, one-based PDF p.20, is registered as
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
Its no-automorphism restriction motivates the explicit object-rigidity
premise; its prime-to-p level and isogeny conventions are distinct from
the full-adelic Harris conventions. The original passages and all five
pages of the supplied Harris publication/errata list were read during
this development; that supplied list contains no correction of this
passage. This observation is limited to the supplied list.

The new proof is an internal deduction combining the two specified
preceding results, rather than a proof attributed verbatim to either
source. The representing witnesses, named infrastructure and two
relative-dual assertions remain explicit inputs. Applicable
representability under the source's division and global hypotheses,
comparison with the complete source moduli functor, etaleness of
original forgetting, and rigidity from Harris smallness remain
obligations. Canonical-model comparisons, uniformization and actual
coefficient local systems and their descent comparison remain open.
This conditional torsor input does not complete the source cover
theorem or the host task.

All code and prose in this pair are by Worker 57. The pinned environment
is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
