# Scheme Hecke spans from exact normalized CM representations

This module constructs actual scheme Hecke spans from the exact represented
normalized CM tower in `HarrisTaylorCMSchemeLevels`. Its inputs retain the actual
central simple unitary datum `D`, the CM-compatible Harris signature charts `C`,
the original opposite finite-adelic similitude group, and all named tensor,
Picard, duality, polarization, finite Weil, adele-comparison and torsion
prerequisites. The construction is conditional on exact representability of the
already constructed moduli presheaves. It provides no existence proof.

## Small intersections and actual transporters

Write `G` for `D.rationalInvolution.FiniteAdelicPoints` with opposite
multiplication. For `U V : SmallCMLevel D` and `g : G`,
`smallCMHeckeLevel D U V g` has underlying compact-open subgroup
`U ∩ g V g⁻¹`, with all products interpreted in this same opposite group.
The construction uses `CompactOpenLevel.heckeLevel`; its local smallness proof
is inherited from `U` by the published monotonicity theorem. Rational
finite-dimensionality is derived from `D.finite` over the number field `F`
using `Module.Finite.trans F A`. It is not supplied as another arithmetic
hypothesis. No small-level existence or cofinality is proved.

`smallCMHeckeLeft` is the inclusion transporter from this intersection to `U`,
represented by the element `1`. `smallCMHeckeRight` is the transporter to `V`,
represented by the actual element `g`. The two displayed element formulas are
proved by reduction of these constructions. The original arrow condition is
`g⁻¹ U g ≤ V`; no quotient of transporter arrows is introduced.

`smallCMInclusion` uses the identity element for a genuine subgroup inclusion.
Given inclusions `U' ≤ U` and `V' ≤ V`, `smallCMHeckeRefinement` constructs the
actual inclusion of the corresponding intersections for the same `g`.
Membership follows from the two given inclusions. Extensionality of the
transporter structures and the group identity laws prove both leg squares,
identity refinement and the composition law for successive refinements.

## Actual schemes and their class interpretation

For each small level, let `R U` be the exact `CMLevelRepresentation` of the
previously constructed presheaf. This includes an actual componentwise admissible
scheme over `Spec F`, smoothness, the specified projective-space immersion and a
natural lifted-Yoneda representation isomorphism. In particular, the input is
not a collection of arbitrary output schemes with arbitrary transition maps.

`representedCMHeckeLeft` and `representedCMHeckeRight` apply the previously
constructed `representedCMSchemeTower R` to the two actual small-level
transporters. Their common source is the represented scheme at
`smallCMHeckeLevel D U V g`; their targets are the represented schemes at `U`
and `V`. These are actual Mathlib `Scheme` morphisms. The two `_over` theorems
prove that each leg composed with its target's actual structure morphism equals
the middle scheme's structure morphism to `Spec F`. The proofs specialize the
existing tower equation in the over-category.

`representedCMHeckeSpan` packages the two scheme morphisms and this equality as
an actual `Limits.PullbackCone` over the two endpoint structure maps. It does
not supply an `IsLimit` proof: no assertion that the square is a fiber product
is made.

The two `_classes` theorems quantify over every actual test scheme `S` of
`ComponentwiseAdmissibleCMBaseCategory` and every actual morphism from `S` to
the represented middle object. Under the specified representing isomorphisms,
postcomposing with the first or second lifted map gives exactly the existing
CM moduli transition at that transporter. The scheme legs are the underlying
scheme morphisms of these lifted maps by construction. The first transporter
is the identity-element forgetting map and the second is the original
right-translation element `g`. Their action is inherited from the existing
normalized polarized CM class presheaf, including its actual geometric and
componentwise constructions. The proofs apply
`representedCMBaseTower_map_classes`; they assume no new comparison theorem.
The formulas concern this exact admissible test category and do not extend its
representability to arbitrary `F`-schemes.

`representedCMHeckeRefinement` applies the same scheme tower to the actual
inclusion of intersections. The two refinement squares commute by the
corresponding transporter equalities and the tower's composition law. Its
identity and composition theorems follow by the tower's functor laws.

For another family `R'` representing the same presheaves, the two
`_comparison` theorems prove the squares relating the respective Hecke legs
and the canonical `representedCMSchemeTowerComparison R R'`. Each proof is the
naturality equation of that existing comparison at the actual left or right
transporter. Thus both endpoint comparisons and the common middle comparison
come from the same identity of moduli presheaves. The identity and cocycle laws
for these comparisons are already proved for the full represented tower in
`HarrisTaylorCMSchemeLevels`.

Finally, `cmHeckeLeft` and `cmHeckeRight` choose `R` from a proof `q` of exactly
`CMRepresentabilityStatement`, using `chosenCMLevelRepresentation`. Their
domains and codomains are objects of the existing `cmSchemeTower q`. All named
prerequisites and the exact existence proposition remain explicit in these
constructions.

## Source and scope

The original motivation is Harris and Taylor, *The Geometry and Cohomology of
Some Simple Shimura Varieties* (2001), III.1, printed p.91 (one-based PDF p.99).
That page specifies level forgetting and the action sending the level frame
`eta` to `eta` composed with `g` under the conjugation-inclusion condition. It
also asserts representability and finite-etale and Galois cover properties.
Only the transporter and represented-map consequences are implemented here.
The source is registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

This is a derived construction by Worker 57: the implemented proof route is
subgroup membership, transporter extensionality, the existing fully faithful
Yoneda tower and its functor and comparison laws. It does not invoke a geometric
representability theorem. Source division/global applicability, comparison with
the original moduli problem, representer admissibility, geometric existence,
finite etaleness, Galois covers, canonical models, complex uniformization and
coefficient descent remain separate obligations. The exact existence proof is
not supplied by the current host task's progressive prerequisite publication.
The pinned environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
