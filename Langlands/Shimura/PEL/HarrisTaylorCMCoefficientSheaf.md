# Full Harris torsion coefficient sheaves on original CM schemes

Author: Worker 57.

This derived specialization constructs an actual module sheaf on the small
etale site of the original chosen CM scheme, using its original normal
coefficient-kernel cover. It also constructs the evaluation isomorphism after
localization at that cover and proves that the cover covers the final object.
The sheaf and its local trivialization are constructed from the coefficient
action and the proved geometric torsor; neither is supplied as output data.

## Parameters and remaining inputs

Retain the central simple unitary data `D`, Harris signature charts `C`, and
all inherited tensor, Picard, duality, polarization, finite Weil, rational
profinite-integer/adele comparison and torsion inputs displayed in the Lean
variable declarations. The exact `CMRepresentabilityStatement ... q` defines
`cmSchemeTower ... q` through its original chosen representation witnesses.
For a small CM level `U`, write `X` for that tower's scheme at `U` and `J`
for `Scheme.smallEtaleTopology X`.

The further geometric inputs are
`RelativeDualSchemeExistenceStatement.{0}`,
`RelativeDualSchemeGeometryStatement.{0}`, and
`CMGeometricCoarseRigidity ... U.obj`. Exact representability, these dual
assertions and coarse rigidity remain premises. The generic
`DominantUnramifiedEtaleStatement.{0}` is discharged here by
`DominantUnramifiedEtaleProof.dominantUnramifiedEtale`; it is not a new
premise. No etaleness, surjectivity, kernel-comparison isomorphism, torsor
structure or local trivialization of the original map is an extra premise.

Assume `Module.Finite ℚ A`. Let `K` be a number field, `W` a finite
`K`-module and `ρ` an algebraic representation of
`D.rationalInvolution.baseChange K` on `W`. Fix a rational finite place `p`,
a natural scalar `m` with `hm : m ≠ 0`, and an exponent `k : ℕ`. Set

```text
V = cmHarrisCoefficientLevel D ρ p U m hm k
Q = SmallCMResidualGroup D U V
R = HarrisCoefficientReductionRing K p m k
M = cmHarrisCoefficientAction D ρ p U m hm k.
```

These are the actual small normal kernel level, original residual quotient,
full coefficient quotient ring and its descended module action from
`HarrisTaylorCMCoefficientReduction`. All coefficient places above `p`
remain in `R` and `M`. The scalar hypothesis permits every nonzero natural
`m`; no primality, positive exponent or freeness is assumed.

## Original cover and invariant sheaf

`cmHarrisCoefficientTorsor` specializes
`cmNormalGeometricTorsor_of_dominantCriterion` to `V`, using the proved
inclusion `cmHarrisCoefficientLevel_le` and the published dominant
criterion proof. Its value is an action `Y : Action X.Etale Q`, paired
with a proof of `IsFiniteGeometricTorsor X Y`. Etaleness is part of the
small-etale object; the predicate proves finite acting group, finite and
scheme-surjective structural morphism, and unique residual translation
between separably closed field-valued points over the same base point.

The equations `cmHarrisCoefficientTorsor_left`,
`cmHarrisCoefficientTorsor_hom` and
`cmHarrisCoefficientTorsor_ρ_left` identify the source with the chosen
original scheme at `V`, the structural morphism with that tower's original
forgetting map, and each deck map with `cmNormalQuotientAction`. Each
proof is reflexivity. The construction preserves the original opposite
CM group and its inverse-right scheme action.
`cmHarrisCoefficientTorsor_coversTop` applies
`etale_coversTop_of_surjective` to the actual torsor's scheme surjectivity.
It proves `J.CoversTop (fun _ : Unit => Y.V)`.

`cmHarrisCoefficientSheaf` is
`(etaleAssociatedFunctor X Y).obj M`, an object of
`Sheaf J (ModuleCat.{0} R)`. More explicitly, apply the base constant-sheaf
functor to the coefficient module and action. If `F` denotes this action
in sheaves, the sheaf is the limit of the diagonal action on
`(productSheaf J Y.V).obj F.V`. Its action at `g : Q` is pullback along
the deck map `Y.ρ g⁻¹`, followed by the coefficient map `F.ρ g`.
Thus the inverse-deck and coefficient conventions are fixed by the actual
imported `diagonal` construction.

`cmHarrisCoefficientInclusion` is the limit projection into sections over
the cover. `cmHarrisCoefficientInclusion_invariant` is the corresponding
limit-cone identity, obtained from `inclusion_invariant`: composing this
inclusion with any diagonal action map gives the inclusion again.

## Evaluation on the coefficient cover

`cmHarrisCoefficientTrivialization` is an isomorphism

```text
(J.overPullback (ModuleCat R) Y.V).obj (cmHarrisCoefficientSheaf ...)
  ≅ (J.overPullback (ModuleCat R) Y.V).obj
      ((constantSheaf J (ModuleCat R)).obj M.V).
```

It applies `constantAssociatedTrivializationOfSplitting` to `M`, with
`etaleTorsorSectionSplitting X Q Y hY R` supplying the section-splitting
proof from the actual finite geometric torsor. The published splitting
and trivialization proofs establish invertibility; no section-splitting
assertion is assumed here.

`cmHarrisCoefficientTrivialization_hom` identifies its hom with
`associatedEvaluation J Y F`. The expanded equation
`cmHarrisCoefficientTrivialization_hom_eq` identifies the same map with
the localized invariant inclusion followed by `productEvaluation`.
For an object `T ⟶ Y.V` of the slice, this last map restricts sections
along its tautological graph `T ⟶ Y.V × T`. Both identifications are
reflexive equations of the implemented construction. The target is the
restriction of the constant sheaf on the base site; this module does not
construct a separate comparison to a constant sheaf formed on the slice.

## Sources, derivation and scope

The motivating sources are Harris, *Galois properties of cohomological
automorphic forms on GL(n)* (1999), Section 3, printed pp.306–308,
one-based PDF pp.8–10, especially the stable lattice, inverse equivariance
in (3.7), and finite congruence-quotient factorization before (3.8);
and Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, PDF pp.98–99, and III.2,
printed pp.94–95, PDF pp.102–103. III.1 gives right frame composition and
the normal-level Galois-cover assertion. III.2 constructs coefficient
sheaves from finite quotient actions by inverse-equivariant functions on
connected components and states independence of choices and functoriality.
The registered sources and content hashes are:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The supplied five-page author errata list was checked; it identifies no
correction to these passages. This observation is limited to that list.
This module is an internal composition of the coefficient reduction,
original CM torsor and generic invariant-sheaf/evaluation constructions.
It proves the displayed specialization and identifications. It does not
prove a function-on-components comparison, comparison of representation
normalizations, independence of choices, compatibility as the scalar or
exponent varies, arbitrary scheme inverse-image compatibility, freeness,
or the source's entire lisse adic construction. Applicable existence,
source-moduli comparison, source rigidity and canonical-model geometry
remain obligations of the surrounding development. This conditional
coefficient specialization does not complete those obligations.

The code and prose in this pair are by Worker 57; only published generic
sheaf constructions are reused. The pinned environment is Lean 4.34.0
with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
