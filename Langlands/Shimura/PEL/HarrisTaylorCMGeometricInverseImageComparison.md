# Inverse-image comparison for exact geometric CM coefficients

Author: Worker 57.

This internal construction identifies the existing inverse image of the full
original CM coefficient system with association on the exact geometric CM
coefficient covers. The isomorphism respects every coefficient reduction and
uses the existing canonical cartesian cover comparison. Its component maps and
its forward invariant-inclusion formula are specified in Lean.

## Inputs and exact systems

The arithmetic and geometric inputs are exactly those of
[HarrisTaylorCMGeometricAssociatedSystem](HarrisTaylorCMGeometricAssociatedSystem.md):
the universe-zero number fields E, F, L and K, central simple unitary datum D,
Harris signature charts C, finite rational algebra A, finite-dimensional
algebraic representation ρ over K, small level U, rational finite place p and
nonzero natural number m. The tensor, Picard-zero, duality, polarization,
Weil-transition, adelic-comparison and torsion-finiteness premises are retained.
The exact representability premise q, relative dual existence and geometry
premises, and coarse geometric rigidity at U remain explicit. Neither the
comparison nor any replacement coefficient system is supplied as an input.

Write X for the existing original CM scheme at U, Xbar for its existing base
change to the algebraic closure of F, and
`π = (cmGeometricProjection ... q).app U`. This is the actual fiber-product
projection. The inverse-image functor is `EtaleInverseImage.inverseImage π R`,
where `R = HarrisCoefficientIntegers K p` is the full product integral ring.
There is no etaleness premise on π.

The group diagram is the existing `cmHarrisCoefficientGroups D ρ p U m hm`.
The unchanged coefficient diagram M is
`cmHarrisCoefficientDiagram D ρ p U m hm`. At exponent k its underlying module
is the full original stable-lattice reduction with R scalars. Its transitions
are the original lattice reductions, retaining the opposite-group action
convention. Let Y be the original coefficient-cover diagram, Ybar the exact
geometric coefficient-cover diagram, and

```text
Ypull = (etaleTorsorDiagramPullback π groups).obj Y.
e : Ybar ≅ Ypull = cmHarrisGeometricCoefficientEtaleDiagramPullbackIso ...
```

All torsor properties are the existing proved properties of these exact
covers. At each index e is the canonical cartesian comparison, and the
published diagram isomorphism already respects all transitions and actions.

## Whole-system comparison

`cmHarrisGeometricCoefficientSystemAssociatedIso` has type

```text
cmHarrisGeometricCoefficientSystem ...
  ≅ cmHarrisGeometricAssociatedCoefficientSystem ...
```

Both sides are functors from `ℕᵒᵖ` to actual small-etale sheaves of R-modules
on Xbar. The first side is the existing original associated coefficient system
postcomposed with inverse image along π. The second is association on Ybar,
with the same group and coefficient diagrams M.

The definition first evaluates the published natural isomorphism
`etaleAssociatedVaryingSystemInverseImage π R Y originalProperty` at M. This
identifies inverse image of the entire original associated system with the
system associated to Ypull. It then composes with the existing
`cmHarrisGeometricAssociatedCoefficientSystemCoverIso`, which identifies the
Ypull system with the system associated to Ybar. Consequently the construction
is an isomorphism of entire diagrams, including the inverse-cover transitions.

The `_hom_app` lemma identifies the forward component with
`inverseImageConstantAssociatedIso` at the original cover and M_k, followed by
`etaleCrossCoverMap` along e.hom at k and the identity of M_k. The `_inv_app`
lemma reverses these steps, using e.inv and the inverse arbitrary-morphism
comparison. Both formulas follow by reflexivity.

The `_transition` theorem states that inverse image of the original transition
followed by the comparison at j equals the comparison at i followed by the
geometric associated transition. The `_inv_transition` theorem gives the
reverse square. These are naturality of the constructed forward and inverse
system morphisms, so every original coefficient reduction is retained.

## Invariant inclusions

Let ι_k be the original invariant inclusion on Y_k, and let ιbar_k be the
invariant inclusion on Ybar_k. The theorem `_hom_inclusion` states that the
forward comparison followed by ιbar_k is the composite of these four maps:

1. Inverse image of ι_k.
2. The forward `inverseImageProductSheafIso` for the original finite geometric
   torsor and the constant sheaf of the underlying coefficient module on X.
3. The product sheaf on Ypull_k applied to the forward
   `inverseImageConstantIso` for that same module.
4. `coverPullback` along the underlying map e.hom at k, with the constant
   coefficient sheaf on Xbar.

The proof expands the two system comparisons, applies the published
geometric cover-comparison inclusion identity, and then applies
`inverseImageConstantAssociatedIso_hom_inclusion`. This recovers the actual
invariant maps, including the original cartesian cover coordinate, rather
than only an abstract objectwise existence assertion.

## Provenance and remaining scope

This is an internal composition and specialization of the published modules
[EtaleInverseImageVaryingSystem](../Coefficients/EtaleInverseImageVaryingSystem.md),
[HarrisTaylorCMGeometricAssociatedSystem](HarrisTaylorCMGeometricAssociatedSystem.md)
and their exact geometric cover inputs. No external-literature theorem is
newly asserted here; source provenance for the arithmetic and moduli inputs
remains in the paired imported modules.

The exact moduli representability theorem, rigidity, canonical-model geometry
and other named premises remain obligations. This unit supplies no new
derived, cohomological, quotient-ring scalar, inverse-limit or lisse-adic
assertion and does not complete the host task.
