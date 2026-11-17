# Integral root generation on adjoint pinned charts

Worker 632.

This internal construction isolates the integral criterion on the adjoint
charts used in Task 6584. Its motivation is Brian Conrad, *Reductive group
schemes* (2014), Remark 6.4.5, p.233, and the proof of Proposition 6.4.4,
pp.232–233, registered as `conrad-2014-reductive-group-schemes`. Remark 6.4.5
uses the fact that an adjoint semisimple root datum decomposes into adjoint
irreducible factors. The present module proves the lattice criterion on a
supplied chart; it does not construct that decomposition or a Weil restriction.

`AffineAdjointPinnedModel` extends the Library's `AffinePinnedModel` by the
condition that its roots span its **entire integral character lattice**.
The full lattices and the perfect pairing are retained; no saturation or
rational span replaces this condition.

The root-span comparison under an equivalence of full root data is proved
by mapping the integral span using its weight map and using surjectivity.
It gives `CoordinateRootDatum.rootSpan_fieldRealization_iff`. Integral
root generation also implies that the additive exponent subgroup generated
by the roots is the whole character group.

`AffinePinnedModel.center_eq_bot_of_rootSpan_eq_top` proves triviality of
the full scheme-theoretic centre over the original ring. The published
`centerKernel_isSchemeTheoreticCenter` identifies this centre with the
diagonalizable group of the full character quotient by the root subgroup.
That quotient is trivial under the integral spanning condition, so its
characters, and hence all of its points on every relative test scheme,
are trivial. This accounts for central infinitesimal points as well.

`AffinePinnedModel.isAdjoint_field_iff` compares the integral root criterion
with adjointness on any supplied field-valued fibre using the original
algebra structure. Necessity applies the published
`IsAdjoint.rootSpan_eq_top` and the full-lattice realization comparison.
Sufficiency applies the published split semisimplicity criterion to the
trivial character quotient and pulls back the trivial centre just proved
over the ring.

The residue-field and geometric-fibre equivalences follow from actual
residue-field maps and the published adjoint field-extension comparisons.
The integral condition implies `IsFibrewiseAdjoint` on every base, including
the empty one. Its converse is stated only with `Nonempty M.base`, since
the fibre condition is vacuous over an empty scheme.

`AffineAdjointPinnedModel.isFibrewiseAdjoint` and `.center_eq_bot` expose
these consequences of the stored criterion. All schemes and coefficient
fields occur in the arbitrary universe `u`; no restriction on
characteristic or reducedness of the base is imposed. These are internal
compositions of Library results, not independently quoted assertions from
the motivating source.
