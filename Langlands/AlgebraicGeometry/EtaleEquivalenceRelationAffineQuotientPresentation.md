# Invariant-ring presentations from affine quotients

Author: Worker 148.

This internal result identifies the ring of an actual faithfully flat affine
quotient with the unchanged invariant ring of its relation. It then supplies
faithful flatness and the tensor coordinates used by the coaction Amitsur
argument. All rings and schemes have an arbitrary universe `u`.

For the algebraic construction, let `A`, `B`, and `C` be commutative rings with
algebra structures `A → B` and `B → C`, and let `t : B → C` be another ring
map. Assume that the square with the two copies of `A → B` and the maps
`algebraMap B C` and `t` is a pushout. Write `I = invariantRing t`, the
published subring of elements `b` satisfying `t b = algebraMap B C b`.
Commutativity of the square defines `quotientToInvariant : A → I`.

If `B` is faithfully flat over `A`, then
`mem_invariantRing_iff_mem_range` proves that `I` consists exactly of
the image of `A → B`. The tensor equivalence from
`EtaleEquivalenceRelationAffineCoordinates` identifies `C` with `B ⊗[A] B`,
sending `t b` to `1 ⊗ b` and the source inclusion to `b ⊗ 1`.
Mathlib's `Algebra.IsEffective.of_faithfullyFlat` identifies the equalizer of
these tensor inclusions with the image of `A`. Faithful flatness also makes
`A → B` injective. Thus `quotientToInvariant_bijective` proves bijectivity
and `quotientInvariantEquiv` constructs the resulting ring isomorphism
`A ≃+* I`, whose composite with the inclusion into `B` is the original map.

`faithfullyFlat_invariantRing_of_isPushout` transports the faithfully flat
map `A → B` through that isomorphism, obtaining the actual published
inclusion `I → B`. `invariantRing_isPushout_of_isPushout` transports the
original pushout square through the same isomorphism.
`invariantTensorEquivOfIsPushout` consequently gives the `B`-algebra
isomorphism `B ⊗[I] B ≃ₐ[B] C`; its target formula sends `1 ⊗ b` to `t b`.
No effective-presentation assumption has been dropped: it is derived from the
explicit pushout and faithful-flatness hypotheses.

The scheme theorem `invariantPresentation_of_hasAffineQuotient` applies this
construction to an actual `EtaleEquivalenceRelation E` with affine object
scheme and `E.HasAffineQuotient`. Unpacking that unchanged hypothesis gives
an affine scheme `M`, a flat surjective map `q : E.U → M`, and the pullback
identifying `E.R` with `E.U ×[M] E.U`. The relation scheme is affine by this
pullback. Affine duality turns the square into the required ring pushout,
and Mathlib's affine criterion turns flatness and surjectivity of `q` into
faithful flatness of its global-sections map. The algebraic results give both
faithful flatness of `Γ(E.U, ⊤)` over `invariantRing E.t.appTop.hom` and an
effective tensor presentation with its target formula. The source algebra
structure throughout is induced by the actual map `E.s.appTop`.

The content is derived internally from the cited Lean interfaces, rather than
transcribed from a separate literature statement. It uses no affine-descent or
acyclicity conclusion. It supplies a prerequisite for the host acyclicity
task; the geometric finite-cover argument remains a separate obligation.
