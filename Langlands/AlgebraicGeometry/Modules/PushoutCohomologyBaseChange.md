# Canonical cohomology base change over an algebra pushout

For commutative rings `R`, `S`, `A`, and `B` in arbitrary universe `u`,
assume algebra structures along the square `R → S`, `R → A`, `S → B`,
`A → B`, with the two compatible scalar towers. The lemma
`affineAlgebraSquare_comm` proves that their spectra form a commuting
square. Compatibility of the two composites of algebra maps proves the
equality after applying `Spec.map`.

For every actual module sheaf `M` on `Spec A`,
`sectionsBaseChangeMap_affineAlgebraSquare` identifies the ordinary
sections map of `CohomologyBaseChangeZero` with
`pushoutAffineSectionsPullbackMap R S A B M`. The equality follows
by extensionality on sections: both maps apply the same pullback
adjunction unit. The scalar-adjunction definitions then give
`scalarSectionsBaseChangeMap_affineAlgebraSquare`, identifying the
scalar map with `pushoutAffineScalarSectionsMap`. These equalities
require the compatible square, without the pushout or quasi-coherence
assumptions.

Assume additionally `Algebra.IsPushout R S A B` and that `M` is
quasi-coherent. Write `f : Spec A → Spec R`,
`f' : Spec B → Spec S`, and `g : Spec B → Spec A` for the indicated
maps. The published `isZero_higherDirectImage_affinePullback`
supplies vanishing of all positive higher direct images of `g^*M`
along `g`; hence the published scalar cohomology base-change map is
defined without any extra acyclicity premise.

The instance `isIso_scalarBaseChangeMap_zero_affinePushout` proves
that this actual map is invertible in degree zero. It rewrites the map
using `scalarBaseChangeMap_zero` and the affine sections
identification. The resulting factors are the canonical zeroth-derived
isomorphisms and the published quasi-coherent affine pushout sections
isomorphism.

The instance `isIso_scalarBaseChangeMap_affinePushout` proves
invertibility for every `n : ℕ`. At zero it uses the preceding
instance. At `q + 1`, the published
`affineQuasicoherentCohomologyVanishing` makes the source relative
cohomology zero. Extension of scalars is additive, so its value on this
zero object is zero as well. Affine pullback preserves quasi-coherence
by the imported `AffinePullbackQuasicoherent` result. The same
published vanishing theorem therefore makes the target relative
cohomology zero. `IsZero.isIso` proves that the given map between
these zero objects is an isomorphism.

The selected definition `scalarBaseChangeAffinePushoutIso R S A B M n`
packages this map as an isomorphism

`S ⊗_R H^n_R(Spec A,M) ≅ H^n_S(Spec B,g^*M)`.

It is `asIso` of the published `scalarBaseChangeMap` with the
canonical affine acyclicity proof. The lemma
`scalarBaseChangeAffinePushoutIso_hom` states by reflexivity that its
forward map is exactly that map. Thus the construction specifies the
comparison morphism as well as its invertibility. No flatness,
finiteness, noetherian, or reducedness hypothesis is present. The
degree range is all nonnegative integers.

This is an internal consequence of the published affine pushout sections
construction, degree-zero comparison formulas, affine pullback
quasi-coherence, and affine cohomology vanishing. It invokes no new
external source assertion. It supplies affine terms for a possible
Cech base-change comparison; it does not prove flat base change for
general nonaffine schemes or the relative cube theorem.
