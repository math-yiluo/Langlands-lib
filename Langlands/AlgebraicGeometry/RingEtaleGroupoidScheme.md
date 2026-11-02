# Ring étale groupoids and affine étale equivalence relations

Author: Worker 266. `RingEtaleGroupoid.toScheme` copies the Library
construction `RingEtaleEquivalenceRelation.toScheme` (module
`RingEtaleEquivalenceRelationScheme`, Worker 122).
`EtaleEquivalenceRelation.ringEtaleGroupoid` copies the proof of the Library
theorem `etaleEquivalenceRelationRingForm` (module
`EtaleEquivalenceRelationRingFormProof`, Worker 424) for the fields that do
not involve the closed immersion condition.

## Declarations

`RingEtaleGroupoid.toScheme hE`, for `hE : RingEtaleGroupoid t` with
`t : B →+* C`, is the étale equivalence relation (Library
`EtaleEquivalenceRelation`) with `U = Spec B`, `R = Spec C`,
`t = Spec.map t` and `s = Spec.map (algebraMap B C)`. The proof is the Library
proof for `RingEtaleEquivalenceRelation.toScheme`. The global-sections and
spectrum adjunction `schemePointEquiv` turns the ring axioms on the global
sections of a test scheme `X` into the scheme axioms on `X`-valued points.
For the monomorphism `j = (t, s)` the field `hom_ext` is used where the Library
proof uses the lemma `RingEtaleEquivalenceRelation.hom_ext`. The lemmas
`toScheme_U`, `toScheme_R`, `toScheme_t` and `toScheme_s` record the four
components; all hold by `rfl`.

`EtaleEquivalenceRelation.ringEtaleGroupoid E`, for an étale equivalence
relation `E` with `E.U` and `E.R` affine, says that the global sections form a
ring étale groupoid with `t = E.t.appTop` and source algebra structure
`E.s.appTop`. `refl`, `symm`, `trans` and the two étaleness fields are proved
as in `etaleEquivalenceRelationRingForm`: `FiniteEtale.affinePointEquiv`
identifies points `Spec T ⟶ E.R` with ring maps `Γ(E.R, ⊤) ⟶ T`, and
`HasRingHomProperty.iff_of_isAffine` gives étaleness of the ring maps. The new
field `hom_ext` comes from `E.mono_lift`. Two ring maps out of `Γ(E.R, ⊤)` that
agree after `E.t.appTop` and `E.s.appTop` give two points of `E.R` with equal
composites with `t` and `s`, hence with `j = (t, s)`. So the points are
equal, and so are the ring maps.

## Provenance and scope

This is internal translation between the scheme and ring forms of affine
étale equivalence relations; Stacks Project Tags 022P and 02WS define the
scheme-level notion formalised by `EtaleEquivalenceRelation`. Unlike the Library
theorem `etaleEquivalenceRelationRingForm`, `ringEtaleGroupoid` assumes
nothing about `prod.lift E.t E.s` beyond the monomorphism condition that every
étale equivalence relation has. It applies to a first level `E₀` in the proof
of NL, whose map `j₀` is not known to be a closed immersion.
