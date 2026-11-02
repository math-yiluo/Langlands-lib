# Direct-image base change to an open

For any scheme morphism `f : X ⟶ Y`, open `V` of `Y`, and module sheaf
`M` on `X`, `openDirectImageBaseChangeIso f V M` identifies the pullback
of `f_* M` to `V` with the direct image along `f ∣_ V` of the pullback
of `M` to `f⁻¹ V`. It is the composite of the inverse of the restriction-to-pullback
isomorphism on the base, the inverse of `restrictPushforwardIso`, and the
pushforward of the restriction-to-pullback isomorphism on the source.

`restrictPushforwardIso_inv_adjoint` computes the adjunct of the ordinary
restriction comparison. On every open, both sides are composites of the
same presheaf restriction maps. The proof combines these maps and uses
uniqueness of morphisms in the poset of opens.

`pushforwardBaseChange_morphismRestrict` proves that the homomorphism of
`openDirectImageBaseChangeIso` is exactly the published map
`pushforwardBaseChange V.ι f (f ∣_ V) (f ⁻¹ᵁ V).ι
  (isPullback_morphismRestrict f V).w.symm M`.
After cancellation of the base restriction-to-pullback isomorphism,
the proof applies the restriction adjunction. The computed adjunct,
naturality of the pushforward comparison, and compatibility of the two
adjunction units under uniqueness of left adjoints give the equality.
`isIso_pushforwardBaseChange_morphismRestrict` follows from that equality.
No quasi-coherence, finiteness, flatness, or separation condition is assumed.

This is an internal derived result. Its provenance is the formal adjunction
construction of `pushforwardBaseChange` in `DerivedRestriction`, the
restriction comparison in `HigherDirectImageOpenRestriction`, and Mathlib's
restriction adjunction and uniqueness of left adjoints. It introduces no
additional geometric assertion from external literature.
