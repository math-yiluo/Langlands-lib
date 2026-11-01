# Finite actions on the canonical relative integral endomorphism presheaf

This internal construction connects the finite integral-action equations to
the exact relative endomorphism presheaf used in
`RelativeEndomorphismRepresentabilityStatement`.
The base scheme `S` and the supplied actual abelian scheme `B/S` have an
arbitrary universe `u`. No noetherian, projective or representability
hypothesis is needed for the constructions.

For `T : Over S`, the ring is the actual categorical endomorphism ring
of `(baseChange T.hom).obj B`. Its underlying set is exactly the
published `Cartier.RelativeHom B.toCommGroupScheme B.toCommGroupScheme T`.
Multiplication has the existing categorical convention `f*g = g ≫ f`;
addition is the pointwise commutative group law.

For every morphism `a : T' → T` over `S`, `relativeEndRestrict B a`
retains the existing `Cartier.restrict`. It first pulls an actual
endomorphism back along `a.left` and conjugates it by the canonical
`baseChangeCompIso` from the two presentations of the same base change.
The existing restriction is additive. The two private lemmas prove
preservation of identity and composition: functoriality preserves the
middle identity or composition, and the adjacent inverse/hom comparison
maps cancel. Thus this same restriction is a unital ring homomorphism.
It includes the canonical iterated-pullback comparisons.

`relativeEndRingFunctor B` packages these rings and restriction maps on
the full category `(Over S)ᵒᵖ`. Its functor laws are the published
`restrict_id` and `restrict_comp`. The theorem
`relativeEndRingFunctor_forget` is a definitional equality with the
published relative-Hom presheaf after forgetting its additive structure.
It therefore fixes the same actual carriers and the same restriction
maps used in the relative End representability target.

For any finite integer basis `b : Basis I ℤ O` of a unital ring `O`,
`relativeIntegralActionFunctor B b` assigns the universe lift of actual
ring actions `O →+* End(B_T)` to `T`. After unwrapping, its morphism map postcomposes with
`relativeEndRestrict B a`. `relativeIntegralActionSolutionsFunctor B b`
assigns the universe lift of the existing finite actual endomorphism tuples satisfying the
unit and ordered basis-multiplication equations; its morphism map
unwraps, applies that same ring homomorphism to every entry, and rewraps.

`relativeIntegralActionSolutionsIso B b` specializes the natural
finite-equation equivalence to this ring-valued presheaf. At each test
scheme it is the existing actual integral-action equivalence conjugated
by the canonical unwrap/rewrap equivalences:
forward evaluation at `b_i`, and inverse reconstruction by the sum
`∑ i, b.repr(x)_i • r_i`. The comparison is natural for every actual
morphism over `S`.

`locallyNoetherianTestInclusion S` is exactly the full-subcategory
inclusion for `fun T : Over S => IsLocallyNoetherian T.left` used by the
published relative End target. Whiskering the preceding isomorphism with
its opposite gives `locallyNoetherianIntegralActionSolutionsIso`.
This retains all locally noetherian tests and all their morphisms;
there is no affine, connectedness, finite-type or reducedness restriction.
The order and basis have independent universes `uO,uI`, and the action
and tuple functors use `ULift` to take values in `Type (max u uI uO)`.
The ring-valued endomorphism presheaf itself remains unlifted.

The provenance is internal: canonical group-scheme pullback and
conjugation, the published relative-Hom functor laws, and the proved
finite-equation natural isomorphism. This does not prove relative End
representability or construct an action locus, an ambient moduli scheme,
an integral representative of a rational action, or the normalized CM
representability theorem. It supplies the precise presheaf comparison
that a subsequent representing-locus argument must consume.
