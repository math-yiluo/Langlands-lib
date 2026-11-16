# Group structure on a supplied finite closed-fibre part

Over any commutative local ring `R : Type u`, let `K` be a group scheme
and let `U` be a supplied open of its underlying scheme with
`IsFiniteClosedFibrePart K.X.hom U`. This internal construction equips
the actual open subscheme `U` with a group structure, and constructs its
actual inclusion as an open and closed subgroup of `K`.

The unit source `Spec R`, the finite scheme `U`, and the product `U ×_R U`
are finite, hence universally closed, over `R`. The lifting helper
`IsFiniteClosedFibrePart.lift` therefore restricts the ambient unit,
inverse and multiplication to `U`. Their composites with the inclusion
are proved equal to the original maps. The published
`GroupObjectDescent.grpObjOfMono` supplies the group laws by cancellation
of the monomorphic inclusion; its homomorphism theorem proves the
inclusion preserves the group law. Thus `group` and `inclusion` retain
these actual schemes and morphisms.

The structure map of `group` is finite by the supplied finite-part
hypothesis. Flatness and local finite presentation are inherited from
`K → Spec R` by composition with the open immersion. The inclusion's
range is exactly `U`, so it contains every point of the closed fibre.
All statements and constructions are universe-polymorphic.

This is source-free internal composition of the paired lifting helper,
Mathlib's finite-morphism and open-immersion APIs, and the published
group-object restriction construction. It assumes the finite part; it
proves neither its existence nor normality in any ambient group.
