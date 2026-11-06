# Twisted intertwiners and the Hom-space consequences of Schur

This is internal algebraic support for the comparison and endomorphism
arguments in Renard, *Représentations des groupes réductifs p-adiques*,
2026 version, VI.5.3 (printed p. 173, PDF p. 179). It derives the needed
consequences from Mathlib's Schur lemma for maps between irreducibles, the
published `CuspidalSupport.isIrreducible_comp_of_surjective`, and Mathlib's
module-length inequalities. It does not assume an unproved geometric lemma.

The field, group, and two carrier types have independent universes.
The results require no topology, smoothness, finite-dimensionality,
admissibility or algebraic closure.

`twistedIntertwiner_bijective` starts with irreducible representations `ρ, σ`
of the same group, a surjective endomorphism `α` of that group, and a nonzero
linear map `S` satisfying

`S (ρ (α h) v) = σ h (S v)`.

The pullback `ρ.comp α` is irreducible by the published surjective-pullback
lemma. The displayed identity makes `S` an actual intertwiner from that
pullback to `σ`. Mathlib's bijective-or-zero theorem then makes `S` bijective.
`twistedIntertwinerEquiv` constructs the resulting actual representation
equivalence, whose underlying function is the supplied map `S`.

`intertwiningMapEquivEnd e` identifies `Hom(ρ, σ)` with `End(ρ)` for a
supplied equivalence `e : ρ.Equiv σ`, by postcomposition with `e.symm`.
Postcomposition with `e` is its inverse.

`length_end_le_one_of_scalar` assumes every endomorphism of `ρ` is a scalar
multiple of the identity. The scalar-to-endomorphism linear map is then
surjective, so the endomorphism space has module length at most the length
one of the coefficient field. `length_hom_le_one_of_scalar` assumes both
representations are irreducible and the same scalar property on the source.
If every intertwiner is zero, the Hom length is zero. Otherwise Schur makes
a nonzero intertwiner an equivalence, and `intertwiningMapEquivEnd` transfers
the length bound from the source endomorphism space.

Finally, `intertwiningMap_eq_zero_of_not_equiv` and
`length_hom_eq_zero_of_not_equiv` record vanishing between inequivalent
irreducibles, again by the bijective-or-zero theorem.

The scalar property in the length lemmas is explicit. This file does not
assert scalar Schur for an arbitrary field or arbitrary irreducible
representation, nor does it prove the maximal-Levi dichotomy.
