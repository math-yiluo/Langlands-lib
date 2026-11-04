# Canonical maps between central maximal tori

Author: Worker 1487.

This internal construction uses actual
`NilpotentCentralTorusQuotientData` for smooth connected affine geometrically
nilpotent groups over the same arbitrary field in universe `u`.
Such data are constructed in `Nilpotent.CentralQuotient`. The results
below use their stated fields; they do not assume that the quotient is
unipotent.

Every homomorphism from a torus into the ambient group factors uniquely
through the chosen central maximal torus. Indeed, its composite with the
quotient map has trivial all-test range, since the quotient receives no
tori. Every point of its image therefore belongs to the actual kernel
range of the quotient, which is the all-test range of the chosen torus
inclusion. The representing-subgroup factorization constructs an actual
group-scheme homomorphism. Monomorphy of the closed inclusion gives
uniqueness.

`torusMap` consequently assigns a homomorphism between the chosen tori
to every homomorphism between the ambient groups. Its composite with the
target torus inclusion is the original source inclusion followed by the
ambient homomorphism. The assignment preserves identity and composition,
as follows by composing with the monic target inclusion.
`torusMapIso` applies this to an ambient isomorphism and its inverse.
In particular, `torusIso` identifies two choices over the same ambient
group by an actual isomorphism commuting with the inclusions.

For any maximal torus of the ambient group, its unique factorization
through the chosen torus must be an isomorphism by maximality.
Thus all maximal tori have equal all-test range. Every ambient
automorphism over the original field preserves this range; the theorem
`torus_range_comp_aut` asserts this equality of subgroup functors.
It does not assert invariance under automorphisms over arbitrary
extensions or relative bases, or preservation of maximality after field
extension.

All results are internal deductions from the constructed quotient, its
exact kernel and absence of tori, maximality and the existing
representing-subgroup factorization. This module supplies no new
literature translation and no proof of unipotence of the quotient or
of the parent no-torus theorem.
