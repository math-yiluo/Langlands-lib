# A principal-open construction from a fibre-dense affine open

`SmoothDvrPrincipalOpen.affinePrincipalOpenMeetingClosedFibre` constructs a
global function `f` on an actual smooth, quasi-compact, separated scheme `Y`
over a DVR `R`, with a specified fraction field `K`. It assumes that the
actual pullback of `Y` to `Spec K` is affine, that the special fibre has a
point, and that an affine open `W` is supplied with the following property:
every special-fibre point has a generization in `W` lying in the special fibre.

The result is a subtype containing the chosen function, a proof that `Y_f`
is affine, a proof that the prescribed canonical affinization map is an
isomorphism over `D(f)`, and a point of `Y_f` in the special fibre. The output
function need not be nonvanishing on every component of the special fibre.
The construction requires no connectedness, integrality of the total scheme,
henselianity or excellence assumption.

This is the principal-open argument in Bosch, Lütkebohmert and Raynaud,
*Néron Models* (Springer, 1990), §6.5, Lemma 6, printed page 161 (PDF page 168),
with the fibre-dense affine open kept as a supplied input. Its existence is
the separate affine-neighbourhood ingredient from §6.4, Lemma 4, printed
page 155. This module does not construct that affine neighbourhood and
does not prove unconditional group-scheme affineness.

The registered source is
`bosch-lutkebohmert-raynaud-1990-neron-models`, SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
The helper lemmas below express the internal formal route implementing the
source's argument.

The proof first observes that a special-fibre point has a generic-fibre
generization because a flat morphism is generalizing. If a point lies outside
`W`, choose a generization maximal in the closed complement. If it were
special, the assumed fibre-density supplies a proper special generization
in `W`, and flatness supplies a further proper generic generization.
The stalk at the maximal complement point is a factorial domain by regularity
and factoriality of smooth DVR stalks. The lemma
`FactorialAffineComplement.false_of_generization_chain` rules out this chain.
Thus every complement point has a generic-fibre generization outside `W`.
The maximal-generization lemma is reused from the abelian-scheme development;
that lemma itself is entirely topological and has no abelian-scheme hypothesis.

The uniformizer basic open is the actual generic fibre, using the localization
description of the specified fraction field and the range of the pullback open
immersion. It is affine by the generic-affineness hypothesis.
A basic-open neighbourhood inside `W` in this affine generic open is defined by
a function on the generic open. Quasi-compactness and quasi-separatedness clear
its uniformizer denominator to a global function.

The proof divides this global function by the largest possible power of the
uniformizer. To justify finiteness without total integrality, it uses the germ
at a chosen special-fibre point. Nonvanishing at a generization implies that
this germ is nonzero: specialization of stalks would otherwise send it to a
zero unit. The Krull intersection theorem in the noetherian local stalk
bounds the possible powers. The global division lemma of `SmoothDvrGlobalSections` then shows that
the normalized function is nonvanishing somewhere on the special fibre.
Division does not change its principal open on the generic fibre.

If its principal open had a point outside `W`, the complement-generization
lemma would give a generic point outside `W` in that same principal open,
contradicting its construction. The principal open therefore lies in the
affine `W` and is itself affine. Finally,
`isIso_toSpecΓ_restrict_basicOpen` supplies the isomorphism for the prescribed
canonical affinization map. Classical choice packages this existence proof
as the stated function subtype.
