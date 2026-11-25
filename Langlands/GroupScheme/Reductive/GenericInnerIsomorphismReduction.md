# Inner corrections from an actual integral inner-isomorphism torsor

This derived reduction uses the actual data in
`GenericInnerIsomorphismTorsor`. It asserts no existence of that data.
Its purpose is to isolate the geometric construction from the final torsor
and point calculations in Conrad's proof of Theorem 7.2.16 (2014),
pp.261–262, registered source `conrad-2014-reductive-group-schemes`,
SHA-256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

The canonical isomorphism between two actual field-level adjoint quotients
intertwines their inner actions. The proof checks equality after an fpqc
local lift of the acting point, where both actions are conjugation.
It does not assume that rational adjoint points lift globally.

For an actual integral section `p` of the supplied torsor, let `k` be the
unique group point carrying the prescribed generic point to `p`'s generic
image. The evaluation compatibility of the torsor says that the isomorphism
at `p` equals the given generic isomorphism precomposed with the inner action
of `k⁻¹`. The proof transports this inverse through the actual pullback point
equivalence and checks the resulting equation on every scheme over `K`.

`exists_correction_for_quotient_of_section` sends this correction through
the canonical comparison with any supplied actual adjoint quotient and uses
the preceding inner-action comparison. `exists_correction` first obtains
the section by `nonempty_section`, assuming completeness at a maximal ideal
with finite quotient. These assertions retain the torsor as an explicit
hypothesis; they do not construct it.

The final theorem
`reductiveLocalIntegerIsomorphism_of_genericInnerIsomorphismTorsorExistence`
proves the implication from the separate geometric existence statement over
all DVRs to `ReductiveLocalIntegerIsomorphismStatement`, in
every universe. For a nonarchimedean local field, Mathlib supplies the DVR
of integers, its fraction-field structure, finite residue field and adic
completeness. The proof installs the compatible additive uniform structure
used by Mathlib's completeness instance, obtains the geometric torsor from
the assumed existence statement, and applies `exists_correction`.
The supplied generic isomorphism and arbitrary adjoint quotient are unchanged.
This is a conditional reduction, and the existence statement remains
unproved in this module.
