# Global functions and products of flat schemes over a PID

This internal auxiliary construction supplies the global-function comparison used
by canonical affinization of flat groups. It applies in every universe and makes
no finite-generation assumption.

`flat_sections` proves that global functions of any flat scheme over a principal
ideal domain are flat over that domain. It combines the Library's
`Smoothening.isTorsionFree_sections` with torsion-free-implies-flat over a
Dedekind domain. `flat_appTop` translates this into flatness of the actual
structural ring map, using the spectrum/global-sections isomorphism of the base.

`isPushout_appTop` is the global-section form of Mathlib's
`isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`. Both factors
are quasi-compact and quasi-separated, the base is affine, the right scheme map
is flat, and the left structural ring map is flat. Neither factor is assumed
affine. `isPushout_appTop_pid` discharges the last condition when both schemes
are flat over a PID. It gives the canonical ring pushout, equivalently the
canonical tensor-product description of global functions of their fibre product.
`globalFunctionsProductIso` supplies the actual canonical isomorphism from the
ring pushout to the global functions on the product.

The reason for this auxiliary unit is the natural group structure on
`Spec Γ(G, O_G)` used in Prasad–Yu, *On quasi-reductive group schemes*, author
preprint p.5, Proposition 3.1. The PID scope and the implemented reduction to
Mathlib's flat global-section comparison are internal; they are not a claim
that Prasad–Yu states this auxiliary result in this generality.
