# Schwartz–Bruhat closure of the first-block partial Fourier integral

This derived module realizes the existing plus-sign
`rowPartialFourierIntegral ψ μ e Φ ξ v` as the value of a Schwartz–Bruhat function
at the joined row `join e ξ v`. It retains the supplied scalar Haar measure,
the arbitrary coordinate placement, and all finite block dimensions, including
zero. It assumes that the scalar Haar measure is self-dual for the supplied
character.

The proof uses the published finite joined-tensor expansion of the full-row
Schwartz–Bruhat function. Self-dual row Fourier closure transforms each
first-block tensor factor into a Schwartz–Bruhat function. The finite sum of
the joined transformed first factors and unchanged second factors is again
Schwartz–Bruhat. The published tensor integral formula identifies every value
of this sum with the actual partial Fourier integral.

`partialFourierSchwartz` selects such a function; its value is uniquely
determined by `partialFourierSchwartz_join`, since every row is a joined row.
`partialFourierSchwartz_apply` gives the equivalent formula in terms of the
first and second coordinate projections.

This supplies compact support and boundedness of the transformed function for
the diagonal estimates in the lower-unfolding convergence argument. Its
provenance is internal: the new conclusion follows from the existing tensor
expansion, Fourier closure and tensor integral formulas, with no additional
assertion from the literature.
