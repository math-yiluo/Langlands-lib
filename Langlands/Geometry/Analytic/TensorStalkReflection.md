# Reflection at prime localizations of an algebraic pushout

Consider a pushout square of commutative rings with maps `R → S`,
`R → T`, `S → D` and `T → D`. Assume that `T` is flat over `R` and
`D` is flat over `S`. For a prime `p` of `D`, let `q` be its contraction
to `S`. The theorem `TensorStalkBaseChange.etale_atPrime_reflect`
proves that flatness and formal unramifiedness of `D_p` over `T`
imply the corresponding conditions for `S_q` over `R`.
The four ring universes are independent. No finite-type hypothesis
is needed for this ring-theoretic result.

The canonical local homomorphism `S_q → D_p` is flat by localization
of the supplied flat map `S → D`. Being a homomorphism of local rings,
it is faithfully flat. Flatness of `D_p` over `T` and of `T` over `R`
composes; `flat_of_faithfullyFlat_target` then descends it to `S_q`.

For formal unramifiedness, the module `Ω[D_p/T]` vanishes. The Kähler
module isomorphism for localization identifies this with the scalar
extension of `Ω[D/T]`. The pushout Kähler comparison identifies
`Ω[D/T]` with `D ⊗[S] Ω[S/R]`. Tensor cancellation then identifies
the resulting zero module with `D_p ⊗[S_q] Ω[S_q/R]`, using the
localization comparison for `S → S_q`. Faithful flatness reflects
vanishing, so `Ω[S_q/R]` vanishes.

This is derived from Mathlib's local flatness and faithful-flatness
criteria, the canonical local ring homomorphism, Kähler pushout and
localization equivalences, and tensor cancellation. No general
affinoid-domain flatness or analytic tensor comparison is asserted.
