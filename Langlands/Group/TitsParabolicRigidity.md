# Conjugacy rigidity in a Tits system

This is an internal derivation from the published `IsTitsSystem` axioms and
their Bruhat-cell consequences. It works with arbitrary groups `G` and `W`,
with no finiteness assumption.
The reduced-cell construction also occurs in the published proof of
`IsTitsSystem.mem_closure_of_mem`; here the new induction uses membership
in a conjugate overgroup to shorten a transporter representative.
The existing `normalizer_eq_of_le` assumes an element preserves `P` and
concludes that it belongs to `P`. The new transporter theorem requires only
`g⁻¹ B g ≤ P`, so it is a stronger statement.
The existing `exists_eq_standardParabolic` identifies the overgroups of `B`
as unions of Bruhat cells; it does not assert the transporter condition or
rigidity of conjugate overgroups. These results are related and remain
independently useful.

`rep_mem_of_conjugate_le` proves that if `B ≤ P` and a representative `n ∈ N`
satisfies `n⁻¹ B n ≤ P`, then `n ∈ P`.

The proof inducts on the published word length of `π n`. If that image is the
identity, the kernel condition puts `n` in `B`. Otherwise take a left descent
`s` and representatives `ns` and `nv` of `s` and `s * π n`. Every element `x`
of the original Bruhat cell has `n⁻¹ x ∈ P`. The reduced-length multiplication
rule puts `ns * b * nv` and `ns * nv` in that cell for `b ∈ B`. Their ratio
therefore belongs to the conjugate overgroup `Q = n P n⁻¹`.

Choose `b` by the Tits nondegeneracy axiom. Its ratio
`ns * b * ns⁻¹` lies in the simple cell, so the published cell-representative
lemma places `ns` in `Q`. Thus `p = n⁻¹ * ns * n ∈ P`. Conjugating the original
containment by this member of `P` supplies the induction hypothesis for
`ns⁻¹ * n`, whose length is smaller. Finally
`(ns⁻¹ * n) * p = n` proves the claim.

`mem_of_conjugate_le` extends this result to every `g ∈ G`. Bruhat
decomposition writes `g = b₁ * n * b₂`. Apply the given containment to
`b₁ * b * b₁⁻¹`, then conjugate the resulting member of `P` by `b₂ ∈ P`.
This gives `n⁻¹ * b * n ∈ P`. The representative result puts `n` in `P`;
the two outer factors also belong to `P`, proving `g ∈ P`.

`parabolicTransporterEquiv` packages that result as an equivalence from
`{g : G // ∀ b ∈ B, g⁻¹ * b * g ∈ P}` to the actual subgroup `P`.
Both directions preserve the underlying element of `G`. The inverse uses
closure of `P` under multiplication and inversion, together with `B ≤ P`.

`eq_of_conjugate_of_le` proves the desired rigidity: if `P` and `Q` both
contain `B` and
`Q = P.comap (MulAut.conj g⁻¹).toMonoidHom`, then `P = Q`.
The equality expresses `Q = g P g⁻¹`; its containment of `B` gives the
transporter hypothesis for `g`, so the preceding theorem yields `g ∈ P`.
Conjugation by a member of a subgroup preserves that subgroup, and an explicit
membership calculation proves the equality.

This abstract result does not establish a Tits-system realization for an
actual reductive group. It also does not identify rational-point subgroups
with all-test subgroup functors.
