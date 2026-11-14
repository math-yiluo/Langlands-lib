# Finite-field quotient data for a semilinear chamber orbit

This internal interface records the geometric inputs needed to apply Lang's theorem
to chambers through a specified building point. It does not construct those inputs.

Let `B` be integer-valuation building data for `G` over a field `k`. Let `κ` be a
finite field and `Ω/κ` an algebraic field extension. Supply maps `θ : G(k) → G(k)`
and `τ` on the reduced building, and a point `y`.

`B.HasFiniteFieldChamberQuotient κ Ω θ τ y` asserts the existence of:

- a connected reductive group scheme `R` over `κ`;
- a subgroup `P` of the actual group `G(k)` fixing `y`;
- a surjective group homomorphism from `P` onto the actual `Ω`-points of `R_Ω`;
- a map `θP : P → P` whose underlying map is the restriction of `θ`, with reduction
  intertwining `θP` and the canonical descent action of the cardinality-of-`κ`
  Frobenius;
- an initial chamber `Y₀`, with the explicit translated generic facet and closure
  presentation through `y`, such that the kernel fixes `Y₀` setwise and `τ(Y₀)` is
  an explicitly supplied `P`-translate of `Y₀`.

The geometric points are the identity-test morphisms to the actual base-changed
group scheme. Neither the quotient group nor its Frobenius is an arbitrary
abstract substitute. The definition does not identify `P` as a parahoric or `R`
as a special-fibre reductive quotient. Such an identification, when used to
construct these witnesses, is a separate geometric obligation. It does not assume
that `Y₀` is stable under `τ`.

If `Ω` is algebraically closed and
`τ(g • z) = θ(g) • τ(z)`, the supporting theorem
`HasFiniteFieldChamberQuotient.exists_stable_chamber` produces a `τ`-stable chamber
with an explicit closure presentation through the same point `y`.

The proof equips `R` with its smooth, affine and connected instances, applies
`langSurjective_descentBasePoint` to its actual geometric points, and then applies
`exists_stable_chamber_of_quotient_lang`. The restriction identity for `θP` supplies
the required semilinearity. The subgroup fixing `y` ensures that translating
`Y₀` preserves the specified closure point.

This definition and implication are an internal assembly of the two preceding
Lang correction modules. They restate no numbered source theorem and make no
unconditional assertion about unramified buildings.
