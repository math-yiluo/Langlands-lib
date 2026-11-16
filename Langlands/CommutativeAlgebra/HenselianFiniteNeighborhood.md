# Finite idempotent neighborhoods over a Henselian local ring

This internal construction derives finite idempotent neighborhoods from Mathlib's
étale quasi-finite decomposition and the Library's Henselian section theorem.

`finite_away_of_retract` transports a finite localization of `A ⊗[R] S`
along an algebra retraction `A → R`. The induced map to `S` is surjective,
as is its localized map. Finiteness passes to the quotient and then from
the auxiliary coefficient ring to `R`.

`exists_idempotent_finite_away` applies this transport to the étale
idempotent neighborhood constructed by
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`. The étale
neighborhood has unchanged residue field at the chosen prime, so its
residue point lifts to a retraction by
`HenselianSections.exists_lift_of_etale`. The prime comparison across this
residue-field isomorphism shows that the transported idempotent avoids
the specified prime of `S`.

`finiteNeighborhood` chooses such an idempotent as a subtype carrying its
idempotence, avoidance and finite-localization proofs. It constructs local
algebra data; this module does not yet assert the global scheme finite-part
existence statement.

All rings may have arbitrary characteristic. `R` is a Henselian local
commutative ring in universe `u`, and the finite-type algebra `S` may lie
in another universe `v`. Only quasi-finiteness at the chosen prime above
the closed point is required. No new source assertion is introduced:
the construction composes the named proved decomposition and lifting
results with localization and prime-ideal calculations.
