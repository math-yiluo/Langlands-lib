# Noetherian and DVR reduction for reductive group monomorphisms

Authors: Worker 700 (original proof) and Worker 528 (verification and submission).

`Langlands.GroupScheme.reductiveMonomorphismValuativeReduction.{u}` proves the unchanged
`Langlands.GroupScheme.ReductiveMonomorphismValuativeReductionStatement.{u}` without
additional hypotheses. This module imports that existing theorem from
`MonomorphismValuativeReduction` and retains the additional scheme-level
criteria and base-change lift construction from Worker 700's shared draft for
Task 6383. The duplicate final theorem has been removed without changing its
statement or the supporting constructions.

The supporting implementation first shows that a quasi-compact, locally finite-type scheme
monomorphism to a noetherian affine scheme is closed if every DVR valuative square
lifts. The Library's noetherian DVR criterion gives universal closedness. A monomorphism
is separated, so the morphism is proper and hence a closed immersion. The same
criterion over locally noetherian targets follows by restriction to an affine open cover.

For a homomorphism `f : G → H` over a locally noetherian base, reductivity makes the
structure map of `G` smooth and affine. This implies that `f` is locally of finite
type and quasi-compact, while finite presentation of `H` makes its total scheme
locally noetherian. A valuative square determines a base map `Spec R → S`.
The proof explicitly pulls its two horizontal maps into the base-changed group
schemes over `R`. If the base-changed group homomorphism is a closed immersion,
properness supplies a lift, and its projection gives the original lift. The DVR
assertion applies to this homomorphism because reductivity, separatedness, finite
presentation and quasi-compactness persist under base change, as does monicity.
The generic criterion therefore gives the locally noetherian assertion.

The imported final theorem supplies the equivalence; its converse specializes a locally noetherian base to the spectrum of a
DVR, using that such a ring is noetherian. All arguments are uniform in `u`.

The statement extracts the valuative paragraph of Brian Conrad, *Reductive group
schemes* (2014), Theorem 5.3.5, pp.165–166, registered as
`conrad-2014-reductive-group-schemes` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).
The implementation uses the published
`Langlands.AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_hasLift`,
`IsReductive.baseChange`, and Mathlib's proper-monomorphism criterion.
This is an internal supporting reduction. It proves neither the substantive DVR
case nor descent from an arbitrary base to a noetherian model, and therefore does
not prove the original unrestricted theorem.
