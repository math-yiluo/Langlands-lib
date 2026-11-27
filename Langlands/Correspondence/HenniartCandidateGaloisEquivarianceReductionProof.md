# Galois equivariance of Henniart's candidate

`Langlands.Henniart.candidateGaloisEquivarianceReduction` has type
`CandidateGaloisEquivarianceReductionStatement.{uK, uW, uV}` at independent field,
Weil representation and supercuspidal representation universes. It gives (CI2)
for `Extension.rankExtension` in every rank with `StableExistsAt` over the top
field of a cyclic prime-degree step, under `CandidateExistenceStatement`.

Fix a step `M/L` and `w ∈ W_L`. Write `g` for its image in `Gal(M/L)` and `c`
for `finiteGaloisWeilConjugation`, the automorphism of `W_M` defined by
conjugation by `w`. The lattice transport uses the chosen Weil map `φ` of the
inverse field automorphism `g⁻¹` (the map of Weil groups is contravariant).
Its action on the stable Weil generator agrees with the pullback along `c`.
Indeed, let `λ` be the chosen lift of `g⁻¹` to the closure of `M`, and `θ` the
lift of `g` given by `closureConjugation`. Then `κ = θ ∘ λ` fixes `M` and is an
absolute Galois element. The two closure projection formulas give
`κ · pr(φ y) = pr(c y) · κ` for each `y ∈ W_M`. If the generator factors
through `q` with representation `R`, the invertible operator `R(q(κ))`
intertwines the two restrictions. This proves equality of the unitary basis
classes. The supercuspidal pullback uses `g` on matrix entries, as in
`CyclicPrimeStep.galoisConjugate`.

Take a stable decomposition of `τ` from `Extension.rankExtensionBasis_spec`.
`IsStableImage.fieldPullback` transports its stable image using the given
rank-stability hypothesis. Pullback along `c` commutes with the Weil twist
because `localDegree_finiteGaloisWeilConjugation` preserves the degree. On the
supercuspidal side the determinant of the entrywise pullback is transported by
`g`, and `PadicField.CanonicalTransport.ord_map` preserves its order, so the same
unramified twist parameter works. These facts give a stable decomposition of
`weilConjugate S w τ`. `Extension.rankExtensionBasis_eq` computes the rank
extension from it, using unramified-twist independence obtained from candidate
existence and `LocalClassField.commonClosureReciprocityExistence`. Finally,
`Extension.sigma_rankExtension` identifies the rank-tagged class with the
corresponding class in the specified rank.

The lattice clauses and the extension by unramified twists come from Henniart
(2000), §§3.8 and 4.1–4.4, pp. 451–453, literature ID
`henniart-2000-simple-proof`, retained PDF SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The (CI2) identity is recorded in *The numerical local Langlands correspondence
for GL_n: counts on the two sides and the recommended route of proof*, §6.5,
`numerical-LLC-route.tex`, lines 1153–1157, literature ID
`operator-numerical-llc-route-2026-11-16`, source file SHA-256
`b57ba9428a0d664d0c6beed75bbc2a2d0d73638718a8080c2f913b75acbbb3c8`.
