# Local-field affine boundedness and compactness

`localFieldAffineBoundedCompactness_proof` proves the exact published target
`LocalFieldAffineBoundedCompactnessProperty F` at arbitrary universe `u`.
For every nonarchimedean local field `F`, every affine finite-type `F`-scheme
`X`, and every closed subset `B` of its actual identity-test rational points,
algebraic boundedness is equivalent to compactness in precisely
`rationalPointTopology F X`.

This is the local-field case of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Fact 2.2.3, printed page 70 / PDF page 101, with boundedness
and topology as in Definition 2.2.1 and Remark 2.2.2. The registered original
source is `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The mandatory corrections `kaletha-prasad-2024-corrections`,
1 November 2024, PDF page 24, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
add Henselianity throughout Section 2.2. The implemented proof directly uses
Mathlib's compact valuative balls for nonarchimedean local fields. It neither
assumes nor needs to invoke the separate general Henselian-field comparison.

The internal scalar helper `IsCompact.exists_valuative_bound` first proves
that every compact subset of a field with its valuation topology has a
nonzero uniform valuative upper bound. Nonzero valuative closed balls are
open and cover the field, including zero. Compactness gives a finite
subcover. The maximum of the finitely many radii and 1 is nonzero, and the
surjectivity of the canonical valuation represents this radius by a nonzero
scalar. This direction needs only compatibility with the valuation topology
and also covers a trivial valuation.

For the forward implication of the affine theorem, finite type of the actual
global-section algebra gives a surjective algebra homomorphism from a
polynomial ring in `Fin n` variables. Precomposition is a closed embedding on
algebra points over the Hausdorff local field. The polynomial-point
homeomorphism then embeds them into `Fin n → F`. Composing with the published
rational-point and affine-scheme-point homeomorphisms gives a closed
embedding of the actual rational points with the specified topology.
Algebraic boundedness supplies a separate scalar bound for each of the
finitely many coordinate functions. The product of these compact valuative
balls is compact. Its preimage under the closed embedding is compact and
contains `B`; closedness of `B` proves its compactness.

For the reverse implication, each actual global regular function is
continuous, by the same two point homeomorphisms and the published
`AlgPoint.continuous_eval`. Its image of a compact set is compact. Applying
the scalar helper supplies the nonzero bound required by
`IsAlgebraicallyBounded` for that function.

No topology is replaced: the proof installs exactly the named topology in
the target. There is no reducedness, smoothness, characteristic, or nonempty
coordinate assumption. In particular `n = 0` is included. The theorem proves
only the local-field comparison, leaving the separate general Henselian
comparison and the chamber compact-openness conclusion to their own proofs.
