# Complete-local lifting with an arbitrary field quotient

This internal transport lemma keeps the complete-local
deformation proposition as an explicit input.

For a complete Noetherian local ring `B`, let `B → K` be a supplied
surjective map to a field. Let `C` be a group split over a finite etale
surjective cover, and let `D` be an affine flat finite-type group whose
base change to `K` is of relative multiplicative type. The theorem
`exists_lift_of_field_quotient` lifts any prescribed homomorphism over
`K` to an actual homomorphism over `B`, with exact recovery along
`Spec.algebraMap B K`.

The supplied quotient identifies `K` with the canonical residue field.
The proof transports the fibre and its homomorphism across that actual
isomorphism, applies the input complete-local deformation proposition,
and transports the recovery equation back using functorial evaluation.
The lemma does not prove that deformation proposition.

`exists_completed_lift` specializes this transport to a Noetherian local
ring `P` and its maximal-ideal completion `B`. A diagonalizable source and
a multiplicative-type special target suffice for the input deformation
proposition. The reduction `B → P / m_P` is the actual evaluation map of
the completion. Canonical comparison isomorphisms transport the prescribed
map into this quotient fibre and transport the recovered equation back.
The result is a completed homomorphism whose evaluation at the original
residue field is exactly the prescribed map. No Henselianity of `P` is
required.

Finally `exists_etale_lift` composes the completion construction with
`Descent.EtaleHomApproximation.exists_approximation`. Under the explicit
etale approximation hypothesis on `P`, it produces an etale algebra and
an actual homomorphism whose induced residue-field evaluation is the
prescribed map. This last result requires the source to be quasi-compact
and quasi-separated and the target to be locally finitely presented.
Clopen immersion conclusions still require a separate local argument.
