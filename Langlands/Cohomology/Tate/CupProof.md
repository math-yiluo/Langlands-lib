# Normalization and naturality of the dimension-shifted product

Proof author: Worker 45. Audit and documentation preparation: Worker 211.

At degrees `(0,0)`, the recursively constructed tensor family reduces to
the normalized quotient product. Functoriality of the actual degree-zero
class map proves that composing the tensor pairing with an equivariant
coefficient pairing recovers exactly `cupZero`. In particular, products
of invariant representatives are represented by their coefficient pairing.

Naturality in both coefficients is proved by induction in both
directions on the first degree, then in both directions on the second.
The base is the proved degree-zero naturality. The induction steps use
the actual tensor connecting-map naturality and coefficient-shift
naturality, including their inverse forms and integer-degree transports.
Integer scalar multiplication commutes with the coefficient maps.
The general pairing-valued naturality theorem then follows from the
equivariant tensor morphism and functoriality of actual Tate cohomology.

The file also proves the recursive shift certificates: the first-factor
boundary with second degree zero has positive sign, and both directions
of the chosen second-factor shift have sign `(-1)^p`. The inverse
second-factor formula uses the proved identity that this integer unit
squares to one. These certificates concern the actual selected shift
sequences. The general tensor-exact boundary formulas are proved in the
separate `CupBoundary` and `CupBoundarySecond` modules.

These are proofs about the constructed maps, not hypotheses defining
them. `CupLawsProof` assembles the exact published cup-law target from these
lemmas and the boundary and subgroup compatibility modules.
`CupDefinitions` and `ZeroProof` are unchanged published dependencies;
`TensorNaturality` supplies the tensor shift naturality lemmas. The
comparison with ordinary cochain cup products is a separate result, not proved
in this file. It is the published statement `OrdinaryTateCupLaws`, proved as
`ordinaryTateCupLaws` (through the lemma `ordinaryToTate_cup`) in
[OrdinaryTateCupProof](OrdinaryTateCupProof.md). It covers every commutative
coefficient ring, finite group and equivariant pairing, and all natural
bidegrees `(p, q)` including zero, with no flatness hypothesis. In degree zero
the comparison map `ordinaryToTate` is the quotient map from invariants to
`Ĥ⁰`, not an isomorphism. Negative ordinary degrees are not asserted.

The normalization and naturality statements are from Serre, *Local
Fields* (1979), Chapter VIII, section 3, Proposition 5(i–ii),
printed p. 131 (PDF p. 137). Source ID `serre-1979-local-fields`;
retained PDF SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
