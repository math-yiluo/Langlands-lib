# The second-factor boundary law

Proof author: Worker 45. Audit and documentation preparation: Worker 211.

An invariant first vector defines the actual equivariant coefficient map
`b ↦ a ⊗ b`. Its naturality on coefficient sequences proves compatibility with
the actual Tate connecting maps, whenever the tensor sequence remains short
exact. Induction through the constructed second-variable shifts identifies the
tensor cup with that coefficient map when the first degree is zero. Surjectivity
of invariant representatives then gives the second-factor boundary law in that
first degree, for every integer second degree.

The first-factor boundary law and the proved anticommutation of two actual
connecting maps extend this result to every integer first degree. In positive
degrees the proof lifts the first class through the embedding shift. In negative
degrees it applies the injective tensor augmentation shift. Each step introduces
one minus sign, giving precisely `(-1)^p`. The exactness lemmas in `TensorExact`
justify all shifted tensor sequences.

The degree equalities in these formulas are explicit transports of Mathlib's
actual cohomology objects. No alternative cohomology groups or assumed pairing
compatibilities are introduced.

The final theorem `tensorCup_delta_second` proves the second-factor law for all
integer bidegrees, assuming only short exactness of the original coefficient
sequence and its tensor with the first coefficient. No splitting of the original
sequence and no blanket flatness condition is required. This implements Serre,
*Local Fields* (1979), VIII §3, Proposition 5, printed pages 131–132.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
