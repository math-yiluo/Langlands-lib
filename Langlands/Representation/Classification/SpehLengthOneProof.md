# Length-one Speh comparison

Author: Worker 1431.

`spehLengthOneComparison` proves exactly
`Langlands.Classification.SpehLengthOneComparison.{uF,uV} F T`.
It works for every prime, finite p-adic field and compatible topology, with
independent field and representation universes. The supplied datum has an
actual irreducible unitarizable analytically square-integrable representation
`delta`, positive rank and length, and the hypotheses `length = 1` and
`h : degree = rank`. For every actual smooth candidate `pi`, the conclusion is
`d.IsSpeh pi` if and only if `Nonempty ((h ▸ pi) ≅ d.delta)`.

The auxiliary construction `SpehDatum.centeredInducedLengthOneIso` gives an
actual isomorphism from the centered decreasing induction to `h.symm ▸ delta`.
The existing single-block normalized-product evaluation equivalence removes
the one-block induction. Its only real exponent is zero; `realPowerTwist_zero`
removes the determinant twist. The existing `castRankEquiv` then supplies the
stated group-rank transport. The construction retains the original smooth
actions and upper normalized-induction convention.

The private quotient lemma proves that a surjective intertwiner from an
irreducible smooth representation to an irreducible smooth representation is
bijective. The target is nontrivial by simplicity of its monoid-algebra module.
Surjectivity therefore makes the map nonzero, and irreducibility of the source
makes it injective. `SmoothRep.mkIso` turns the resulting equivariant linear
equivalence into an actual categorical isomorphism.

The source of the length-one centered induction is irreducible because it is
isomorphic to the given irreducible `delta`. In the forward direction, apply
the quotient lemma to the quotient map from `d.IsSpeh pi` and compose with the
single-block comparison. In the reverse direction, compose a supplied
isomorphism with the single-block comparison to obtain the required surjective
intertwiner and transfer irreducibility to `pi`. Apply the same quotient lemma
to every other irreducible quotient to establish the full isomorphism-class
uniqueness clause in `IsSpeh`. A private equality-transport lemma moves the rank
cast between the source and target of the displayed isomorphism.

This is an elementary derivation from the actual Speh definition. It assumes
no Speh existence theorem for arbitrary length and no unitary classification
result. Unitarizability and analytic square-integrability are retained in the
exact target and carried into `IsSpeh`; the argument only uses the
irreducibility component of the discrete-series hypothesis. The full unitary
generic exhaustion theorem and Speh existence for larger lengths remain open.

The source convention is Tadic, *Classification of unitary representations in
irreducible representations of general linear group (non-archimedean case)*,
1986, printed p.338 and section 7.4, p.370: the Speh class is the unique
irreducible quotient of the centered decreasing product. Taking length one
makes that product the original square-integrable block. The length-one
comparison is a derived consequence, not a separate numbered source theorem.
The retained source is registered as `tadic-1986-unitary`, SHA-256
`08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683`;
its retained PDF pages 5 and 37 were read for this comparison.
