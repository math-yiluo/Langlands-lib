# Conditional assembly of the JPSS two-block extension

`TwoBlockExtensionAssemblyStatement` is an internal derived proposition. Its
premise is row Fourier surjectivity for every p-adic field in the specified
field universe, with its canonical topological data, and every row dimension.
That premise retains all quantifiers in the published surjectivity predicate:
the character, arbitrary scalar additive Haar measure and Schwartz–Bruhat
cutoff are supplied to it.

The conclusion is exactly the unchanged
`TwoBlockWhittakerExtensionStatement`, with independent universes for the two
factor carriers. In particular, it retains the target's literal conjugation
representations on `ULift.{uV₂} V₁` and `ULift.{uV₁} V₂`, its canonical ordered
normalized induction, its actual Whittaker coefficient-image conclusion, its
iterated leading embedding, and its positive determinant half power. No
irreducibility or additional ambient Whittaker functional is assumed.

The derived rationale is the scalar pure-tensor cell coefficient formula,
followed by the published conditional matrix Fourier slice. A nonzero first
factor functional can be normalized to value one because the first factor is
of Whittaker type. The second coefficient already has a functional and vector
by its intrinsic Whittaker-set membership. Transporting those functionals and
vectors through the literal carrier lifts puts both factors in a common
universe. The Fourier slice provides the required rectangular test function.
The positive induction half modulus times its determinant Jacobian is the
displayed positive half power. Entrywise comparison identifies the two
leading embeddings. These are internal consequences of the named Library
interfaces, rather than an additional claim extracted from the original
literature.

This file defines a conditional proposition; it proves neither row Fourier
surjectivity nor the unconditional extension. The implication is proved by
`Langlands.Whittaker.twoBlockWhittakerExtension_of_rowFourierSurjectivity`
in the companion module
`Langlands.Representation.Whittaker.TwoBlockExtensionAssemblyProof`.

The premise family is proved separately. The published theorem
`Langlands.HarmonicAnalysis.padicRowFourierSurjectivity`, of
`Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityProof`, proves
`PadicRowFourierSurjectivityStatement F T d` for every p-adic field `F`,
every topological data `T` and every row dimension `d`. In particular it
covers `F.canonicalTopologicalData`, with every character, scalar Haar
measure and cutoff. The separate published theorem
`Langlands.Whittaker.twoBlockWhittakerExtension`, of
`Langlands.Representation.Whittaker.TwoBlockExtensionProof`, applies this
implication to that theorem. It proves the unconditional parent target
`TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂}`. Neither theorem changes
this proposition, whose row-surjectivity premise remains explicit.
