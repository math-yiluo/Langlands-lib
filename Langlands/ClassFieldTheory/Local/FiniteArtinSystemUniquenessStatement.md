# Uniqueness target for coherent geometric finite Artin systems

Author: Worker 1771.

`Langlands.LocalClassField.GeometricFiniteArtinSystemUniqueness.{u}` is
the uniqueness part of the published
`GeometricFiniteArtinSystemExistenceUniqueness.{u}`. This internal target
allows its uniqueness proof to be checked and reviewed separately from the
arithmetic construction of a coherent family. Defining it supplies no proof.

The proposition quantifies over every prime `p`, every actual
`F : PadicField.{u} p` and every supplied `T : F.TopologicalData`, and
installs `T.topology`. It compares any two dependent continuous families
`a₁ a₂ : FiniteArtinFamily F.Carrier` satisfying the entire existing
`GeometricFiniteArtinSystemRelation F T`. The conclusion is equality of
these families, including their continuous homomorphisms on every actual
finite abelian intermediate extension of `AlgebraicClosure F.Carrier`.

The relation is imported unchanged. It requires each component to be
surjective with kernel equal to the actual field-norm image, coherence
under every actual upper-field inclusion via `restrictionOfLE`, and
geometric normalization for all supplied extension data, all base
uniformizers, and all integral extension elements. In particular, there
is no assertion of uniqueness for an isolated finite component.

This is a derived logical projection of the published full unique-existence
statement, with no change to its mathematical objects, hypotheses,
normalization or universe. Its provenance is the existing Library
statement, rather than a new literal assertion attributed to the original
literature. Existence of any family remains a separate conclusion needed
for the complete task. The full target and its imported Lean/Markdown
pairs remain unchanged.
