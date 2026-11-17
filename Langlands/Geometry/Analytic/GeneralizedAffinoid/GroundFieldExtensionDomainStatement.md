# Ground field extension preserves affinoid domains

`Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension.DomainPreservationStatement`
is the following proposition, universe-polymorphic in the universes `u` of
`K` and `v` of `L`.

Let `K` be a complete ultrametric normed field and let `L` be a complete
ultrametric normed field with `NormedAlgebra K L`. Let `A` and `B` be
presented `K`-affinoid algebras, let `i : A → B` be a bounded `K`-algebra
map, and let `V` be a set of points of the spectrum of `A`. Suppose
`Represents K i V`. Then

`Represents L (map K L i) (spectrumProjection K L A ⁻¹' V)`.

Here `map K L i : A_L → B_L` is the ground field extension of `i` from
`GroundFieldExtension`, and `spectrumProjection K L A` is the projection from
the spectrum of `A_L` to the spectrum of `A`.

## Meaning

`Represents K i V` is the Library's notion of an affinoid domain
representation (`GeneralizedAffinoid/Domain`). It has three clauses:

1. `V` is closed;
2. the spectrum map of `i` has image exactly `V`;
3. the restriction universal property: for every presented `K`-affinoid
   algebra `R` and every bounded `K`-algebra map `φ : A → R` whose spectrum
   map lands in `V`, there is a unique bounded `K`-algebra map `ψ : B → R`
   with `ψ ∘ i = φ`.

The third clause is the factorization property used by
`IndexedAffinoidAtlas.restriction_universal`. The spectrum map of a
representing map is a closed embedding, by the Library theorem
`Domain.spectrumEmbedding`. So the hypothesis says that `i` embeds the
spectrum of `B` onto `V` and has the restriction universal property against
presented `K`-affinoid algebras. The conclusion says the same for `i_L`, with
`V` replaced by its preimage `π⁻¹(V)` under `π = spectrumProjection K L A`.
The test algebras in the conclusion range over all presented `L`-affinoid
algebras, of every arity and radius, with no strictness condition.

## Scope

The degree and transcendence degree of `L/K` are arbitrary. The valuations of
`K` and `L` may be trivial, and no presentation is assumed strict. Zero
algebras and empty sets `V` are included.

## Provenance

Berkovich (*Spectral theory and analytic geometry over non-Archimedean
fields*, AMS 1990) defines affinoid domains by the universal property in
Definition 2.2.1 (printed p. 27, PDF p. 41). The proof of Proposition 2.2.4
(printed p. 29, PDF p. 43) passes to a ground field extension `X ⊗̂ K` and
uses that `π⁻¹(V)` is an affinoid domain represented by
`𝒜 ⊗̂ K → 𝒜_V ⊗̂ K`, where `π : X ⊗̂ K → X` is the canonical projection. This
statement is that assertion for the Library's presented affinoid algebras. It
uses the presented ground field extension of `GroundFieldExtension`, which
`GroundFieldExtensionTensor.tensorEquiv` identifies with the completed tensor
product. The proof is not provided here. In the source it rests on the
Gerritzen–Grauert theorem and Tate acyclicity, as in the proof of
Proposition 2.2.3.
