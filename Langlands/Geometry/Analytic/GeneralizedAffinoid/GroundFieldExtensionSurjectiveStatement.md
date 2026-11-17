# Surjectivity of the spectrum projection of a ground field extension

`Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension.SpectrumProjectionSurjectiveStatement`
is the following proposition, universe-polymorphic in the universes `u` of
`K` and `v` of `L`.

Let `K` be a complete ultrametric normed field and let `L` be a complete
ultrametric normed field with `NormedAlgebra K L`. For every presented
`K`-affinoid algebra `A`, the map

`spectrumProjection K L A : BanachSpectrum (algebra K L A) → BanachSpectrum A`

is surjective. Here `algebra K L A` is the ground field extension `A_L` of
`GroundFieldExtension`, and the projection restricts a bounded multiplicative
seminorm on `A_L` along the structural map `ι : A → A_L`. Thus every bounded
multiplicative seminorm `x` on `A` has the form `a ↦ y (ι a)` for some bounded
multiplicative seminorm `y` on `A_L`.

## Scope

There is no restriction on the degree or transcendence degree of `L/K`. The
valuations of `K` and `L` may be trivial, and the presentation of `A` need not
be strict. The statement includes the zero algebra, whose spectrum is empty, and
arity zero.

## Provenance

Berkovich (*Spectral theory and analytic geometry over non-Archimedean
fields*, AMS 1990) uses this fact in the proofs of Propositions 2.2.3(ii) and
2.2.4 (printed p. 29, PDF p. 43). There `π : X ⊗̂ K → X` is called "the
canonical surjective map", and the proofs use that `𝓜(𝒜_V ⊗̂ K) → 𝓜(𝒜_V)` is
surjective. The source states the fact for the completed tensor product
`𝒜 ⊗̂_k K`. This statement uses the presented algebra `A_L`, which
`GroundFieldExtensionTensor.tensorEquiv` identifies with
`CompletedTensorAlgebra.Algebra K A L` by a bounded `K`-algebra equivalence
that sends the first leg to `ι` (`tensorEquiv_leftMap`). Hence restricting
seminorms along `ι` corresponds to restricting them along the first leg of the
completed tensor product.

A standard proof goes as follows. Realize a point `x` of `𝓜(A)` by a
bounded map `A → 𝓗(x)` to a complete field. Amalgamate `𝓗(x)` and `L` over
`K` isometrically in a complete ultrametric field `Ω`. Then apply the
universal property of `A_L` to `A → 𝓗(x) → Ω`. The norm of `Ω` pulled back
along the resulting `L`-algebra map `A_L → Ω` restricts to `x`. The Library
has the needed ingredients `pointAmalgamation` and
`completeFieldAmalgamation`. They are stated in a single universe, so a proof
for different universes of `K` and `L` must transport between universes. This
paragraph is a guide only; the statement prescribes no proof route.
