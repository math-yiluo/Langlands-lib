# Schur orthogonality for essentially square-integrable representations

Worker 89. The theorem
`Langlands.Renard.CompactRepresentation.schurOrthogonality` proves the exact
published proposition `SchurOrthogonalityStatement`, the fourth component of
`UnitarySquareIntegrableStatements`. It includes both integrability conclusions,
the self relation with a positive real formal degree, and vanishing for two
nonisomorphic irreducible representations with the same central character.

Source: Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, IV.3.3 Lemma (i)–(ii), printed pp.101–102 /
PDF pp.107–108; the admissibility and unitarity inputs are IV.3.2, printed
p.100 / PDF p.106. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Hypotheses and reused proofs

The theorem retains the published independent group and carrier universes.
The group is locally compact, Hausdorff and totally disconnected, and the
central quotient carries the supplied Borel Haar measure, also right invariant.
The essential-square-integrability witnesses are exactly smooth open-kernel
twists with unitary central characters and `MemLp` of every smooth coefficient
norm. No countability, admissibility or finite-length hypothesis is added.

The proof uses the already proved
`essentiallySquareIntegrableAdmissible` to obtain admissibility, and
`squareIntegrableUnitarySemisimple` to obtain positive invariant forms on the
square-integrable twists. Van Dantzig gives compact-open cofinality from the
group hypotheses. All existing statement pairs and their dependencies are
preserved.

## Self relation

`schurOrthogonality_self` in the companion `SchurOrthogonalityCore` module
proves this half. It represents the two invariant weak forms by intertwiners,
scalarizes them with admissible Schur, and uses a positive diagonal integral
to obtain a positive real formal degree. Smooth dual twist equivalence
preserves the underlying functionals, and the two factors `ω(g)` and
`ω(g⁻¹)` cancel. This gives the exact formula for every descended function
`F` in the target, together with integrability. The paired core Markdown
details the implemented argument.

## Mixed integrability with independent twists

Let the square-integrable twists be `ρᵢ=πᵢ⊗ωᵢ`, and put `η=ω₂/ω₁`.
`twist_norm_on_center` compares their unitary scalar central actions with
the common original central character `χ`. Irreducibility supplies a
nonzero vector, so scalar cancellation gives

`|ωᵢ(z)| * |χ(z)| = 1`.

Consequently `|η(z)|=1` on the center, and `η` has open kernel.

`integrable_essentiallySquareIntegrable_mixed` transports both functionals to
their twists. `character_norm_bounded_on_coefficient_support`, proved in
`SchurPhaseSupport`, bounds `|η|` by a positive constant `C` on the support
of the first twisted coefficient. The bound follows from local unitary
phase equivalences, a common finite-dimensional fixed coefficient space,
and a finite Vandermonde argument; its paired Markdown gives the details.
This is an internal convergence argument, not an additional premise or a
claim attributed to the source.

Write the second twisted functional as `b₂(z,-)` using the surjective
Hermitian smooth-dual identification. Invariance turns its inverse
coefficient into the conjugate of the forward coefficient
`b₂(x₂,ρ₂(g)z)`. Pointwise, the original product is

`η(g) * ℓ₁(ρ₁(g)x₁) * ℓ₂(ρ₂(g⁻¹)x₂)`.

Its norm is therefore at most `C` times the product of the two forward
coefficient norms on the central quotient. Where the first coefficient is
zero the inequality also holds. Both forward norms are `MemLp` with
exponent two, so Hölder makes this upper bound integrable.
The original integrand is continuous because the original central characters
agree and both representations are smooth. The measurable dominated bound
therefore proves its integrability.

## Mixed vanishing

For fixed first functional and second vector, the now integrable mixed
Schur form gives an actual intertwiner `π₁ → π₂`. Right invariance of the
supplied measure proves its covariance. An equivalence of the underlying
representations would give an isomorphism of the bundled smooth objects;
the target excludes that isomorphism. Irreducibility forces the intertwiner
to be zero. Evaluating it against the second functional gives the required
zero integral. Any `F` satisfying the target's coefficient identity is
pointwise equal to this integrand, so both conclusions transfer to `F`.

The source's proof of (ii) also uses the weak intertwiner. This implementation
supplies the convergence argument for the independently twisted inputs
before forming it. It uses left and right invariance directly, without
assuming inversion invariance of the Haar measure.
