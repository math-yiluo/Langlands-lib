# Real-radius binary Laurent splits of full domains are split squares

`Langlands.Analytic.PresentedAffinoidAlgebra.DomainBinaryLaurentSplitSquareStatement`
is an unproved proposition definition. It is an intermediate statement for the
proof of `FiniteAffinoidAlgebraDescentStatement`, not an axiom.

## Statement

Fix a complete ultrametric normed field `K` (trivial valuations allowed), an
actual presented positive-polyradius affinoid algebra `R`, a full domain `U`
of `R` (`Domain K R`), an element `a` of the domain algebra `U.algebra`, and an
arbitrary real radius `ρ > 0` (not required to lie in the value group of `K`).
Write `{|a| ≤ ρ}` for the image under `U.spectrumMap` of the set of points `y`
of the bounded multiplicative spectrum of `U.algebra` with `y a ≤ ρ`, and
similarly for `{|a| ≥ ρ}`; these are subsets of the spectrum of `R`.

The statement is the conjunction of:

1. **Existence.** There are full domains `U₁` and `U₂` of `R` whose loci are
   exactly `{|a| ≤ ρ}` and `{|a| ≥ ρ}`.
2. **Split square.** For all full domains `U₁`, `U₂`, `W` of `R` with
   `U₁.locus = {|a| ≤ ρ}`, `U₂.locus = {|a| ≥ ρ}` and
   `W.locus = U₁.locus ∩ U₂.locus` (with the evident containments
   `U₁, U₂ ⊆ U` and `W ⊆ U₁, U₂` supplied as hypotheses), the four original
   bounded restrictions `restriction : U.algebra → U₁.algebra`,
   `U.algebra → U₂.algebra`, `U₁.algebra → W.algebra`, `U₂.algebra → W.algebra`
   (the unique ones of `FiniteAffinoidAlgebraDescent.restriction`) form a
   `BoundedAlgHom.SplitSquare`: the square commutes, compatible pairs on `U₁`
   and `U₂` glue to an element of `U.algebra`, the restriction from `U₂` to
   `W` has dense range, and every element of `W.algebra` is a sum of
   restrictions from `U₁` and `U₂` with norms bounded by a fixed constant
   times its norm.

Only `Nonempty` of the split-square structure is asserted.

## Provenance

The domains `{|a| ≤ ρ}` and `{|a| ≥ ρ}` are the Laurent domains of Berkovich,
*Spectral theory and analytic geometry over non-Archimedean fields* (1990),
2.2.2(i), printed p.27 / PDF p.41 (registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`),
with arbitrary positive real radii; by 2.2.2(iii)–(iv) of the same source,
domains of domains are domains. Gluing of compatible pairs on the binary cover
is the case of a two-member cover of the Acyclicity Theorem, Proposition 2.2.5,
printed p.30 / PDF p.44 of the same source. The bounded splitting of the
annulus algebra into its nonnegative and negative Laurent parts and the
density of the restriction from `{|a| ≥ ρ}` to the Weierstrass subdomain
`{|a| = ρ}` are the standard ingredients of the Laurent-cover step in the
proofs of Tate's acyclicity theorem and Kiehl's theorem; Kiehl's theorem in
this non-strict generality is cited in Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Kiehl's Theorem and Remark 1.2.1(ii),
printed p.15 / PDF p.12 (registered source `berkovich-1993-etale-cohomology`).

The Library already proves the radius-one analogue for the abstract binary
Laurent diagram over any presented affinoid algebra (`BinaryLaurentIdealDescent`:
splitting with constant 2 and density, and `splitSquare` given gluing). The
present statement is the derived internal formulation for actual full domains
and arbitrary real radii, chosen so that it applies to every member of an
iterated binary Laurent refinement (see
`FiniteCoverBinaryLaurentInductionStatement`) together with
`SplitSquareModuleGenerationStatement`.
