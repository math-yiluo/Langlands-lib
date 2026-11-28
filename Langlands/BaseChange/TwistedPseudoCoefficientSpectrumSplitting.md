# Splitting of the twisted irreducible spectrum at a σ-discrete orbit

`twistedPseudoCoefficientSpectrumSplitting` proves
`TwistedPseudoCoefficientSpectrumSplittingStatement`, stated in
`Langlands.BaseChange.TwistedPseudoCoefficientOrbitSeparation`. The three
universes `u`, `v` and `z` stay free.

Let `E` be a cyclic extension of a characteristic-zero nonarchimedean
local field `F` with its supplied `F`-module topology. Let `σ` generate
the cyclic group, let `2 ≤ n` (the hypothesis of the statement), let `τ`
satisfy `IsSigmaDiscreteSeries σ n τ` on a carrier in universe `z`, and let
`μ` be a Haar measure on `GL_n(E)`.
Then there is one compact open subgroup `J` with two properties:

- the orbit span `twistedOrbitSpan` is disjoint from the whole
  complementary sum `twistedPseudoCoefficientComplementSpan σ μ τ J`;
- every irreducible admissible twisted distribution, in
  `twistedSpectrumSpan`, lies in the sum of the two.

The complementary sum consists of the other essentially tempered span,
the span of all proper σ-inductions of irreducible admissible σ-stable
inducing pairs (tempered or not), and the `J`-invisible span.

## Proof

As in `twistedPseudoCoefficientSpanning`, the field `E` is realized as a
`p`-adic field by `CharZeroLocalField.topologicalData E`, keeping its
original module topology. Of the hypothesis `2 ≤ n` the proof uses only
the consequence `0 < n`, which is what the separation and spanning
results below assume.

- Disjointness is `exists_compact_disjoint_twistedOrbitSpan_complement_padic`.
  It combines the triangular separation of the orbit from the other
  essentially tempered and proper-induction spans
  (`disjoint_twistedOrbitSpan_otherTempered_sup_properInduced`) with
  selection by the unramified twist class of the supercuspidal support
  of `τ`. That selection fixes the level `J`.
- Spanning is `twistedPseudoCoefficientSpanning`: the irreducible
  twisted distributions lie in the sum of the orbit span, the other
  essentially tempered span and the proper-induction span. These three
  spans are contained in the orbit span plus the complementary span.

In Henniart–Lemaire (2011), II.5.13, pp. 113–114, pseudo-coefficients
of σ-discrete series come from the twisted Paley–Wiener theorem (II.5.7,
p. 105). It is applied to an element `Φ` of `𝒢^{*}_0(G(E),σ)`: a
ℤ-linear form on `𝒢_0(G(E),σ)` with `Φ(Π, λA) = λ Φ(Π, A)`. `Φ` factors
through the quotient `Ḡ(G(E),σ) = 𝒢(G(E),σ) / 𝒢_{0+}(G(E),σ)` of the
twisted Grothendieck group (II.5.4, p. 103), through which twisted
traces also factor. `Φ` is a regular function on the unramified twists
of the given representation, zero on the other essentially tempered
classes, and zero on the induced part. Extension by zero uses the direct
sum of II.5.11, Lemme 2, pp. 111–112. The conditions of II.5.7 are then
checked: (i) through the Bernstein component of the representation, and
(ii) through II.5.12, Lemme 2, and the two cases of p. 114. The theorem
here is a statement about spans of twisted distributions on `GL_n(E)`
at one compact open level `J`. It is not a statement about Grothendieck
groups, and its proof does not use them.
