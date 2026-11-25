# Correcting a crossed homomorphism into a closed additive subgroup over any field

Module
`Langlands.GroupScheme.Trigonalizable.CorrectionOfSolvable`, namespace
`Langlands.GroupScheme.LinearAdditiveExtension`.

The Library's `LinearAdditiveExtension.exists_corrected` (the correction step
in the proof of Milne 15.34(d)) assumes an algebraically closed field only to
find a root `r₀ ∈ k` of `f - μ`, where `f` is the closed polynomial of the
kernel and `μ ∈ k` the constant obtained by averaging. This module proves the
same conclusion over any field under an explicit solvability hypothesis.

## Declaration

`exists_corrected_of_solvable` has the setting and hypotheses of
`exists_corrected` (an extension `q : E ⟶ D(Λ)`, flat, surjective and
quasi-compact, a closed embedding `a` of its kernel into `𝔾ₐ`, a character
`χ`, an action `b` with the linearity law `hlin`, a crossed homomorphism `c'`
with `hc₁` and `hc₂`), without `[IsAlgClosed k]`, and with

`hsolv : closedPolynomial a ≠ 0 →
  (∀ m : k, ∃ r : k, (closedPolynomial a).eval r = m) ∨
  ∀ T d, VectorGroup.charValue χ T d ^ (closedPolynomial a).natDegree = 1`.

Its conclusion is that of `exists_corrected`: a crossed homomorphism `c''` with
the same two identities and all values in the range of `a`.

## Proof

The proof is the Library's proof of `exists_corrected`, unchanged up to the
averaging step that produces the constant `μ` with
`μ = hD(z) + χ(z)^N μ`. Then:

- if every constant is a value of `f`, take `r₀` with `f(r₀) = μ` and finish
  exactly as in the Library proof with `c'' = c' + r₀ (χ ∘ q - 1)`;
- if `χ(z)^N = 1` for all points, the averaging identity gives `hD = 0`, so
  `f ∘ c' = hD ∘ q = 0` and `c'' = c'` already has values in the range of `a`.

The case `closedPolynomial a = 0` is treated as in the Library proof.

## Provenance

Internal generalization of the published Library proof
(`Langlands/GroupScheme/LinearAdditiveExtension/Correction.lean`), which
follows Milne, *Algebraic Groups* (2017), `milne-2017-algebraic-groups`,
Theorem 15.34 and its proof (printed p.319). No new mathematical source is
used; the solvability hypothesis isolates the only step that needs an
algebraically closed field.
