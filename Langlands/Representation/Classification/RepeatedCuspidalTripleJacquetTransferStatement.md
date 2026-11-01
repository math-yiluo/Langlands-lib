# Repeated-factor cuspidal triple Jacquet transfers

Author: Worker 19. Statement specification: Worker 320.

This module defines the proposition
`Langlands.Classification.RepeatedCuspidalTripleJacquetTransfer.{uF,uV} F T`.
It states both local transfers used in the proof of Jantzen (2000),
Lemma 2.2.2, printed pp.545–547. Neither transfer is proved here.

## Actual representations and hypotheses

The outer parameters are an arbitrary prime `p`, an actual
`F : PadicField.{uF} p`, and the supplied `T : F.TopologicalData`.
The definition installs `T.topology` and quantifies every natural rank `n`,
positive block shape `B : GeneralLinear.BlockShape n`, smooth complex
representation `π` of `GL_n(F)`, and family `C i` of actual
`GeneralLinear.SupercuspidalRep` objects on the groups `GL_(B.size i)(F)`.
The field and carrier universes `uF,uV` are independent. Both `π` and every
factor have carriers in `Type (max uF uV)`; their external tensor and actual
Jacquet quotients remain in that universe. There is no rank equality or
universe equality hypothesis.

The explicit hypotheses are `π.IsIrreducible`, `π.IsAdmissible`,
`π.HasFiniteLength`, and

```lean
SmoothRep.IsSubquotient
  (FiniteTensor.externalSmoothObject (fun i => (C i).obj))
  ((T.normalizedJacquetFunctor B).obj π)
```

Finite length is composition length over the complex group algebra, as in
the existing smooth-category predicate. Each `SupercuspidalRep` already
includes irreducibility, admissibility and the existing actual Jacquet
vanishing condition. Input and output use the existing `IsSubquotient`:
an invariant submodule of the ambient representation, an invariant submodule
of that submodule, and an actual categorical isomorphism from the indicated
tensor to the resulting quotient. The input need not be a quotient of the
entire Jacquet module.

## The two implications

For every `j` with `j + 2 < B.length`, put `a = j`, `b = j + 1`,
`c = j + 2`, and let `σab` and `σbc` be the existing adjacent block-label
swaps at `j` and `j + 1`. Write

```text
[C_i]  = ⟨B.size i, (C i).isoClass⟩
ν[C_i] = ⟨B.size i,
            T.supercuspidalClassRealPowerTwist (B.size i) 1 (C i).isoClass⟩.
```

These are elements of
`Σ d : ℕ, SupercuspidalClass.{max uF uV,uF} (F := F.Carrier) (n := d)`.
Equality first enforces equality of ranks and then equality of isomorphism
classes after transport along that rank equality. At a fixed rank,
`SupercuspidalRep.isoClass_eq_iff` identifies class equality with an actual
isomorphism of supercuspidal objects. The twist is the existing actual
determinant-character twist on classes.

After the common data and input subquotient hypothesis, the proposition is
the conjunction of:

1. If `[C_a] = ν[C_b]` and `[C_c] = [C_b]`, the actual external tensor of
   `fun i => (C (σab i)).obj` is an actual subquotient of
   `(T.normalizedJacquetFunctor (B.permute σab)).obj π`.
2. If `[C_a] = ν[C_b]` and `[C_c] = [C_a]`, either the actual external tensor
   of `fun i => (C (σbc i)).obj` is an actual subquotient at
   `B.permute σbc`, or the tensor of `fun i => (C (σab i)).obj` is such a
   subquotient at `B.permute σab`.

Thus the patterns, up to actual factor isomorphisms, are
`(A,B,B) → (B,A,B)` and
`(A,B,A) → (A,A,B) or (B,A,A)`, with `A = νB`.
The first disjunct of the second implication swaps `b,c`; the second swaps
`a,b`. The permutation maps each new position to its old label, and
`(B.permute σ).size i = B.size (σ i)`, so the permuted factor family has
exactly the required ranks without a chosen carrier identification.
Every position outside the selected adjacent triple is fixed. Outside
factors are arbitrary supercuspidal objects; they may repeat or be linked
with the selected factors. No isolated three-factor product replaces the
ambient subquotient conclusion.

## Source comparison and derived scope

Chris Jantzen, *On Square-Integrable Representations of Classical p-adic
Groups*, Canadian Journal of Mathematics 52 (2000), no.3, 539–581,
[DOI 10.4153/CJM-2000-025-7](https://doi.org/10.4153/CJM-2000-025-7).
Literature ID: `jantzen-2000-square-integrable-classical-i`.
The retained original is
`/home/taskhub/pilot/literature/Jantzen (2000), On Square-Integrable Representations of Classical p-adic Groups.pdf`,
SHA256 `539eee93dd339c42bf6d065bbb1969ab0e2c6c54699c5b4447a2166a3ddf9428`.
Section 1.2, PDF pp.3–4 / printed pp.541–542, and the complete proof of
Lemma 2.2.2, PDF pp.7–9 / printed pp.545–547, were read directly; the latter
three pages were also checked visually.

On printed pp.545–546 the selected factors are
`ν^αρ, ν^(α−1)ρ, ν^(α−1)ρ`. Jantzen passes to the coarse factor
`δ([ν^(α−1)ρ,ν^αρ]) × ν^(α−1)ρ`, asserts that it is the unique irreducible
coarse representation containing that triple in its minimal Jacquet module,
and returns to the order
`ν^(α−1)ρ, ν^αρ, ν^(α−1)ρ`. This is the first implication.
On printed p.547 the selected factors are
`ν^αρ, ν^(α−1)ρ, ν^αρ`. The two displayed coarse alternatives use
`δ([ν^(α−1)ρ,ν^αρ]) × ν^αρ` and
`ζ([ν^(α−1)ρ,ν^αρ]) × ν^αρ`. Refining them gives the two orders
`(ν^αρ,ν^αρ,ν^(α−1)ρ)` and
`(ν^(α−1)ρ,ν^αρ,ν^αρ)`. The second implication retains both alternatives.
The source later eliminates one alternative by lexicographic minimality;
that elimination is outside this statement.

The printed lemma concerns finite-length representations supported on one
integral real-twist line of a unitary supercuspidal representation and its
lexicographically minimal Jacquet constituent. This pair extracts the local
implications as a derived target: the selected supercuspidal `B` is arbitrary,
the ambient representation is explicitly irreducible, admissible and of
finite length, the positive block shape can be nonuniform, and all outside
supercuspidal factors are unrestricted. No unitary normalization, common
cuspidal line, lexicographic minimality or square-integrability is an input.
The printed statement alone does not establish this enlarged scope. An exact
proof must establish the local rank-three structure for arbitrary
supercuspidal `B` and justify coarse-constituent extraction and refinement in
the presence of all outside factors. It must derive any needed twisting
reduction rather than assume a unitary realization as data.

Section 1.2 uses normalized induction and Jacquet modules for standard upper
parabolics, with `ν = |det|` and `|ϖ| = q⁻¹`. The reused `T` definitions use
that residue-normalized absolute value, positive half-modulus covariance
and right translation for induction, and the inverse half-modulus action
on the actual upper Jacquet quotient. The exponent `1` in
`supercuspidalClassRealPowerTwist` is precisely this `ν`.

A bounded local filename and web search found no source-specific erratum;
this is not a claim that none exists. On p.545 the first printed
lexicographic inequality has the reversed direction: after swapping
`α₂ < α₁ − 1`, the new word is smaller. This concerns the later use of the
local transfer and changes neither implication here.

## Proof boundary and independence

The pair adds only a Prop-valued definition. It assumes no triple
irreducibility, composition structure, coarse-constituent uniqueness,
extraction theorem, embedding into a cuspidal induction, or classification
theorem. The two-supercuspidal product structure statement is a separate
rank-two target, and `TwoSupercuspidalAdjacentStructure` is a conditional
lower proof. Neither establishes the asserted rank-three uniqueness or
two-branch structure. Likewise, pair or segment-head commutation alone
does not prove these transfers.

The future proof must remain directly and transitively independent of
the parent analytic strong-head classification, multisegment exhaustion,
ordered strong-head existence, ordered quotient coverage, tempered block
uniqueness, square-integrable Langlands classification, square-integrable
exhaustion and regular exhaustion, including their conclusions and proof
successors. Independently proved lower geometric-lemma, actual finite-length,
tensor, Jacquet exactness/transitivity and local cuspidal-product results
are potential inputs only after an audit of their proof dependencies.
The placement of the original local argument before a classification
theorem does not certify that independence.
