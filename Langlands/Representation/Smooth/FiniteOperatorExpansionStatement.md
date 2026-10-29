# Finite operator expansion of a smooth representation of `Fˣ`

Worker 940 defines `Langlands.FiniteOperatorExpansionStatement.{uF,uV}` in
module `Langlands.Representation.Smooth.FiniteOperatorExpansionStatement` as a
closed proposition. This file states the result; it does not prove it.

## Exact statement

Quantify over a natural number `p` with `Fact p.Prime`, a p-adic field
`F : PadicField.{uF} p` and local-field data `T : F.TopologicalData`, and install
the topology `T.topology` on `F.Carrier`. The unit group `F.Carrierˣ` then carries
Mathlib's `Units` topology, which is induced by `u ↦ (u, u⁻¹)` into
`F.Carrier × F.Carrierᵐᵒᵖ`. Then quantify over a complex vector space
`V : Type uV` (`AddCommGroup V`, `Module ℂ V`) and an actual representation
`σ : Representation ℂ F.Carrierˣ V`. The universes `uF` and `uV` are independent
and unrestricted.

There are exactly two hypotheses.

1. `IsSmooth σ`: every vector of `V` is fixed by some open subgroup of
   `F.Carrierˣ` in the topology above (`Langlands.IsSmooth`).
2. `FiniteDimensional ℂ (Submodule.span ℂ (Set.range σ))`: the operators `σ(a)`,
   `a ∈ F.Carrierˣ`, span a finite-dimensional complex subspace `S` of
   `Module.End ℂ V`.

Write `|x|` for `T.normalizedAbs x`, which is `q^(-ord x)` for `x ≠ 0` and `0`
at `0`, where `q` is the cardinality of the residue field of the valuation in
`T` and `ord` is its normalized order. Let `S⁺` be the actual submodule

```lean
Submodule.span ℂ {B : Module.End ℂ V |
  ∃ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 ∧ σ b = B}
```

spanned by the operators `σ(b)` with `|b| ≤ 1`. The conclusion is the conjunction
of the following two assertions.

- **Bounded span.** `S⁺ = S`, as an equality of submodules of `Module.End ℂ V`.
- **Expansion.** There exist a finite set `Y : Finset (F.Carrierˣ → ℂ)` and a
  total family `A : (F.Carrierˣ → ℂ) → Module.End ℂ V` such that:
  1. every `η ∈ Y` is continuous for the `Units` topology, and its left
     translates `fun a => η (b * a)`, as `b` ranges over `F.Carrierˣ`, span a
     finite-dimensional complex subspace of `F.Carrierˣ → ℂ`;
  2. `A η ∈ S⁺` for every `η ∈ Y`;
  3. for every unit `b`, the equality of endomorphisms
     `σ b = ∑ η ∈ Y, η b • A η` holds.

The set `Y` and the family `A` are chosen once, before every unit `b` and every
vector: the identity is an equality in `Module.End ℂ V`, so the same finite data
expands `σ(b) v` for all vectors `v` at once. The identity holds for every unit
`b`, including those with `|b| > 1`; the bound `|b| ≤ 1` only restricts the
spanning family of `S⁺` in which the coefficient operators lie. The values of `A`
outside `Y` are unrestricted. If `S` is zero, for example when `V` is the zero
space, `Y` may be empty; no nontriviality hypothesis is imposed.

No topology on `V`, finite-dimensionality of `V`, admissibility, finite
generation, irreducibility, central or generalized-eigencharacter decomposition,
common open kernel or expansion certificate is assumed. The functions `η` are
arbitrary finite functions, not required to be characters.

## Correspondence with the source

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, printed p.181 (one-based PDF page 14). Section (2.2) recalls that a
finite function on a locally compact abelian group is a continuous function whose
translates span a finite-dimensional vector space. The proof of Proposition (2.2)
then begins with remarks on a smooth representation `σ` of `Fˣ` on a complex
vector space such that the algebra `𝒜` spanned by the operators `σ(a)` is finite
dimensional. The remarks assert:

- there are a finite set `X` of finite functions on `Fˣ` and elements
  `A_χ ∈ 𝒜` with `σ(a) = ∑_{χ ∈ X} χ(a) A_χ` for every `a ∈ Fˣ`;
- the set `X` depends only on the isomorphism class of `𝒜`;
- every element of `𝒜` satisfies a polynomial equation, so `𝒜` is spanned as a
  vector space by the operators `σ(a)` with `|a| ≤ 1`.

The statement corresponds to these remarks as follows.

- The source's algebra `𝒜` is the Lean linear span `S`. The linear span of the
  operators `σ(a)` already contains the identity `σ(1)` and is closed under
  composition, since `σ(a) σ(b) = σ(ab)`; hence it equals the algebra they span.
- The first remark is the expansion conjunct, with `Y` for `X` and `A η` for
  `A_χ`. A finite function is encoded as continuity in the `Units` topology
  together with finite-dimensionality of the span of the translates
  `a ↦ η(b * a)`. Because `Fˣ` is commutative, left and right translates agree.
- The third remark is the bounded-span conjunct `S⁺ = S`. The source's `|a|` is
  a normalized absolute value of `F`. The condition `|b| ≤ 1` means that `b` is
  integral for the valuation, so `S⁺` does not depend on how the absolute value
  is normalized; the Lean statement uses the project's `T.normalizedAbs`.
- The second remark, dependence of `X` only on the isomorphism class of `𝒜`, is
  not formalized.

### Derived packaging

The following choices are internal to this formalization.

- The source places `A_χ` in `𝒜`. The Lean statement places `A η` in `S⁺`. By
  the bounded-span conjunct these are the same condition, but stating membership
  in `S⁺` records directly the property used on printed p.182, where the
  operators `A_η` belong to the linear span of `{ρ(b) : |b| ≤ 1}`.
- The coefficient operators form a total family on all functions `Fˣ → ℂ`
  rather than a family indexed by `Y`.
- Smoothness and continuity use the topology installed from `T.topology`; for a
  topological field with continuous inversion away from zero, the `Units`
  topology agrees with the subspace topology, but the statement does not rely on
  this comparison.
- The universes of the field and of the representation space are separate.

## Intended route (not a proof)

The following outline explains why the statement is expected to hold; it is not
an implemented Lean proof. A finite-dimensional subspace of `Module.End ℂ V` is
separated by evaluations at finitely many vectors. Each of these vectors is fixed
by an open subgroup; on the intersection `K` of these subgroups, `σ(k) - σ(1)` is
an element of `S` that vanishes at all of these vectors, so `σ(k)` is the
identity. Hence `σ` is constant on cosets of `K`. The coordinates of `σ(b)` in a
basis of `S` are therefore locally constant, hence continuous, and their
translates lie in their span because left multiplication by `σ(b)` preserves `S`.
For the bounded span, let `ϖ` be an element with `|ϖ| < 1`. The invertible
element `σ(ϖ)` of the finite-dimensional algebra `S` has an inverse that is a
polynomial in `σ(ϖ)`. For any unit `a`, choose `N` with `|aϖ^N| ≤ 1`; writing
`σ(a) = σ(aϖ^N) σ(ϖ)^(-N)` expresses `σ(a)` through operators `σ(aϖ^m)` with
`m ≥ N`, all of normalized absolute value at most `1`. No finite-dimensionality
of `V` is used.

## Dependencies and intended uses

Project imports: `Langlands.LocalField.Normalization.Definitions` supplies
`PadicField.TopologicalData.normalizedAbs`, and
`Langlands.Representation.Smooth.Definitions` supplies `IsSmooth`. Mathlib
supplies representations, the `Units` topology, submodule spans,
finite-dimensionality and finite sums. Existing Library pairs are unchanged.

This statement is a focused prerequisite of the exact proof of
`Langlands.Whittaker.JPSDecompositionStatement` (task
`b1da68dc-38c9-449e-a71c-bae1f8902b22`), whose proof on printed p.182 applies these
remarks to the coordinate action `σ_n` on a coordinate-germ quotient. That
consumer must itself supply smoothness of the quotient action; this statement
does not assume, and is not derived from, `JPSDecompositionStatement` or the
Whittaker asymptotic statements.

`Langlands.CentralOperatorExpansionStatement` is a different result. It assumes
an admissible, finitely generated representation of an ambient group, which
implies finite-dimensionality of the operator span there, and it asserts no
bounded-span equality. The present statement instead assumes finite-dimensionality
of the operator span directly and does not require admissibility or finite
generation, which coordinate-germ quotients need not satisfy.

## Source record

Registered source `jps-1979-gl3-i`: H. Jacquet, I. I. Piatetski-Shapiro and
J. Shalika, *Automorphic forms on GL(3) I*, Ann. of Math. (2) 109 (1979),
169–212. Retained file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`,
SHA-256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Worker 940 read the extracted text and the rendered image of printed p.181 (PDF
page 14), including the finite-function definition and the remarks above, and
the text of printed p.182 where they are applied. No errata file for this source
was present in the project notes, the current Library notes or the literature
collection when this statement was prepared.
