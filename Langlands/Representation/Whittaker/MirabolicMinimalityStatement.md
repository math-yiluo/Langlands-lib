# Compact minimality in the actual mirabolic smooth induction

Author: Worker 440. Worker 127 supplied the precise target specification
and source route.

`Langlands.Whittaker.MirabolicCompactMinimalityStatement.{uF}` is a
proposition target for the p-adic specialization of Bernstein–Zelevinsky
(1976), Proposition 5.15(c), printed pp.49–50. This module states the
containment; it does not prove it or assume it as an axiom.

## Exact statement

The proposition quantifies over every prime through
`(p : ℕ) (_hp : Fact p.Prime)`, every `F : PadicField.{uF} p`, and then
installs `F.canonicalTopologicalData.topology`. It quantifies over every
`n : ℕ`, every `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`,
and every
`W : Subrepresentation (Whittaker.mirabolicSmoothInduced ψ n)`.
Its conclusion is

```lean
W ≠ ⊥ → Whittaker.mirabolicCompactSubrepresentation ψ n ≤ W
```

All these quantifiers are inside the proposition definition. The field
universe `uF` is arbitrary. The coefficients are ℂ and the function carrier
is the one already constructed by `MirabolicModels`; no independent
representation carrier or additional universe is introduced. The bundled
additive character already includes continuity, nontriviality and values
in the unit circle. There are no hypotheses on irreducibility,
admissibility, finite generation or multiplicity one, and no supplied
embedding or minimality assertion.

An internal `letI` supplies `IsTopologicalRing F.Carrier` from the
published canonical valuative relation and local-field certificate by
typeclass inference. This is a derived certificate for the selected
canonical topology, needed to instantiate the models, not another
quantified instance or mathematical hypothesis.

## Source correspondence and canonical image

BZ76 §5.1, printed p.44, defines the last-row mirabolic group `P_r` and
its full upper unitriangular subgroup `U_r`. In this module `r = n + 1`;
these are the published `GeneralLinear.mirabolic n F.Carrier` and
`GeneralLinear.Mirabolic.upperUnipotent n F.Carrier`.
Sections 5.5–5.6, printed p.45, choose the nondegenerate character
`Θ(u) = ψ₀(∑ uᵢ,ᵢ₊₁)`. The published `mirabolicCharacter ψ n` uses
exactly this positive character: the additive-character law turns the sum
into the product of the adjacent-entry character values, as certified by
`mirabolicCharacter_eq_product`.

Section 5.7, printed p.45, defines the smooth standard representation
`τ_P = Ind(P,U,Θ)` and the compact standard representation
`τ_P⁰ = ind(P,U,Θ)`. They correspond respectively to
`Whittaker.mirabolicSmoothInduced ψ n` and the compact model whose
canonical image is `Whittaker.mirabolicCompactSubrepresentation ψ n`.
The latter is literally a subrepresentation of the former, with membership
given by compactness of the actual projected nonzero support in `U \ P`.
The published `mirabolicCompactInclusion ψ n` is the underlying function
inclusion. Both models use `f(u * g) = Θ(u) * f(g)` and right translation
`(s • f)(g) = f(g * s)`, as in §§2.21–2.22, printed pp.21–22. No modular
normalization from the alternative convention on p.22 is inserted.
The source's compact-open right stabilizer and the implementation's open
right stabilizer give the same smooth functions in the p-adic setting,
where every open subgroup contains a compact open subgroup.

Proposition 5.15(c), printed p.49, states that a nonzero subrepresentation
`π ⊆ τ_P` has completely nondegenerate part equal to `τ_P⁰`, and in
particular contains `τ_P⁰`. The target records precisely this last
containment. It does not state the additional conclusion about the
degenerate quotient or introduce the derivative filtration.

The proof on printed p.50 uses the scalar uniqueness of §5.15(b).
A nonzero subrepresentation of `τ_P` is nondegenerate because its
inclusion gives a nonzero map to `τ_P`; its completely nondegenerate part
is a nonzero direct sum of copies of `τ_P⁰`. Any such copy maps nontrivially
into `τ_P`. Part (b) identifies every map `τ_P⁰ → τ_P` as a scalar multiple
of the standard embedding. A nonzero scalar multiple has the same image
as that embedding. Thus the source identifies the actual canonical
compact image inside `τ_P`, which is the containment used here; existence
of an unspecified isomorphic copy would be weaker. This paragraph
explains the source's argument and is not a claim of an implemented Lean
proof.

## Rank-one boundary and scope

The source's matrix rank `r` is `n + 1`, so every positive matrix rank is
retained. In particular `n = 0` gives `P₁ = U₁ = {1}`. The adjacent-entry
product is empty, hence the induced subgroup character is trivial even
though `ψ` itself remains nontrivial. The quotient is a point and both
standard function models are one-dimensional complex spaces. The
containment then says that any nonzero complex subspace contains this
whole space. No positive lower bound on `n` is needed or imposed.

This is a source-derived mathematical specialization. The imported
mirabolic groups, character transport, evaluation, support and inclusion
laws are elementary implementation definitions and proofs; they do not
establish the minimality assertion. The coefficient-image construction,
ambient-open-subgroup and compact-support adapters, conversion of raw
characters, and final Kirillov deduction remain separate work. This
module constructs no Fourier, sheaf or derivative machinery and makes no
claim that those prerequisites or this proposition have been proved.
All existing Library Lean/Markdown pairs are preserved.

## Source and imports

- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F) where F is a non-Archimedean local field*, Russian Math. Surveys
  31:3 (1976), 1–68, English translation. Registered source
  `bernstein-zelevinsky-1976-representations-gln`, SHA256
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
  Read §§2.21–2.22, printed pp.21–22 (zero-based PDF indices 20–21);
  §§5.1 and 5.5–5.7, pp.44–45 (indices 43–44); and §5.15 with its
  proposition and proof, pp.48–50 (indices 47–49). Printed pp.45, 49
  and 50 were also checked visually. The retained source hash was
  verified. No registered erratum for this source was found in the
  current project/Library notes or literature index.

The two imports are
`Langlands.Representation.Whittaker.MirabolicModels`, supplying the actual
groups, characters and induction models through its published dependencies,
and `Langlands.LocalField.Canonical`, supplying the canonical p-adic
topological data. No change to `KirillovStatement` or `MirabolicModels`
is required.
