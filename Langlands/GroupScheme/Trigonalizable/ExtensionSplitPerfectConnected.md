# Splitting of trigonalizable extensions with connected quotient over perfect fields

Module
`Langlands.GroupScheme.Trigonalizable.ExtensionSplitPerfectConnected`,
namespace `Langlands.GroupScheme.TrigonalizableExtensionSplit`.

This module proves case (c) of Milne's Theorem 16.26 in the encoding of the
published statement `TrigonalizableExtensionSplitStatement`. It does not prove
case (b) of the statement.

## Declaration

`exists_section_of_perfect_of_connected`: let `k : Type u` be a perfect field,
`G` a group scheme over `Spec k` with `[LocallyOfFiniteType G.X.hom]` and
`[IsAffineHom G.X.hom]`, `i : U ⟶ G`, `Λ : Type u` finitely generated and
`q : G ⟶ D(Λ)`, with `IsClosedSubgroup i`, `IsUnipotent U`,
`(SubgroupFunctor.range i).IsNormal`,
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`, and assume
`ConnectedSpace D(Λ).X.left`. Then there is a homomorphism
`s : D(Λ) ⟶ G` with `s ≫ q = 𝟙`.

## Proof

`admitsTower` (module `ExtensionSplitAlgClosed`, valid over every field)
gives a finite character-linear kernel tower for `q`.
`oneStepSplitting_of_perfect` gives the one-step splitting over `k` for the
connected `D(Λ)`, and `exists_section_of_admitsTower'` splits the tower.

## Source

J. S. Milne, *Algebraic Groups* (2017), `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, Theorem
16.26(c), printed p.332: "the field k is perfect and D is connected", with the
proof on printed p.333, which treats the case N isomorphic to `𝔾ₐ` by 15.34(a)
and the case N finite by 15.34(c) for π₀(N) and 15.34(b) for N°.
The correspondence between Milne's statement and the hypotheses is recorded
in the paired Markdown of the published statement. The Lean proof follows
Milne's induction along the series of Theorem 16.21, in the form of the
Library's character-linear kernel towers; at each step the correction is
solved by `PerfectCorrection.surjective_or_charValue_pow_eq_one` instead of
the exact sequences of 15.34.
