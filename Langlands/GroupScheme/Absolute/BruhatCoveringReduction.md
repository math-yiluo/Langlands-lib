# Reduction of the absolute Bruhat covering to structure-theory statements

This module reduces the absolute Bruhat covering
([`AbsoluteBruhatCoveringStatement`](BruhatCoveringStatement.md)) to seven Library statements
from the structure theory of linear algebraic groups. It assembles the group-theoretic steps of
[`BruhatCoveringSteps`](BruhatCoveringSteps.md) with three geometric modules:
[`ProperAffineExtension`](../Dynamic/ProperAffineExtension.md) (a `𝔾_m`-orbit in a proper
scheme extends over the affine line),
[`SchemeActionLimit`](../Dynamic/SchemeActionLimit.md) (the value at `0` of such an extension
is a fixed point) and [`BruhatCellLimit`](../Dynamic/BruhatCellLimit.md) (the opposite-cell
argument at that fixed point).

## The prerequisite statement

`BruhatCoveringPrerequisites` (a `Prop` in the universe parameter `u`) is the conjunction of
the following Library statements, in this order:

1. `TorusFiniteGaloisSplittingStatement`;
2. `RegularCocharacterBorelStatement`;
3. `GenericCentralizerStatement`;
4. `MaximalTorusCentralizerStatement`;
5. `ParabolicSubgroupQuotientProperStatement`;
6. `CentralizerBorelIntersectionStatement`;
7. `SolvableMaximalTorusConjugacyStatement`.

Each statement's mathematical content and sources are recorded in its own Markdown. None of
them is the rational Bruhat decomposition, Borel–Tits 1965 Proposition 4.18,
`TwoBorelCommonMaximalTorusStatement`, `ParabolicIntersectionGeometryStatement` or
`ParabolicIntersectionTorusStatement`, and the proof below uses none of these.

Provenance: this definition is internal. It records exactly the inputs that the dynamic-limit
proof below needs and that are not yet proved in the Library, so that the absolute Bruhat
covering follows once they are proved.

## The reduction theorem

`absoluteBruhatCovering_of_prerequisites`: `BruhatCoveringPrerequisites` implies
`AbsoluteBruhatCoveringStatement`. Both are taken in the same universe `u`.

The proof fixes an algebraically closed field `k`, a connected reductive `G` over `k`, a Borel
pair `(i : B ⟶ G, j : T ⟶ G)` and a rational point `g` of `G`. It then:

1. takes `ν : 𝔾_m ⟶ T` with `P(ν ≫ j)` represented by `i` and `Z(ν ≫ j) = range j`
   (`BruhatCovering.exists_cocharacter`, from statements 1–4);
2. takes a quotient `q : G ⟶ Q` with `Q` separated and proper over `k`, `q` smooth, surjective
   and quasi-compact, and fibres exactly the cosets of the range of `i`
   (`BruhatCovering.exists_proper_quotient`, from statement 5), and lets `a` be the left
   translation action of `G` on `Q` (`Dynamic.flagQuotientSchemeAction`, with
   `Dynamic.flagQuotientSchemeAction_act_lift` for compatibility with `q`);
3. extends the orbit map `t ↦ (ν ≫ j)(t) · q(g)` (`SchemeAction.gmOrbit` of the restricted
   action) over the affine line to `e`, since `Q` is proper
   (`AffineLine.exists_extension_of_isProper`);
4. the value `Dynamic.evalZero e` is fixed by the restricted action
   (`SchemeAction.IsGmOrbitExtension.isFixed_evalZero`), so it equals `q(n)` for some `n` in
   `normalizerPoints j` (`BruhatCovering.exists_normalizerPoint_of_isFixed`, from statements 6
   and 7);
5. the opposite-cell argument gives `b₁ b₂ : B(k)` with `g = i(b₁) · n · i(b₂)`
   (`Dynamic.BruhatCellLimit.exists_eq_mul_mul_of_mem_normalizerPoints`, which uses the proved
   `oppositeCellStatement`), and `n` with its normalizing automorphism is the required element of
   `normalizerPoints j`.
