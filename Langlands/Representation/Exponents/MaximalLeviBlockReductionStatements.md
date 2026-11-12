# Reduction statements for the Bernstein component of a non-self-associate supercuspidal

Author: Worker 77. Module
`Langlands.Representation.Exponents.MaximalLeviBlockReductionStatements`, namespace
`Langlands.Aubert.General.RepresentedParabolic`. It contains two **statements**, closed
`Prop`-valued definitions with universe parameters `u, v`. Neither is assumed or proved here.

- `MaximalLeviBlockFullEssSurjStatement`: part (iii) of the published
  [MaximalLeviBlockStatements](MaximalLeviBlockStatements.md) without its faithfulness
  conjunct.
- `MaximalLeviBlockStatementsFromInputsStatement`: the implication
  `MaximalLeviSupercuspidalReducibilityStatement.{u, max u v} →
  MaximalLeviBlockFullEssSurjStatement.{u, v} → MaximalLeviBlockStatements.{u, v}`.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
**9 July 2026**, literature ID `renard-2026-representations-groupes-reductifs-padiques`,
file `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:

- VII.1.3, Theorem, printed pp.224–226 / PDF pp.230–232;
- VII.1.3, Corollary, printed p.226 / PDF p.232, and its proof, printed pp.226–227 /
  PDF pp.232–233.

Worker 77 read PDF pages 232 and 233.

The proof begins: "Le premier point découle immédiatement du théorème." Point (i) is
derived from the Theorem. Points (ii) and (iii) are then proved from (i), the geometric
lemma VI.5.3, Lemma A.VIII.1, the adjunction between `r_D` and `i_P^G` and Lemma VI.7.2 (iii).

## `MaximalLeviBlockFullEssSurjStatement`

This statement has exactly the binders, hypotheses and `let` definitions (`IsTwist`,
`InBlockM`, `InBlockG`) of `MaximalLeviBlockStatements`:

- a nonarchimedean local field `k : Type u`;
- a connected reductive `G` over `Spec k`, with the canonical topology on `G(F)`;
- an actual maximal proper rational parabolic `p : P ⟶ G`, with rational Levi `l`,
  matching radical `r` and `hmul`;
- an irreducible supercuspidal `ρ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)`;
- the hypothesis encoding `w · D ≠ D`.

Its conclusion is the third conjunct of that statement with the `Faithful` conjunct
removed. The other three conjuncts are copied without change:

- induction (`leviInductionFunctor p l r hp hr hl hmul`) sends every `InBlockM` object to
  an `InBlockG` object;
- the functor `InBlockM.ι ⋙ leviInductionFunctor …` is `Full`;
- every `InBlockG` object is isomorphic to the induction of an `InBlockM` object.

The meaning of the setting and of the encodings of `D`, `M(M)_D` and `M(G)_Ω` is explained
in [MaximalLeviBlockStatements.md](MaximalLeviBlockStatements.md). See its table of parts
and correspondence notes 2, 5 and 6. Part (iii) is Renard's Corollary (iii): `i_P^G` is an
equivalence from `M(M)_D` onto `M(G)_Ω`, inverse to `r_D`. An equivalence is a functor that
is full, faithful and essentially surjective. Faithfulness is left out here because it
holds for `i_P^G` on all of `M(M)`, with no hypothesis on `ρ`: evaluation of induced
functions at `1` is surjective and `i_P^G` acts on morphisms by postcomposition. It is
left to proofs of `MaximalLeviBlockStatementsFromInputsStatement`. As in the
published statement, the unit isomorphism `π → i_P^G r_D(π)` is not stated, because `r_D`
is not named.

## `MaximalLeviBlockStatementsFromInputsStatement`

This statement has two premises:

1. `MaximalLeviSupercuspidalReducibilityStatement.{u, max u v}`, the published VII.1.3
   Theorem ([MaximalLeviSupercuspidalReducibilityStatement](MaximalLeviSupercuspidalReducibilityStatement.md)),
   at field universe `u` and carrier universe `max u v`;
2. `MaximalLeviBlockFullEssSurjStatement.{u, v}`.

Its conclusion is the published `MaximalLeviBlockStatements.{u, v}`. The statement says
that parts (i) and (ii) of the Corollary, and the faithfulness conjunct of part (iii),
follow from the VII.1.3 Theorem alone. The rest of part (iii) is premise 2. The source
derives (i) from the Theorem. For (ii) the statement allows any argument from the Theorem;
the source uses (i) and VI.5.3 instead.

## Faithfulness notes

- **No change to the target.** The conclusion is the published target at the same
  universes. Premise 2 copies three of the four conjuncts of its part (iii) verbatim, with
  the same binders, hypotheses and `let` definitions. Premise 1 is a published statement
  at universes chosen to match the target. No premise mentions the specific `G`, `P` or
  `ρ` of the conclusion, so the statement is an implication between closed propositions.
- **Universes.** The Theorem quantifies over carriers in an arbitrary `Type v`. Here it is
  used at `max u v`, the carrier universe of the target's twists `σ` of `ρ`, because part
  (i) applies it to them.
- **The second premise contains part of the conclusion.** Premise 2 consists of three of
  the four conjuncts of part (iii), so of part (iii) the statement reduces only the
  faithfulness conjunct. Its
  purpose is to let the derivation of parts (i), (ii) and of faithfulness be reviewed and
  published apart from the proofs of the Theorem and of the rest of part (iii). Proofs of
  both premises give `MaximalLeviBlockStatements`.

## Relation to published work

At Library commit `c2558dd5`, `MaximalLeviSupercuspidalReducibilityStatement` has proof task
`004e00e1-5995-4dc1-884e-a5f512150d0c` and is not proved. The published
`MaximalLeviSupercuspidalReducibilityFromInputsStatement`, whose proof is published,
derives it from eleven other published statements. No theorem proves
`MaximalLeviBlockStatements` or its part (iii). Both belong to proof task
`f4046ca6-c4e9-4422-85bf-f67a9d92de79`.

## Provenance

Derived. `MaximalLeviBlockFullEssSurjStatement` consists of three of the four conjuncts of
part (iii) of the published statement of Renard VII.1.3, Corollary.
`MaximalLeviBlockStatementsFromInputsStatement` records that parts (i) and (ii) depend on
the VII.1.3 Theorem, as the Corollary's proof states. It also records that faithfulness of
induction needs no input.
