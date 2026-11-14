# Proof of NYLL M362.016

This module proves `Langlands.NYLL.PortInternal.M362.d016` with target
`Langlands.NYLL.PortInternal.M362.d016Statement`, imported from the
published `U016.Statements` module. It retains the target's full source
universe and parameter telescope.

The source is Naganori Yamaguchi's NYLL, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveDisplacement.lean:274–284`
(statement lines 274–278),
private theorem `LubinTate.hasEval_fin_two` (M362.016). The source file has
SHA-256 `520ab08231608ac43915d72c8a94c5d4ea1ad2fd4b7311a77f8f889a37421cbc`.
The registered source is `nyll-classfieldtheory-fbd320cd-supplement`.

The implemented proof follows the original. Each coordinate of the pair is
admissible by one of the two supplied univariate evaluation hypotheses. The
cofinite condition is automatic because `Fin 2` is finite.

Changes: prefix and internalize the source-private name, make the otherwise
independent ring universe explicit, state the theorem using the target and
unfold it, import only that target and `Mathlib.Tactic.FinCases`, and omit all
surrounding local-field context. The proof body otherwise follows the source.
No completeness, continuity, field or ring topology assumption is added.
The Apache-2.0 copyright and authors are retained, with Library notices in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

The proof introduces no definitions or instances and changes no imported
statement or hypothesis.
