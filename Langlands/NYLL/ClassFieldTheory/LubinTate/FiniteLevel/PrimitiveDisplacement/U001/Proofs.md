# Proof of NYLL M362.001

This module proves `Langlands.NYLL.PortInternal.M362.d001` with target
`Langlands.NYLL.PortInternal.M362.d001Statement`, imported from the
published `U001.Statements` module. It retains the target's full source
universe and parameter telescope.

The source is Naganori Yamaguchi's NYLL, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveDisplacement.lean:47–69`,
private theorem `LubinTate.coeff_subst_X_zero` (M362.001). The source file has
SHA-256 `520ab08231608ac43915d72c8a94c5d4ea1ad2fd4b7311a77f8f889a37421cbc`.
The registered source is `nyll-classfieldtheory-fbd320cd-supplement`.

The implemented proof specializes the published Library theorem
`Langlands.CommutativeAlgebra.MvPowerSeriesFactorial.coeff_subst_restrictFamily`
from `Langlands/CommutativeAlgebra/MvPowerSeriesCoordinateChange.lean`.
The hypothesis `hd` identifies `d` with `Finsupp.single 0 (d 0)`.
At `n = 1`, the published `restrictFamily` is definitionally the pair
`![PowerSeries.X, 0]`, as checked at both indices of `Fin 2`.
The published coefficient equality then has the exact target type, using
Mathlib's definition of univariate coefficient extraction.

Changes: prefix and internalize the source-private name, make the otherwise
independent ring universe explicit, state the result using the target and unfold
it, replace the source's coefficient-sum calculation by specialization of the
published theorem, import that theorem and `Mathlib.Tactic.FinCases`, and omit all
surrounding local-field context. The `ext i` tactic acts on finitely supported
functions; it does not invoke M336.002 `LubinTate.LubinTateSeries.ext`.
The Apache-2.0 copyright and authors are retained, with Library notices in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

The proof introduces no definitions or instances and changes no imported
statement or hypothesis.
