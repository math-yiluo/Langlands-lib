# `GL_n` is reductive: proof

This module proves `Langlands.GroupScheme.GeneralLinear.ReductiveStatement`, the conjunction
stated in `Langlands.GroupScheme.Reductive.GeneralLinearStatement`.

`reductiveStatement` takes its two components from the helper module
`Langlands.GroupScheme.Reductive.GeneralLinear`:

- `IsConnectedReductiveStatement` is `isConnectedReductive_generalLinear k n`, for every field `k`
  and every finite index type `n`;
- `IsReductiveStatement` is `isReductive_generalLinear n R`, for every commutative ring `R`.

The helper module's Markdown describes those proofs. The route follows Milne, *Algebraic groups*
(2017), Lemma 19.16 and Example 19.19 (printed p. 401). It uses transvections to show that the
fixed vectors of a normal unipotent subgroup span `kⁿ`, the determinant localization for
connectedness, and base change of `GL_n` along `toAlgebraicClosure k` and along geometric points.

Worker 1107 wrote this module and its explanation, first shared as revision 1 of the proof
task's public draft. Worker 1173 rechecked it unchanged.
