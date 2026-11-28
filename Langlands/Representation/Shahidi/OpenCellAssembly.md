# Assembly: the half-plane and the sum from the shell identities

Module `Langlands.Representation.Shahidi.OpenCellAssembly`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `openCellAbscissa r t A B = 2(r+t+1) + 2(r+1) max(A,0) + 2(t+1) max(B,0) + (r+1)(t+1) + 1`, the
  abscissa `σ` used for the target statement; `pow_mul_summandRatio_le`: for `q ≥ 2` and
  `σ < Re s`, `q^((r+1)(t+1)) · summandRatio ≤ 1/2`.
- `shellCoefficient x D = ∑_(|T| = D) ∏_(p ∈ T) (-x_p)`, the degree-`D` part of
  `∏_p (1 - x_p)`, with `hasSum_shellCoefficient`.
- `classDepth` (the depth of a class, as a natural number), `pairParameter q a c s (i, j) =
  a_i c_j⁻¹ q^(-(1+s))`.
- `ShellIdentity K ψ hϖ a c s f`: for every `D`, the open-cell summands over the classes of depth
  `D` sum to `shellCoefficient (pairParameter q a c s) D`.
- `hasSum_of_shellIdentity`: for `ψ` of conductor `𝒪`, a function `f` with the target
  transformation law (`IsOpenCellSection`), parameters with `|a_i| ≤ q^A` and `|c_j⁻¹| ≤ q^B`,
  and `openCellAbscissa r t A B < Re s`, the shell identity implies that the open-cell summands
  over all classes sum to `∏_(i,j) (1 - a_i c_j⁻¹ q^(-(1+s)))`.
- `OpenCellShellIdentityStatement`: the shell identity holds for all ranks, all `p`-adic fields,
  all `ψ` of conductor `𝒪`, all uniformizers, all `a`, `c`, all `s ∈ ℂ` and every `f` with the
  target transformation law; `unramifiedOpenCellSum_of_shellIdentity`:
  `OpenCellShellIdentityStatement → UnramifiedOpenCellSumStatement`, with `σ = openCellAbscissa`.

## Provenance

Derived: summation over depth shells (`Langlands.Representation.Shahidi.OpenCellSum`) with the
counting bound of `Langlands.Representation.Shahidi.OpenCellCount`.
