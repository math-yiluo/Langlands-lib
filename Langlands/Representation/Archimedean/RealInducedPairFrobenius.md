# Four-crossing Frobenius map for two real induction blocks

Worker 765 derives this operator and its landing property from the actual
Fourier-defined standard modules, the ambient GL3 landing theorem
`RealSwapLandingInStages.realSwapLandingInStages`, and disjoint Frobenius
commutation. This is internal infrastructure; no classification theorem or
external literature result is assumed.

Write `KF(ds)` for the complex submodule of functions on `GL_4(R)` which belong
to `realStandardModule 4 ds` and are finite under right translation by `O(4)`.
For complex character data `d,e`, put `L = d.weight.natAbs` and
`M = e.weight.natAbs`. The definitions `first d` and `second d` are the actual
position characters of the induction block: their exponents are
`d.exponent + L/2` and `d.exponent - L/2`, and their parities are respectively
`(L+1) mod 2` and zero. The same convention applies to `e`.

## Statement and multiplier assumptions

`RealInducedPairFrobeniusLandingStatement` quantifies over all `d,e`, every
complex parameter `delta`, and four sequences `mu1,mu0,mu2,mu3 : Z -> C` with
`MultiplierData d e delta mu1 mu0 mu2 mu3`. This structure consists precisely of
recurrence and symmetry at the following parameters:

| Multiplier | Recurrence parameter | Parity representative | Symmetry sign |
| --- | --- | --- | --- |
| `mu1` | `delta` | `M+1` | `(-1)^(M+1)` |
| `mu0` | `delta+L` | `L+M+2` | `(-1)^(L+M+2)` |
| `mu2` | `delta+M` | `0` | `1` |
| `mu3` | `delta+L+M` | `L+1` | `(-1)^(L+1)` |

Here recurrence and symmetry mean the existing `IsRecurrent` and `IsSymmetric`
predicates, restricted to the indicated integer parity class. There is no
nonzero-weight, exponent-order, invertibility or nonvanishing assumption.
The parameter `delta` is arbitrary; the statement does not require it to equal
an exponent difference.

For every `f` in `KF([induced d,induced e])`, the statement says that the
four-crossing map `h.to4 f`, initially constructed with a full-character target,
lies in `KF([induced e,induced d])`. The theorem
`realInducedPairFrobeniusLanding` proves this statement. `MultiplierData.swap`
is the resulting complex linear map between those actual standard modules,
obtained by restricting the codomain. `swap_apply_coe` identifies its underlying
function with `to4`.

## Crossing maps

Write `dA,dB,eA,eB` for the first and second position characters. The intermediate
lists are:

| Name | Characters in order |
| --- | --- |
| `l0` | `dA,dB,eA,eB` |
| `l1` | `dA,eA,dB,eB` |
| `l10` | `eA,dA,dB,eB` |
| `l12` | `dA,eA,eB,dB` |
| `l3` | `eA,dA,eB,dB` |
| `l4` | `eA,eB,dA,dB` |

`characterSwapData` constructs valid `IsBlockFrobData` for two adjacent
character blocks using any natural representative of their parity class.
`data1,data0,data20,data3` give the word of positions `1,0,2,1` from `l0` to
`l4`, with multipliers `mu1,mu0,mu2,mu3`. The other two data lemmas,
`data2,data02`, give the alternative middle order `2,0`. All targets of these
individual maps are full-character standard modules. The definitions
`to1,to10,to12,to3,to4` compose the corresponding actual `blockFrobMap` maps;
`to1` first includes the input in `KF(l0)` by forgetting its Fourier constraints.

## Implemented landing proof

The `posChar` lemmas compare the existing position characters through
`realPositionCharacter_eq_charFun`, including positions beyond rank four.
`kf_le` forgets selected induction constraints while retaining the same
principal series and compact finiteness. It supplies the three source
inclusions into `l0`, `[induced d,eA,eB]`, and `[dA,dB,induced e]`.
The lemmas `mem_tD`, `mem_tE`, and `mem_dst` recover the required induction
constraints from their forbidden Fourier modes on `O(4)` by
`mem_realStandardModule_of_unitaryCompact`. Thus compact vanishing gives
membership in the actual globally defined standard module.

For `landing10`, forget the input e-block constraint and apply induced-first
ambient GL3 landing in coordinates 0,1,2. The first two crossings then place
the result in `[eA,induced d,eB]`. A second induced-first application in
coordinates 1,2,3 proves `landing4_d`: the forbidden d-modes of the final
output vanish at position 2.

For `landing12`, forget the input d-block constraint and apply character-first
ambient GL3 landing in coordinates 1,2,3. This gives membership in
`[dA,induced e,dB]`. A second character-first application in coordinates 0,1,2
proves the e-block condition at position 0 for the alternative crossing order.
`to3_eq` identifies the two intermediate results by
`blockFrobMap_disjoint_comm`, since positions 0 and 2 are disjoint and share
the same multipliers. The final position-one map then gives the identical
function, establishing `landing4_e` for `to4` itself.

Every GL3 application uses the compact multiplier identity of `blockFrobMap`
and continuity of its actual standard-module output. Parity adjustments use
`isRecurrent_congr`, `isSymmetric_congr`, and equality of powers of minus one
modulo two. No intermediate landing or commutation premise remains.
`mem_dst` combines the two final conditions, completing `landing` and the
named statement proof, including the empty forbidden windows at weight zero.

## Scope

This module constructs the linear exchange map and proves its landing from the
four explicit recurrence and symmetry assumptions. It does not claim an
intertwining law for arbitrary `delta`, existence or invertibility of the
multipliers, injectivity, surjectivity, a kernel description, or a filtration.
In particular `RealInducedInducedFiltrationStatement` remains a separate
proof obligation.
