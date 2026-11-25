# The generic swap of two real induction blocks

Lean module: `Langlands.Representation.Archimedean.RealInducedSwapGeneric`,
namespace `Langlands.Archimedean.RealInducedSwapGeneric`.

This module constructs an internal generic subcase of `RealInducedSwapStatement`. The selected
`genericMap` is an explicit complex-linear map between the actual right
`O(4)`-finite standard modules. The accompanying `injective_of_generic` theorem
proves its injectivity and exact standard intertwining; `injective_in_stages`
extends the result through arbitrary surrounding lists.

This module retains the explicit `IsGenericPair d e` hypothesis. It does
not assert that unlinked induced blocks always satisfy that hypothesis, and it
does not prove the full `RealInducedSwapStatement` at exceptional parameters.
No nonzero-weight, exponent-order or unlinkedness hypothesis is needed for the
generic subcase that is actually proved.

## Characters, lists and hypotheses

Write `A = chA d`, `B = chB d`, `C = chA e` and `D = chB e`, using the published
`RealCharacterInducedSwap` definitions. For a complex character datum `z` of
weight `m` and exponent `t`, these position characters have exponents
`t + |m|/2`, `t - |m|/2`, and parities `(|m|+1) mod 2`, `0`, respectively.

`source d e` is `[induced d, induced e]` and `target d e` is
`[induced e, induced d]`. The following lists contain character blocks:

| Lean name | Ordered characters |
| --- | --- |
| `expanded d e` | `A B C D` |
| `crossed d e` | `A C B D` |
| `movedLeft d e` | `C A B D` |
| `movedRight d e` | `A C D B` |
| `middle d e` | `C A D B` |
| `expanded e d` | `C D A B` |

For adjacent source characters `x,y`, `multiplier x y` is
`genericMultiplier (x.exponent-y.exponent) (pairParity y x)`.
`IsGenericPair d e` requires `IsGenericParameter` for the four ordered
crossings `(B,C)`, `(A,C)`, `(B,D)`, `(A,D)`, with these same parity arguments.
The imported predicate says that the exponent difference avoids both
`epsilon + 2r + 1` and `-(epsilon + 2r + 1)` for every natural `r`.

The position-character identities and `kFin_le_of_conditions` give the inclusions
that forget one or both original induction conditions. In particular,
`keepFirst d e = [induced d,C,D]` and
`keepSecond d e = [A,B,induced e]` retain exactly one of the conditions.
`mem_firstMoved` and `mem_secondMoved` reinsert a compact Fourier window at
position 1 into `C A B D` and `A C D B`, respectively. They use the published
compact standard-module membership criterion, including its propagation of
compact vanishing to vanishing on the whole group.

## The actual map and the disjoint square

`swapData` constructs the published block Frobenius data for exchanging adjacent
characters in any context. The published `data_swap` has the reverse list
orientation, so it is applied with `c=y,d=x`. The generic multiplier has the
required symmetry. `swap_modulo` rewrites the two source position exponents to
`x.exponent,y.exponent`; the generic recurrence therefore has the exact parameter
`x.exponent-y.exponent+1` required by the block intertwining theorem.
`swap_injective` uses nonvanishing of every generic multiplier mode and the
published Fourier criterion for injectivity.

The data `dataBC`, `dataAC`, `dataBD`, `dataAD` give the path

`A B C D -> A C B D -> C A B D -> C A D B -> C D A B`,

at positions `1,0,2,1`. The data `dataBD'`, `dataAC'` instead give the middle path

`A C B D -> A C D B -> C A D B`.

Both middle paths use the same multipliers on the disjoint pairs at positions
0 and 2. `middle_square` applies the exact published Frobenius commuting square
to identify the resulting vectors in their common standard module.

`rawMap` is the first path composed with the inclusion from the original source
into `expanded d e`. It is a complex-linear map into `expanded e d`, before the
two final induction conditions have been imposed.

## The two Fourier windows

The wrappers `inducedFirst_landing` and `characterFirst_landing` specialize the
proved `RealSwapLandingIntegral.inducedFirst` and its proved mirror to the
chosen generic multipliers. The published even-class and sign-class lemmas
convert the pair parities to the classes in the landing theorem. The recurrence
parameters of the two successive crossings differ by exactly the absolute
weight of the induction block, by the formulas for `chA` and `chB`.

For the `d` window, `first_window_once` starts with source membership in
`keepFirst`. It applies `twoStep_landing_in_stages` to coordinates 0,1,2,
with local positions `1,0` and output position 1. Thus the first two crossings
land in `firstMoved d e = [C,induced d,D]`. `first_window` repeats the induced-first
landing on coordinates 1,2,3 with this retained source condition. The last two
crossings put the `d` window in the final position 2.

For the `e` window, `second_window_once` starts with source membership in
`keepSecond` and uses coordinates 1,2,3. Local character-first positions `0,1`
are ambient positions `1,2`, giving the alternative path through `movedRight`.
Reinserting the condition gives `secondMoved d e = [A,induced e,B]`.
`second_window` applies the character-first landing on coordinates 0,1,2 and
then uses `middle_square` to identify this output with `rawMap`. The final
`e` window is at position 0.

At every use of the slice transfer, the intermediate and output functions are
smooth because they belong to the corresponding actual standard modules.
Their compact Fourier multiplier identities are the published exact block
Frobenius identities. Thus all local landing hypotheses are supplied by proved
results, rather than retained as new assumptions.

`rawMap_mem_target` combines these two compact windows with the final
position-character identity. The compact membership criterion yields the
actual target standard-module condition, and right compact finiteness is
inherited from the raw image.

## Injectivity, intertwining and stages

`rawMap_modulo` composes the four exact intertwining results and the source
inclusion, with error submodule bottom. `rawMap_injective` composes the four
generic injectivity results and injectivity of that inclusion.

`genericMap` corestricts the underlying function of `rawMap` to the actual target.
This leaves every function unchanged. `injective_of_generic` transfers exact
intertwining through that equality of underlying functions and obtains an
injective standard intertwiner. `injective_in_stages` then applies the published
`RealInjectiveIntertwinerExists.in_stages` with both middle ranks equal to 4.
It retains the total-rank equality and `IsGenericPair d e` as its only extra
inputs besides the character data and surrounding lists.

## Provenance

This is internal derived content with no new literature identification. The
construction uses the Library position characters and standard modules,
explicit generic Fourier multipliers, the proved GL3 landing theorem and its
mirror, normalized slice transfer, disjoint Frobenius commutation, and the
proved induction-in-stages theorem. The companion Lean implements the path and
window argument described above. The remaining exceptional GL4 cases are outside
this module's claim.
