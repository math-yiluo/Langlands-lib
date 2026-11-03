# Renard's actual uniformizer subgroup

Author: Worker 454.

This module defines the uniformizer subgroup used in Renard's Cartan
representatives. It uses an actual commutative group scheme `T` over an actual
nonarchimedean local field `F`, with the Library's `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` instances. Neither the
characteristic of `F` nor its residue characteristic is restricted.

`uniformizerSection T` evaluates each actual cocharacter
`c : cocharacterLattice T` at the existing
`SplitTorusValuation.uniformizerUnit F`. Its source is the multiplicative
form of the additive cocharacter group. The input point of the multiplicative
group is obtained from `Gm.affinePointsEquiv`; the output is obtained by
`rationalPoints.map (CommGroupScheme.groupHom c)`. The homomorphism reuses
`CocharacterUniformizer.latticeSection F T`. Its multiplicativity is the
published consequence of `comp_groupHom_zero` and `comp_groupHom_add`.
`uniformizerSection_eq_latticeSection` and `uniformizerSection_apply` are
reflexivity proofs identifying the two homomorphisms and their evaluations,
including for a commutative group scheme not assumed split. Calling it a section of a valuation requires the split-torus
identification, which is not asserted for arbitrary `T`.

For a map `i : T.toGrp ⟶ H` into an actual algebraic group,
`C0 T i` is the range of this homomorphism followed by `rationalPoints.map i`.
`mem_C0` expresses membership as the existence of a cocharacter evaluated
at the uniformizer. In the Cartan application, `T` is the chosen maximal
split torus `S`, `H` is its actual algebraic centralizer `Z`, and `i` is
the factorization `S → Z`. These definitions do not construct the centralizer
scheme or assume a building exists.
`C0_eq_map_CA` identifies this ambient subgroup with the image of the
published intrinsic `CocharacterUniformizer.CA F T`; its proof is the
range-of-a-composite law. `uniformizerSection_naturality` says that mapping
`c(π)` along any actual morphism `f : T → U` gives `(c ≫ f)(π)` for the
same field uniformizer. Its proof is the published evaluation-of-composition
law. This applies in particular to nested split subtori used for standard
Levis; it does not construct their inclusions or compare any compact subgroups.

For a specified set `positiveRoots` of actual torus characters,
`nonnegativeCocharacters T positiveRoots` consists of the cocharacters
`c` with `latticePairing T a c ≥ 0` for every `a` in that set.
`C0Plus T i positiveRoots` is their image under the same uniformizer
evaluation and point map. `mem_C0Plus` gives the defining formula, and
`C0Plus_subset_C0` proves that the positive set lies in the uniformizer
subgroup. In the Cartan application, the set is the Library's
`positiveRelativeRoots (S → G) ν`, for the chosen positive system.
An arbitrary supplied set of characters is not asserted to be a positive
relative root system.

`uniformizerSection_splitTorus` identifies the evaluation, by reflexivity,
with the existing `SplitTorusValuation.cocharacterPoints` on a coordinate
split torus. The published
`SplitTorusValuation.valuation_cocharacterPoints_uniformizer` then states
that the valuation of `c(π)` is `c`. In particular the convention is positive:
the order of the chosen uniformizer is `+1`, and nonnegative pairings
give nonnegative root orders.

## Original sources and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
V.2.5 (printed page 107, PDF page 113) defines `C_A` as the image of
cocharacters at a uniformizer; V.3.21 (printed page 116, PDF page 122)
defines the positive cone by nonnegative root orders; V.3.23 (printed
page 117, PDF page 123) uses `C_A^+`; V.5.1(4) (printed page 122,
PDF page 128) specializes to `C_0^+`. The homomorphism packaging and the
membership and naturality lemmas are internal implementations of those definitions.

The positive valuation convention also agrees with Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), §2.5(b), as corrected by
*Corrections and additions*, 1 November 2024, PDF page 24. Their registered
source IDs are `kaletha-prasad-2023-bruhat-tits-new-approach` and
`kaletha-prasad-2024-corrections`; their SHA256 values are respectively
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` and
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

## Scope

Only the actual uniformizer subgroup and its positive part are constructed.
No dominant-cocharacter parametrization of general reductive double cosets
is asserted. The actual centralizer image lattice, its finite-index
comparison with the split torus, the finite representative choices, the
comparison with the centralizer's dominant cone, and the parahoric and
maximal-compact Cartan bijections remain separate obligations.
