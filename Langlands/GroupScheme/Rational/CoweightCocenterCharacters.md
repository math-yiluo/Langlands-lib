# Actual cocenter characters selected by a supplied coweight

Author: Worker 1632.

This internal comparison concerns actual compatible torus maps `i : T → G`,
`t : T → M`, and `j : M → G` with `t ≫ j = i`, over any field `k`.
The groups `G`, `M` and `D` are affine and locally of finite type, and `M`
is connected reductive. The supplied actual root data `P` and `R` describe
`i` and `t` on the unchanged lattices of `T`. A supplied cocharacter `ν`
cuts out the actual `M` roots as precisely the actual `G` roots with zero
integral pairing against `ν`. The map `i` is closed and `T` is split.
The field and three root-index types have independent universes.

The supplied actual derived subgroup `d : D → M` has a compatible split
maximal torus `a : S → D`. The map `t` is maximal in `M`, and the actual
map `φ : S → T` satisfies `groupHom φ ≫ t = a ≫ d`. The supplied actual
root datum `U` describes `a`.

`IsRootDatumOf.map_derived_corootSpan_eq_coweight_zero` identifies the image
of the full integral `U` coroot span under actual postcomposition by `φ`
with the span of all `P` coroots whose roots vanish on this same `ν`.
The published central-complement constructor, applied to `R`, constructs
an actual central split torus whose product with `S` is flat and surjective
onto `T`. The published integral derived-root-datum comparison then maps
the full `U` coroot span onto the full `R` coroot span. Finite actual Weyl
image follows from closed splitness and local finite type. The imported
same-torus coweight comparison identifies the latter span with the claimed
ambient zero-root coroot span. No coroot-span equality is an input.

`characterLattice.cocenterCoweightAnnihilatorEquiv` additionally takes
a semisimple `D`, a supplied commutative fppf quotient `q : M → Q` by the
full actual range of `d`, and splitness of `Q`. Its two remaining structural
inputs are scheme surjectivity of the ordered product `D × T → M` and the
torus property of the entire scheme-theoretic intersection `T ×_M D`.
It constructs an integer-linear equivalence from `X*(Q)` to the submodule
of all actual characters of `T` annihilating those ambient zero-root
coroots. The construction supplies the first theorem's proved span
identity to `cocenterCorootAnnihilatorEquiv`. Its underlying map is actual
precomposition by `t ≫ q`.

`characterLattice.cocenter_coweight_character_comparison` has exactly the
same inputs and proves that this actual pullback is injective, with image
exactly the stated annihilator. Injectivity and both directions of the
image comparison follow from the constructed equivalence and its
surjectivity.

The provenance is composition of the imported proved constructions.
No literature theorem is transcribed. There is no simple-connectedness,
perfectness, algebraic-closure, characteristic, reducedness, finite
root-index, or integral coroot-generation premise. Finite coroot index
in the semisimple derived torus is supplied internally by the published
character comparison. This module preserves `ν` and chooses no root base.
It does not construct the compatible tori or root data, prove either
retained product or intersection premise, choose a splitting extension,
or establish ordinary Galois fixedness. Those inputs remain necessary
for the unconditional Levi cocenter root-model proof.
