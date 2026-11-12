# Local constancy of the finite determinant factor of every Hecke character

Author: Worker 5136.

This internal module proves that, for every Hecke character `χ` of a number
field `F` and every rank `n`, the map `d ↦ χ(det d)` on the finite adelic
matrix group `GL_n(𝔸_F^∞)` has an open kernel and is locally constant. No
finite-order hypothesis is used. The Library's finite-order development
(`Langlands.Automorphic.SmoothDeterminantMultiplier`) obtains the same local
constancy from `χ.HasFiniteOrder`; this module removes that hypothesis for the
finite factor.

`finiteAdelicGL_totallyDisconnectedSpace` shows that `FiniteAdelicGL F n` is
totally disconnected: the matrix of a unit determines the unit, the entry map
is continuous and injective, and the finite adele ring is totally disconnected
(`finiteAdeles_totallyDisconnectedSpace`).

`finiteAdelicGL_nonarchimedeanGroup` is van Dantzig's theorem for this group.
The group is Hausdorff, locally compact (an existing instance) and totally
disconnected, so `Langlands.Topology.isLocallyProfinite_of_mathlib` makes it
locally profinite. The Library's
`Langlands.Topology.LocallyProfiniteProof.vanDantzig` then gives an open
subgroup inside every neighbourhood of the identity. This is the definition of
`NonarchimedeanGroup`.

`isLocallyConstant_of_isOpen_ker` is the general fact that a homomorphism to
`ℂˣ` with open kernel is locally constant: the fibre through `u` is the
translate `u · ker`.

`HeckeCharacter.isOpen_ker_finiteDeterminant` applies the Library's
`Langlands.isOpen_ker_of_continuous_complex_character` to the continuous
homomorphism `χ.adelicDeterminant n ∘ AdelicGL.ofFinite F n`. That result says
a continuous homomorphism from a nonarchimedean group to `ℂˣ` has open kernel,
because a small neighbourhood of `1` in `ℂˣ` contains no nontrivial subgroup.
`isLocallyConstant_finiteDeterminant` and its complex-valued form
`isLocallyConstant_finiteDeterminant_val` follow.

Provenance: this is a standard internal argument (van Dantzig's theorem and the
"no small subgroups" property of `ℂˣ`). It is an ingredient for
Henniart (2000), §2.2, which twists by arbitrary quasicharacters. No
correspondence with a particular passage of the literature is claimed.
