# Enlarging an essentially smooth approximation by a power of a unit

`Langlands.CommutativeAlgebra.Popescu.artinianSmoothEnlargement` proves
`ArtinianSmoothEnlargementStatement.{u}`. The construction follows Stacks Project,
*Smoothing Ring Maps*, Lemma 11.3, printed pages 27–28 of the registered
`smoothing.pdf`. The case where the residue of the unit belongs to the base residue
field is included in the algebraic case. [Stacks Project, Tag 07FI](https://stacks.math.columbia.edu/tag/07FI)

Write `R = localTruncation 𝔭 n`, `L = localTruncation q n` and `ℓ` for the image of
`l` in `L`. The truncation lemmas give the local Artinian structure of `L`, and
`l ∉ q` makes `ℓ` a unit. The given map `ψ` sets the `D`-algebra structure on `L`.
The proof uses the residue field map induced by this local homomorphism.

- If the residue of `ℓ` is transcendental over the residue field of `D`, the inverse
  image of the maximal ideal of `L` under evaluation at `ℓ` consists of the
  polynomials whose coefficients lie in the maximal ideal of `D`. Localize `D[X]` at
  this prime to obtain `D'`. Its maximal ideal is extended from `D` and is nilpotent,
  so the Noetherian local ring `D'` is Artinian. Evaluation extends to `D'`, and the
  image of `X` gives exponent one. The localization is formally smooth and
  essentially of finite type over `D`.
- If the residue is algebraic, some `p`-power `β` of it is separable. Lift its
  minimal polynomial to a monic polynomial `H` over `D`, and use Hensel's lemma in
  `L` to find a root of `H` congruent to the corresponding power of `ℓ`. Take
  `D' = AdjoinRoot H` and send its distinguished root to this Hensel root. The
  irreducible reduction of `H` gives a local ring with maximal ideal extended from
  `D`. The monic power basis makes `D'` finite and hence Artinian. The derivative of
  `H` evaluates to a unit at the Hensel root by separability. The local map into
  `L` reflects this unit back to `D'`. Consequently inverting the derivative in
  `D'` leaves its algebra isomorphism type unchanged, and the standard étale
  presentation for `H` and its derivative gives an étale `D`-algebra. The published
  `Enlargement.exists_pth_power_preimage` applies to the congruence of the root and
  the power of `ℓ` and produces a positive exponent and a preimage.

In both cases the maximal ideal of `D'` is extended from that of `D`, and the
resulting homomorphism sends it into the maximal ideal of `L`. This proves locality.
`Enlargement.flat_of_map_maximalIdeal` then gives flatness from the flatness of `ψ`.
The `D`-algebra homomorphism condition gives the required equality with `ψ` on `D`.

Essential smoothness gives formal smoothness and essential finite type, and both
properties compose along `R → D → D'`. To recover the localization witnesses for
the two essential smoothness conclusions, the proof uses the fact that both `D`
and `R` are Noetherian. A local algebra essentially of finite type over either base
is the localization of a finitely presented subalgebra at the inverse image of its
maximal ideal. Formal smoothness puts that prime in the smooth locus, so a smooth
basic open containing the prime gives a smooth algebra of which `D'` is a
localization.
