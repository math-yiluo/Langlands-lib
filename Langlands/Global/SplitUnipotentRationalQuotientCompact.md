# Compactness of `U(F) \ U(𝔸_F)` for split unipotent groups

Author: Worker 1179. Part of task 40747bb3 (finite volume of `G(F) \ G(𝔸_F)¹`), with
Worker 235.

This module proves the Library proposition `UnipotentRationalQuotientCompactStatement`
(`Langlands/Global/TriangularRationalQuotientCompact.lean`) from two other Library
propositions:

- `PerfectFieldUnipotentSplitStatement`
  (`Langlands/GroupScheme/Unipotent/PerfectFieldSplitStatement.lean`): over a perfect field,
  every smooth connected unipotent affine group scheme is split unipotent
  (`RelativeRoot.IsSplitUnipotent`);
- `SplitUnipotentAffineTorsorStatement`
  (`Langlands/GroupScheme/SplitUnipotentAffineTorsorStatement.lean`): a flat, surjective,
  quasi-compact torsor over an affine scheme under a smooth affine split unipotent group has a
  section.

The main theorem is `unipotentRationalQuotientCompact_of_split`. Neither input proposition is
proved here, so the conclusion remains conditional on them. The Library already derives
`UnipotentRationalQuotientCompactStatement` from `UnipotentTriangularCoordinatesStatement`
(`unipotentRationalQuotientCompact_of_triangularCoordinates`). This module gives a second
route that avoids triangular coordinates.

Notation is as in `TriangularRationalQuotientCompact.md`. `F` is a number field,
`AdelicGroupPoints F G` is the group `G(𝔸_F)` with the Library's topology,
`rationalSubgroup F G` is the image of `G(F)` under `rational F G`, and
`RationalQuotient F G` is the coset space `G(F) \ G(𝔸_F)`.

## Split series

`RelativeRoot.HasSplitSeries n H` (`Langlands/GroupScheme/Rational/RootSubgroupStructureStatement.lean`)
is defined by recursion on `n`:

- for `n = 0`, the range of the identity of `H` is the trivial subgroup functor, so `H` is
  trivial on every test scheme;
- for `n + 1`, there are a closed subgroup `j : K → H` with `K` smooth and connected, its
  range normal, and a homomorphism `q : H → V` that is an fppf quotient by the range of `j`
  (`RelativeRoot.IsFppfQuotient`: `q` is flat, surjective and locally of finite
  presentation, and the range of `kernelι q` equals the range of `j`), with `V` a vector
  group of dimension one and `HasSplitSeries n K`.

`IsSplitUnipotent H` means `HasSplitSeries n H` for some `n`.

## The covering property

- `HasCompactRationalCover G`: some compact set `C ⊆ G(𝔸_F)` meets every rational coset, so
  every `x ∈ G(𝔸_F)` has some `y ∈ G(F)` with `y x ∈ C`. This is the conclusion of the
  Library's `exists_isCompact_rational_mul_mem`, written as a definition.
- `compactSpace_rationalQuotient_of_hasCompactRationalCover`: the covering property makes
  `RationalQuotient F G` compact. The image of `C` under the continuous quotient map is
  compact and is all of the quotient. The proof is the one in the Library for groups with
  triangular coordinates.
- `HasCompactRationalCover.of_iso e`: the property transfers along an isomorphism
  `e : G ≅ H` of group schemes. One takes the image of `C` under `e⁻¹`, which is continuous
  (`continuous_affinePointsTarget`). Rational points correspond under `e⁻¹`
  (`rational_naturality`).

## Vector groups

- `isAffine_vectorGroup`: the standard vector group `𝔾ₐⁿ`
  (`VectorGroup.groupScheme (CommRingCat.of F) n`) is affine, being the spectrum of
  `F[X₀, …, X_{n-1}]`.
- `hasTriangularCoordinates_vectorGroup`: `𝔾ₐⁿ` has triangular coordinates in the sense of
  `HasTriangularCoordinates`, with the coordinate functions
  `VectorGroup.coordinateSection` and all correction polynomials zero. The coordinate ring is
  identified with `F[X₀, …, X_{n-1}]` by `spectrumCoordinateAlgEquiv`, and this identification
  sends the `i`-th coordinate function to `X_i`. So `MvPolynomial.aeval` of the coordinates is
  the inverse of that algebra isomorphism and is bijective. The coordinates are additive on
  points by `VectorGroup.coordinates_mul`.
- `hasCompactRationalCover_vectorGroup`: `𝔾ₐⁿ` has the covering property, by the Library's
  `exists_isCompact_rational_mul_mem`.
- `hasCompactRationalCover_of_isVectorGroupOfDimension`: every group `V` with
  `IsVectorGroupOfDimension V n` has the covering property. The Library isomorphism
  `IsVectorGroupOfDimension.iso` identifies `V` with `𝔾ₐⁿ`, and `of_iso` transfers the
  property.

## The fibration step

`hasCompactRationalCover_of_section` proves the following. Let `H` be affine, `j : K → H`
and `q : H → V` homomorphisms with the range of `kernelι q` equal to the range of `j`, and
`s : V → H` a morphism of schemes with `q ∘ s = id`. If `K` and `V` have the covering
property with compact sets `C_K` and `C_V`, then `H` has it with the compact set
`j(C_K) · s(C_V)`.

*Proof.* The set is compact as a product of continuous images of compact sets
(`continuous_affinePointsTarget`, `continuous_affinePointPostcomp`). Let `h ∈ H(𝔸_F)`.

1. Choose `y_V ∈ V(F)` with `c = y_V q(h) ∈ C_V`.
2. Put `g = s(y_V)`, a rational point of `H` with `q(g) = y_V`. Also `q(s(c)) = c`.
3. The point `h' = g h s(c)⁻¹` satisfies `q(h') = y_V q(h) c⁻¹ = 1`. By
   `mem_range_kernelι_iff` and the hypothesis on ranges, `h' = j(k)` for some `k ∈ K(𝔸_F)`.
4. Choose `δ ∈ K(F)` with `δ k ∈ C_K`. Then `j(δ) g` is rational, and
   `j(δ) g h = j(δ k) s(c)` lies in `j(C_K) · s(C_V)`.

The section `s` is only a morphism of schemes, not a homomorphism. The proof uses only that
`s` maps rational points to rational points and that `q ∘ s = id`.

## Induction along a split series

`hasCompactRationalCover_of_hasSplitSeries htor n` proves that, given
`SplitUnipotentAffineTorsorStatement`, every group `H` over `F` that is affine over the base
(`IsAffineHom H.X.hom`) and has `HasSplitSeries n H` has the covering property. The proof is
by induction on `n`.

- For `n = 0`, every adelic point of `H` is `1`, so `C = {1}` works.
- For `n + 1`, unpack the series into `j : K → H`, `q : H → V` and `HasSplitSeries n K`.
  `K` is affine over the base because `j` is a closed immersion
  (`HomogeneousQuotient.affine_subgroup_of_closed`). `V` is affine over the base by
  `IsVectorGroupOfDimension.isAffineHom`. The Library theorem
  `HomogeneousQuotient.fppf_section_of_split_unipotent_torsors` turns the torsor statement
  into a section `s` of `q`. Here `K` is smooth, closed in `H` and split unipotent. The
  induction hypothesis covers `K`, and the vector-group lemma covers `V`. The fibration step
  then covers `H`.

## Main results

- `unipotentRationalQuotientCompact_of_split hsplit htor`: the two input propositions imply
  `UnipotentRationalQuotientCompactStatement`. Let `U` be a smooth connected unipotent
  affine group scheme over a number field `F`. Number fields have characteristic zero and
  are therefore perfect, so `hsplit` makes `U` split unipotent. The induction gives the
  covering property, and the covering property gives compactness. The hypothesis
  `LocallyOfFiniteType U.X.hom` of the statement is not used.
- `exists_isCompact_rational_mul_mem_of_split hsplit htor F U`: the covering form of the
  same result, `HasCompactRationalCover U`, under the same hypotheses on `U` without the
  finite-type assumption.

## Provenance

The statement `UnipotentRationalQuotientCompactStatement` is already in the Library; this
module adds no new statement about unipotent groups beyond the auxiliary definition
`HasCompactRationalCover`. The proof is internal. The induction along a composition series
whose quotients are `𝔾ₐ` is the usual way to reduce compactness of `U(F) \ U(𝔸_F)` to the
compactness of `F \ 𝔸_F`. Here the existence of scheme sections of the quotient maps is
taken from the Library proposition `SplitUnipotentAffineTorsorStatement`, and the
compactness for `𝔾ₐⁿ` comes from the Library's triangular-coordinates theorem
`exists_isCompact_rational_mul_mem`.
