# The vector weights of an aligned type-`D` spin cover

Author: Worker 73.

Module `Langlands.GroupScheme.SimplyConnected.SpinCoverVectorWeightsStatement`, namespace
`Langlands.GroupScheme`. It contains one `Prop`-valued definition,
`SpinCoverVectorWeightsStatement`, with universe parameter `u`, and proves nothing. Its
proof is a separate task. It is a prerequisite of the published
[`AlignedSpinCoverTitsIndexStatement`](AlignedSpinCoverTitsIndexStatement.md) and has the
same hypotheses, except the star-action hypothesis, which is not needed here.

## Hypotheses

The variables and hypotheses are those of `AlignedSpinCoverTitsIndexStatement`, without
the star-action hypothesis.

* `K` is an arbitrary field.
* `G` is an affine group scheme of locally finite type over `Spec K`, with actual Tits
  index data `d : TitsIndexData G` (module `Reductive.TitsIndex`) and a numbering
  `e : d.Vertex ≃ Fin n` with `4 ≤ n`.
* `G` is simply connected (`IsSimplyConnected`) and absolutely almost simple
  (`IsAbsolutelyAlmostSimple`).
* `d.cartan a b = CartanMatrix.D n (e a) (e b)` for all vertices. In Mathlib's numbering
  of `D_n`, the vertices `0, …, n-3` form a chain. The vertex `n-3` is joined to both fork
  vertices `n-2` and `n-1`, and the two fork vertices are not joined.
* `D : Type u` is a finite-dimensional central division `K`-algebra with
  `finrank K D = degree ^ 2` and `0 < degree`, and `m * degree = 2 * n`.
* `σ` is an involution of the first kind with
  `finrank K σ.symmetricSubspace = degree * (degree + 1) / 2`.
* `q : σ.QuadraticForms (Fin m)` is nondegenerate.
* `π : G ⟶ σ.isometryGroup q` satisfies `σ.IsSpinCover q π`.
* For the vertex `v` numbered `0`, `d.FundamentalWeightTrivialOnKernel v π` holds (module
  `SimplyConnected.SpinCoverFundamentalWeight`). That is, the fundamental weight of `v` is
  trivial on `ker π` in the pinning torus over `K^s`. This makes the vertex numbered `0`
  the vector vertex.

## Conclusion

Write `T_s` for the base change to `K^s = SeparableClosure K` of the pinning torus
`d.pinning.torus`. There are characters `ε_0, …, ε_{n-1}` of `T_s`, elements of the
published `characterLattice T_s`, which is also the character lattice of the pinning's
root datum. They satisfy the following four properties.

1. **Simple roots, chain and first fork vertex.** If `(e a).val + 1 < n`, the simple root
   of `a` is `ε_{e a} − ε_{e a + 1}`. The root is the published
   `d.pinning.rootDatum.root a`.
2. **Simple root, second fork vertex.** If `(e a).val + 1 = n`, the simple root of `a` is
   `ε_{n-2} + ε_{n-1}`.
3. **Roots.** For all `i ≠ j` in `Fin n` and all signs `s, t ∈ ℤˣ`, some root index `α`
   has root `s ε_i + t ε_j`.
4. **Vector weights with multiplicity `degree`.** Let `S = d.splitTorus` be the maximal
   split torus of the index, with `d.torusMap : S ⟶ T` and `d.splitInclusion : S ⟶ G`.
   For a character `ε` of `T_s`, write `ε|_S` for the character of `S` obtained by
   composing `ε` with the base change of `d.torusMap` and descending along the published
   equivalence `characterLattice.baseChangeEquiv` for the split torus `S`. This is the
   recipe of the published `absoluteRootRestriction`, applied to `ε` instead of a root.
   Then, for every cocharacter `ν` of `S` and every integer `c`, the number of pairs
   `(i, s) ∈ Fin n × ℤˣ` with `s · ⟨ε_i|_S, ν⟩ = c` equals
   `degree * finrank D (σ.cocharacterWeightSpace q (ν ≫ d.splitInclusion ≫ π) c)`.

The weight spaces are those of
[`cocharacterWeightSpace`](../Quaternionic/CocharacterWeightSpace.md).

Properties 1 and 2 say that the numbered base is the standard base
`ε_0 − ε_1, …, ε_{n-2} − ε_{n-1}, ε_{n-2} + ε_{n-1}` of a root system of type `D_n`. The
signs are normalized so that the fork vertex numbered `n-2` carries `ε_{n-2} − ε_{n-1}`.
Property 3 lists the roots `±ε_i ± ε_j`.

Property 4 is the multiplicity statement. Over `K^s` the weights of `T_s` on
`D^m ⊗_K K^s` are `±ε_0, …, ±ε_{n-1}`, each with multiplicity `degree`. Consider a
`K`-rational cocharacter `ν` of `S` and its weight-`c` space `W_c ⊆ D^m`, a left
`D`-subspace. Its `K`-dimension is `degree² · finrank_D W_c`. After base change it becomes
the sum of the `T_s`-weight spaces of the weights `s ε_i` with `s ⟨ε_i|_S, ν⟩ = c`, each of
`K^s`-dimension `degree`. Dividing by `degree` gives the displayed identity. It is stated
only for cocharacters of the split torus `S`, so that only the `K`-rational weight spaces
of [`cocharacterWeightSpace`](../Quaternionic/CocharacterWeightSpace.md) occur.

## Role of the hypotheses

The alignment hypothesis is used for `n = 4`. There the three end vertices of the diagram
are permuted by triality, and only the alignment identifies the vertex numbered `0` with
the vector vertex `ε_0 − ε_1`. The other end vertices have half-spin fundamental weights,
which are nontrivial on `ker π`. For `n ≥ 5` the Cartan matrix alone determines the
vector vertex.

The degree and symmetric-subspace hypotheses fix the type of the classical presentation.
`D ⊗_K K^s ≅ M_degree(K^s)` turns `D^m ⊗_K K^s` into `degree` copies of the natural
`2n`-dimensional representation of `SO_{2n}`.

## Provenance

This statement is derived from the literature.

* Tits 1966, Table II, entries `¹D_n` and `²D_n` (source
  `tits-1966-classification-algebraic-semisimple`, printed pp. 56–57, PDF pp. 61–62),
  with the numbering of vertices of Table I. The groups `SO(D, h)` with `D` of degree `d`
  have distinguished vertices `d, 2d, …, rd`. This is what the weights above give after
  restriction to a maximal split torus.
* Knus–Merkurjev–Rost–Tignol, §27.B, type `D_n` (source
  `knus-merkurjev-rost-tignol-1998-book-of-involutions`, printed p. 379, PDF p. 402),
  describes the centre of `Spin(A, σ, f)`. Its vector character is the one that factors
  through `O⁺`. This is the content of the alignment hypothesis, as in the published
  `FundamentalWeightTrivialOnKernel`.

The weights `±ε_i` of the natural representation and the standard base of `D_n` are the
classical description of the even orthogonal group. The formulation through the Library's
`TitsIndexData`, its pinning root datum, `absoluteRootRestriction`-style descent and the
cocharacter weight spaces is new.
