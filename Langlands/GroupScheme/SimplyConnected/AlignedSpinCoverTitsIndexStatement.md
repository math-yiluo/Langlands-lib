# Index comparisons for an aligned spin cover

Author: Worker 64 (interface agreed with Worker 73).

`Langlands.GroupScheme.AlignedSpinCoverTitsIndexStatement.{u}` is an
**unproved** statement. It is the index-comparison half of
`ClassicalTypeDSpinPresentationStatement`. The theorem
`classicalTypeDSpinPresentation_of_aligned` derives that statement from
this one and from `ClassicalTypeDAlignedSpinCoverStatement`. The
statement holds over every field, in every characteristic, for every
absolute rank `n ≥ 4`.

## Hypotheses

The first block repeats the hypotheses of
`ClassicalTypeDSpinPresentationStatement` word for word:

- `K : Type u` is a field and `G` is an affine, locally finite type group
  scheme over `Spec K` with an actual index `d : TitsIndexData G`;
- `e : d.Vertex ≃ Fin n` with `4 ≤ n` preserves every Cartan entry of
  `CartanMatrix.D n`;
- `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`;
- for every `γ : K^s ≃ₐ[K] K^s` and every vertex `a` with
  `(e a).val + 2 < n`, `d.star γ a = a`. So the full star action fixes
  every vertex outside the two fork tips.

The second block supplies an arbitrary spin presentation:

- a central finite dimensional division algebra `D : Type u` over `K`
  and natural numbers `degree`, `m` with `0 < degree`,
  `Module.finrank K D = degree ^ 2` and `m * degree = 2 * n`;
- `σ : Quaternionic.FirstKindInvolution K D` with
  `Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2`
  (natural-number division);
- `q : σ.QuadraticForms (Fin m)` with `σ.IsNondegenerateQuadratic q`;
- `π : G ⟶ σ.isometryGroup q` with `σ.IsSpinCover q π`;
- **alignment**: for every vertex `v` with `(e v).val = 0`,
  `d.FundamentalWeightTrivialOnKernel v π`.

The objects `QuadraticForms`, `IsNondegenerateQuadratic`,
`quadraticWittIndex`, `isometryGroup` and `IsSpinCover` are the ones used
by `ClassicalTypeDSpinPresentationStatement`. The symmetric-dimension
condition is Tits's type-1 convention. In characteristic 2 it holds for
every first-kind involution, symplectic ones included, because there
`Sym(σ) = Skew(σ)`. That case is the quadratic-pair case, and the
statement covers it.

## Conclusions

- `σ.quadraticWittIndex q = splitRank G`;
- for every vertex `a` with `(e a).val + 2 < n`, `a ∈ d.distinguishedVertices`
  holds exactly when `(e a).val + 1 = j * degree` for some natural `j` with
  `0 < j ≤ σ.quadraticWittIndex q`.

No formula for the two fork vertices is asserted.

## Why the alignment hypothesis is needed

`FundamentalWeightTrivialOnKernel` says that the fundamental weight at
`v` is trivial on `ker π ∩ T` over `K^s`, read through all `K^s`-scheme
points. In characteristic 2 that kernel is the infinitesimal `μ₂`, so a
check on `K^s`-points alone would be vacuous. The vector weight is
trivial on `ker(Spin → SO)` and the half-spin weights are not (KMRT
§27.B). For `n ≥ 5`, vertex `0` is the only end vertex outside the fork,
and every spin cover is aligned there (mathematical remark, not used in
Lean). For `D₄` the star action fixes vertex `0`, but triality can make
vertex `2` or `3` the vector vertex of a given spin cover. For such a
cover the vertex-0 comparison can fail. For example, let `q₀ = H ⊥ φ`
over `K` with `H` a hyperbolic plane and `φ` an anisotropic
six-dimensional Albert form, and number `Spin(q₀)` so that the vector
vertex of `q₀` is vertex `0`. That vertex is distinguished. By
triality (KMRT (44.7)–(44.8)) the same group is also a spin cover of a
form over a degree-4 division algebra, Brauer-equivalent to a simple
component of the even Clifford algebra of `q₀`. The vector vertex of
that cover is a fork tip. For that cover
the comparison at vertex `0` would assert `1 = 4 j`. The alignment
hypothesis excludes such covers.

## Original sources and derived formulation

- J. Tits, *Classification of algebraic semisimple groups* (1966),
  Table II explanations, printed pp.54–55 / PDF pp.59–60, and the entries
  `¹D_n`, `²D_n`, printed pp.56–57 / PDF pp.61–62. There `d` is the
  degree of the division algebra, `m = 2n/d`, `r` the relative rank and
  form index, and the distinguished vertices on the chain are
  `d, 2d, …, rd`. Registered source
  `tits-1966-classification-algebraic-semisimple`, PDF SHA-256
  `962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.
- J. Tits, *Formes quadratiques, groupes orthogonaux et algèbres de
  Clifford* (1968): §2.1, printed p.20 / PDF p.3 (type-1 involutions);
  §§2.2–2.3, printed pp.21–22 / PDF pp.4–5 (quadratic forms over
  `(D, σ)`, polar form, nondegeneracy); §3, Proposition 6, printed p.30 /
  PDF p.13 (isometry groups); §4.4, printed p.39 / PDF p.22 (`Spin q`
  covers `SU(q)⁰`). Registered source
  `tits-1968-formes-quadratiques-clifford`, PDF SHA-256
  `f8da4ecd4aae5bd5bbb3bc48873f285d7ccb058d771a5e9be855c867e391c782`.
- M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol, *The Book of
  Involutions* (1998), §27.B, type `D_n`, printed p.379 / PDF p.402
  (the vector character `λ` of the centre factors through `O⁺`);
  (44.7)–(44.8), printed p.562 / PDF p.585 (`Spin(T) ≅ Spin(A)` for
  types `¹D₄`, `²D₄`); §44.A, printed p.563 / PDF p.586 (Tits algebras
  for `D₄`). Registered
  source `knus-merkurjev-rost-tignol-1998-book-of-involutions`, PDF
  SHA-256
  `e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`.

This is a derived formulation. Tits describes the rational points of
representatives of strict isogeny classes and their indices. He does not
state this Lean group-scheme proposition. The proof successor must
compare the Witt index with the actual split rank of `G` through the
central isogeny, and identify the actual distinguished vertices of `d`
with the restricted roots of `O(q)⁰`, using the alignment to fix the
vector vertex.
