# Hopf algebras of central extensions of split tori by diagonalizable groups

This module is part of the proof that extensions of groups of multiplicative
type over a field are of multiplicative type (`multiplicativeTypeFieldExtension`
in `Langlands.GroupScheme.Torus.MultiplicativeTypeFieldExtensionProof`). It
generalizes [`CentralTorusExtensionHopf`](CentralTorusExtensionHopf.md).
There the central subgroup is a split torus with character lattice `ℤ^J`.
Here it is an arbitrary diagonalizable group `D(N)`, for any commutative group
`N`, torsion included.

Let `K` be a field and `A` a commutative `K`-Hopf algebra with bialgebra maps
`φ : K[ℤ^I] →ₐc A` and `π : A →ₐc K[N]`. Geometrically:

* `Spec A = E` is a group;
* `Spec φ` is a quotient map `E → T` onto the split torus `T = 𝔾_m^I`;
* `Spec π` is a central closed subgroup `D(N)` of `E`, with `T = E / D(N)`.

Under these hypotheses, the module proves the following. The group-like
elements of `A` span `A`. If `I` is finite and `N` is finitely generated, the
group of group-like elements is finitely generated. Hence `E` is
diagonalizable.

## Contents copied from `CentralTorusExtensionHopf`

The declarations from `IsCentralExtension` through `exists_degree_eq` are
copied from [`CentralTorusExtensionHopf`](CentralTorusExtensionHopf.md), with
the lattice `J → ℤ` replaced by an arbitrary commutative group `N`. Their
proofs use only the `N`-grading
([`GroupAlgebraCoaction`](GroupAlgebraCoaction.md)) and never use that `N` is
free. In this module they live in the namespace
`Langlands.CentralDiagonalizableExtensionHopf`.

* `IsCentralExtension φ π`: a structure with five fields.
  - `injective`: `φ` is injective (the quotient map is faithfully flat).
  - `surjective`: `π` is surjective (`D(N) → E` is a closed immersion).
  - `comp_eq`: `π ∘ φ = algebraMap ∘ ε` (`D(N)` lies in the kernel).
  - `isCentral`: `π` is central (`GroupAlgebraCoaction.IsCentral`).
  - `invariants`: every element of degree `0` lies in the image of `φ`
    (`T = E/D(N)`).
* `map_mem_grade_zero`: `φ b` has degree `0`.
* `exists_mem_grade_counit_eq_one`: if `π` is surjective, every degree `n`
  has an element of counit one.
* `exists_unit_mem_grade` (for finite `I`): every homogeneous component
  `grade π n` contains a unit of `A`.
  - `grade π n` is an invertible `K[ℤ^I]`-submodule: the invariants give
    `grade π n · grade π (-n) ≤ K[ℤ^I]`, and the antipode
    (`one_mem_grade_neg_mul_grade`) gives the reverse inclusion.
  - The Picard group of `K[ℤ^I]` is trivial
    (`IntLatticeAlgebra.subsingleton_pic`). Hence the component is the span of
    a unit.
* `divide`, `map_divide`, `map_divide_mul`, `map_proj_proj`,
  `comul_eq_map_mul`, `map_map_injective`: for a unit `u` of degree `n`,
  `Δ u = (φ ⊗ φ) f · (u ⊗ u)` for some `f`. This uses centrality
  (`IsCentral.comul_of_mem`).
* `exists_isGroupLikeElem_smul`: a unit `u` of degree `n` has a scalar
  multiple that is group-like.
  - The element `f` is a unit of `K[ℤ^I] ⊗ K[ℤ^I] ≅ K[ℤ^I][ℤ^I]`, so it is a
    monomial (`IntLatticeAlgebra.exists_eq_single_of_isUnit`).
  - The counit identities force the monomial to be `d ⊗ 1` with
    `d · ε(u) = 1`. Then `d • u` is group-like.
  - Only the quotient lattice `ℤ^I`, never `N`, needs to be free here.
* `mem_grade_of_isGroupLikeElem`, `eq_of_mem_grade`, `exists_map_eq_single`,
  `degree`, `map_eq_single_degree`, `mem_grade_degree`,
  `degree_eq_of_mem_grade`: the degree homomorphism
  `Additive (GroupLike K A) →+ N`, `g ↦ n` with `π g = Xⁿ`.
* `iota`, `iota_val`, `degree_iota`, `isGroupLikeElem_of_map`: the
  homomorphism `ℤ^I →+ Additive (GroupLike K A)`, `m ↦ φ(Xᵐ)`, with values of
  degree `0`. If `φ b` is group-like then so is `b`.
* `exists_degree_eq`: every `n : N` is the degree of a group-like element.

## New results

* `exists_isGroupLikeElem_mem_grade` (finite `I`): every component
  `grade π n` contains a group-like element. Apply `exists_unit_mem_grade`,
  then `exists_isGroupLikeElem_smul`.
* `grade_zero_le_span`: the degree-zero component lies in the span of the
  group-like elements.
  - By `invariants`, an element of degree `0` is `φ b`.
  - `K[ℤ^I]` is spanned by its group-like elements
    (`AddMonoidAlgebra.span_isGroupLikeElem`).
  - `φ` maps group-like elements to group-like elements.
* `span_isGroupLikeElem` (finite `I`): the group-like elements span `A`.
  Apply `GroupAlgebraCoaction.span_isGroupLikeElem_eq_top_of_forall_grade`
  from [`CocommutativeGradedGroupLike`](CocommutativeGradedGroupLike.md) to
  the two previous results.
* `ker_degree_le_range_iota`: a group-like element `g` of degree `0` is
  `iota φ m` for some `m`.
  - `g = φ b` with `b` group-like (`isGroupLikeElem_of_map`).
  - The group-like elements of `K[ℤ^I]` are the monomials `Xᵐ`
    (`AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one`).
* `addGroupFG` (finite `I`, finitely generated `N`): the group
  `Additive (GroupLike K A)` is finitely generated.
  - View `degree` and `iota` as `ℤ`-linear maps.
  - `degree` is surjective (`exists_degree_eq`).
  - Its kernel is the range of `iota`: `ker_degree_le_range_iota` and
    `degree_iota`. That range is the image of the finite `ℤ`-module `ℤ^I`.
  - Mathlib's `Submodule.fg_of_fg_map_of_fg_inf_ker` gives finite generation
    of the whole group as a `ℤ`-module, hence as a group
    (`Module.Finite.iff_addGroup_fg`).

## Provenance

The copied part is internal to this project, from
[`CentralTorusExtensionHopf`](CentralTorusExtensionHopf.md); its Markdown
explains the route. The new results are internal as well. The geometric
meaning is SGA 3, Exposé IX, Proposition 8.2 (ii) over a field, after
centrality is known: an extension of a split torus by a diagonalizable group is
diagonalizable. The source proof uses a Galois-cohomology argument. This module
instead uses that the Picard group of `K[ℤ^I]` is trivial and that every unit
of `K[ℤ^I ⊕ ℤ^I]` is a scalar multiple of a monomial. No statement of this module is
attributed to the source.
