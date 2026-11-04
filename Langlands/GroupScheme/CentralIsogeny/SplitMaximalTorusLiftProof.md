# Split maximal tori lift through central isogenies

Author: Worker 1437. The proof uses contributions by Workers 1358, 1384,
1482 and 1508, as described below.

`Langlands.GroupScheme.centralIsogenySplitMaximalTorusLift` proves the
published proposition
`Langlands.GroupScheme.CentralIsogenySplitMaximalTorusLiftStatement.{u}`.
For any field `k : Type u`, connected reductive group schemes `G` and
`H` over `Spec k`, central isogeny `π : G → H`, and split maximal torus
`i : S → H`, it supplies a commutative group scheme `T`, a split
maximal torus `j : T → G`, and a homomorphism `f : T → S` satisfying
`j ≫ π = groupHom(f) ≫ i`. Maximality is among all closed tori.

The statement retains the full scheme-theoretic central kernel. It
allows imperfect fields and every characteristic; it adds no
smoothness or separability requirement on the isogeny or its kernel.
The universe `u` is arbitrary.

The implemented proof composes the following constructions.

1. Worker 1384's `IsCentralIsogeny.exists_pow_eq_one_kernel` in
   `CentralIsogeny.KernelTorsion` gives a positive integer `N` killing
   every point of the actual kernel over every test scheme. Centrality
   makes this finite kernel commutative. Its coordinate Hopf algebra is
   commutative, cocommutative and finite-dimensional; a norm argument in
   convolution rings proves that its dimension kills its points.
   Transport through the actual affine Hopf-coordinate isomorphism and
   precomposition gives the assertion on arbitrary test schemes.
2. Worker 1508's `IsCentralIsogeny.exists_comp_eq_multiplication_comp`
   in `CentralIsogeny.PowerLift` gives a map `a : S → G` with
   `a ≫ π = [2N] ≫ i`. In the inverse image of `S`, commutators lie
   in the central kernel. Its exponent makes the `2N`-th power
   multiplicative and trivial on the kernel of the projection to `S`;
   fpqc homomorphism descent therefore constructs `a`.
3. Worker 1508's `IsSplitTorus.flat_and_surjective_multiplication`
   in `Torus.SplitMultiplication` proves that `[2N]` is surjective
   on the split torus `S`. The construction
   `exists_splitSubtorus_lift_of_surjective_splitParametrization`
   in Worker 1437's `CentralIsogeny.SplitParametrization` takes the
   dominant closed split image of `a`. Schematic dominance descends
   containment of its composite with `π` in the closed subgroup `i`.
   Represented-subgroup factorization gives the actual map `f : T → S`.
   The composite from `S` to this image and then to `S` is `[2N]`,
   so `f` is surjective on underlying schemes.
4. Worker 1482's
   `finiteHomMaximalTorusReflection_of_torusImage` in
   `Torus.FiniteHomMaximalityReduction` proves that this `T` is
   maximal among all tori of `G`. Its image premise is supplied by
   Worker 1358's `torusImageClosedTorusStatement` in `Torus.ImageProof`,
   which also applies to nonsplit tori.

For the last step, take any closed torus `M` of `G` containing `T`.
The image theorem gives a closed torus `Z` of `H` through which
`M → H` factors. Surjectivity of `T → S`, together with the
integrality of `S`, gives schematic dominance and a factorization
`S → Z`. The maximality of `i` among all tori makes this
factorization an isomorphism. Thus `M` maps to `S`. This map is finite,
since `M → G → H` is finite and `S → H` is a closed immersion.
The closed immersion `T → M` has schematically dominant composite to
`S`. Integral incomparability on affine coordinate rings then proves
that `T → M` is an isomorphism. This proves the required all-torus
maximality, including nonsplit competitors.

`Langlands.GroupScheme.splitMaximalTorusLift_of_kernel_exponent` in
`CentralIsogeny.SplitTorusLiftComposition` packages these steps with the
kernel-exponent theorem as an explicit input. The entry theorem
supplies that input with `hπ.exists_pow_eq_one_kernel`; no additional
premise remains.

The provenance of this entry theorem is internal composition of the
named helper proofs. Their paired Markdown describes the individual
constructions and source comparisons. In particular, the argument
proves maximality by finite-map rigidity, rather than by a comparison
of ranks or an assumed maximality theorem after base change.

The published statement's literature route is described in
[`SplitTorusLiftStatement`](SplitTorusLiftStatement.md). Its sources are:

- A. Borel and J. Tits, *Compléments à l'article « Groupes réductifs »*,
  Publications Mathématiques de l'IHÉS 41 (1972), Théorème (2.20)(ii),
  printed p.260 / PDF p.9, source ID
  `borel-tits-1972-complements-groupes-reductifs`. For a central
  surjective morphism of connected reductive groups, this theorem
  supplies a maximal split torus above a given maximal split torus.
  Définition (2.2) and Remarque (2.3), printed p.254 / PDF p.3, use
  the scheme-theoretic central kernel and allow inseparable morphisms.
- J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite
  Type over a Field* (2017), source ID `milne-2017-algebraic-groups`:
  Proposition 17.20, printed pp.357–358 / PDF pp.373–374, sends maximal
  tori to maximal tori under quotient maps over an algebraically closed
  field; Theorem 17.82, printed p.379 / PDF p.395, preserves and reflects
  maximality under field extension; Definition 19.20 and the following
  text, printed pp.401–402 / PDF pp.417–418, identify rank with the
  dimension of a maximal torus. Together with the finite kernel, these
  give the statement's alternative promotion from maximal split tori
  to maximal tori by equality of ranks.

The Lean proof implements the kernel-exponent, power-descent and
finite-map-rigidity argument above. These literature results explain
the statement's provenance; they are not unproved inputs to the Lean
proof. The registered Milne errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no entry for the
cited printed pages.
