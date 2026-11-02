# Unipotent, pseudo-reductive and reductive group schemes

This module defines the basic predicates of the reductive theory for the Library's group
schemes `GroupScheme S`, which are group objects in `Over S` over an arbitrary base scheme `S`:

- fixed vectors of a finite free coefficient representation;
- closed subgroups;
- unipotent group schemes over a field;
- triviality of the unipotent radical;
- pseudo-reductive and connected reductive groups over a field;
- reductive group schemes over an arbitrary base.

The module contains definitions only, plus the definitional restatement `mem_fixedSubmodule`. It
proves no structure theorems: that a unipotent radical exists, that the definitions are
invariant under extension of algebraically closed fields, or that any particular group (such as
`GL_n` or a torus) is reductive.

## Sources and provenance

- J. S. Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`. Printed page
  `p` is PDF page `p + 16`.
  - §4.i (printed p. 96): the subspace `V^G` of fixed vectors, and Proposition 4.33.
  - 6.45 (printed p. 135): unipotent algebraic groups.
  - 6.46 (printed p. 135): the unipotent radical and connected reductive groups.
  - 6.47 (printed p. 136): pseudo-reductive groups.
  - §19.b (printed p. 400): restates 6.46.
- B. Conrad, *Reductive group schemes* (2014), source `conrad-2014-reductive-group-schemes`.
  Printed page equals PDF page.
  - Definition 1.1.11 (p. 11): reductive groups over an algebraically closed field.
  - Definition 3.1.1 and the remark after it (p. 81): reductive group schemes over a base.
- B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), source
  `conrad-gabber-prasad-2015-pseudo-reductive`. Printed page `p` is PDF page `p + 26`.
  - Definition 1.1.1 (printed p. 3): the `k`-unipotent radical and pseudo-reductive groups.

Milne and Conrad work with functors on `k`-algebras over a field `k`. Here the test objects are
all schemes `T` over the base, as everywhere in `Langlands.GroupScheme`. The Lean names, and the
use of an arbitrary base scheme `S`, are internal to this Library.

## Fixed vectors

Fix `R : CommRingCat`, a group scheme `G` over `Spec R`, and a finite index type `n` with
decidable equality. A `MatrixRepresentation G n` is the Library's group-scheme homomorphism
`G ⟶ GL_n`, and `ρ.pointMatrix T g` is the invertible matrix over `Γ(T, 𝒪_T)` attached to a point
`g ∈ G(T)`.

- `scalarMap T : R →+* Γ(T, 𝒪_T)` is the structure ring map of a scheme `T` over `Spec R`: the
  inverse of `Γ(Spec R) ≅ R` followed by the global-sections map of `T → Spec R`.
- `MatrixRepresentation.IsFixedVector ρ v` holds for `v : n → R` when, for every `T` over
  `Spec R` and every point `g : T ⟶ G.X`, the matrix `ρ(g)` fixes the image of `v` in
  `Γ(T, 𝒪_T)ⁿ`. This is Milne's `V^G` (§4.i, p. 96), with `V = Rⁿ` and all `S`-schemes as tests
  rather than all `k`-algebras.
- `MatrixRepresentation.fixedSubmodule ρ` is the `R`-submodule `(Rⁿ)^G` of fixed vectors.
  Closure under `0`, `+` and scalars follows from linearity of `Matrix.mulVec` and of `scalarMap`.
- `mem_fixedSubmodule` restates membership as `IsFixedVector`.

Milne's 4.33 says that `V^G` is the set of vectors fixed by the universal point. The Lean
definition quantifies over all test schemes, so this module does not need that
characterization.

## Closed subgroups

- `IsClosedSubgroup i`, for a homomorphism `i : H ⟶ G` of group schemes over `S`, says that the
  underlying morphism of schemes `H.X.left ⟶ G.X.left` is a closed immersion.

Milne (Definition 1.3, printed p. 7) defines an algebraic subgroup of `G` as a `k`-subscheme
`H` of `G` whose inclusion is a homomorphism. Here closedness is part of the definition: a
subgroup is presented by a homomorphism whose underlying morphism is a closed immersion.

## Over a field

Fix a field `k` (in universe `u`). All group schemes in this section live over
`Spec (CommRingCat.of k)`.

- `IsUnipotent G`: for every nonempty finite index type `n : Type` and every matrix
  representation `ρ : MatrixRepresentation G n`, there is a nonzero `v : n → k` with
  `ρ.IsFixedVector v`. This is Milne 6.45 (p. 135): every nonzero representation has a nonzero
  fixed vector. A nonzero finite-dimensional representation becomes a matrix representation once
  a basis indexed by some `Fin m`, `m > 0`, is chosen. So quantifying over `n : Type` covers all
  of them. Milne states 6.45 for algebraic groups (finite type over `k`). The Lean predicate is
  stated for every group scheme over `k`. It is used below only for smooth closed subgroups of
  smooth affine groups, which are of finite type.
- `HasTrivialUnipotentRadical G`: for every group scheme `H` over `k` and every homomorphism
  `i : H ⟶ G` satisfying all of
  - `IsClosedSubgroup i`,
  - `H` is smooth over `k` (`Smooth H.X.hom`),
  - `H` is connected (`ConnectedSpace H.X.left`),
  - `IsUnipotent H`,
  - `SubgroupFunctor.range i` is a normal subgroup functor,

  the subgroup functor `SubgroupFunctor.range i` is `⊥`. That is, `H(T)` has trivial image in
  `G(T)` for every `T`. Milne 6.46 defines the unipotent radical `R_u(G)` as the largest smooth
  connected normal unipotent subgroup. CGP Definition 1.1.1 defines the `k`-unipotent radical
  `R_{u,k}(G)` as the maximal smooth connected unipotent normal `k`-subgroup. Either one is
  trivial exactly when every such subgroup is trivial. That is the condition stated here, so the
  existence of the radical is not needed. Normality is normality of the image on every test
  scheme, as in `SubgroupFunctor.IsNormal`.
- `IsPseudoReductive G` is a structure with four fields:
  - `smooth`: `G` is smooth over `k`;
  - `isAffineHom`: the structure morphism is affine;
  - `connectedSpace`: `G` is connected;
  - `hasTrivialUnipotentRadical`: `HasTrivialUnipotentRadical G`.

  This is CGP Definition 1.1.1 (printed p. 3), "a smooth connected affine `k`-group `G` such
  that `R_{u,k}(G) = 1`", and Milne 6.47. Over an algebraically closed field this is Conrad's
  Definition 1.1.11 (p. 11) of a connected reductive group. (Conrad's §1.1 works over an
  algebraically closed `k`, and linear algebraic groups there are smooth affine `k`-groups of
  finite type.)
- `toAlgebraicClosure k : Spec (AlgebraicClosure k) ⟶ Spec k` is `Spec` of the algebra map into
  Mathlib's `AlgebraicClosure k`.
- `IsConnectedReductive G` is a structure with four fields:
  - `smooth`, `isAffineHom` and `connectedSpace`, as above;
  - `hasTrivialGeometricUnipotentRadical`: `HasTrivialUnipotentRadical` holds for the Library base
    change `(GroupScheme.baseChange (toAlgebraicClosure k)).obj G`.

  This is Milne 6.46 (p. 135, restated in §19.b, p. 400): a connected group variety over `k` is
  reductive if its geometric unipotent radical `R_u(G_{k^a})` is trivial. Affine plus smooth
  (which includes locally of finite presentation) gives finite type over `k`. Milne's algebraic
  closure `k^a` is realized by Mathlib's `AlgebraicClosure k`. Milne asks for `G` itself to be
  connected, as here. Geometric connectedness of `G_{k^a}` is a theorem (Conrad, p. 81), not
  part of the definition.

## Over an arbitrary base

Fix a scheme `S`.

- `geometricPoint S s` is the geometric point `Spec κ(s)^alg → S` over `s ∈ S`: the composite of
  `toAlgebraicClosure (S.residueField s)` with `S.fromSpecResidueField s`.
- `geometricFiber G s` is the Library base change of `G` along `geometricPoint S s`. It is a
  group scheme over `Spec (AlgebraicClosure κ(s))`.
- `IsReductive G` is a structure with three fields:
  - `smooth`: `G` is smooth over `S`;
  - `isAffineHom`: the structure morphism `G → S` is affine;
  - `geometricFiber`: for every point `s : S`, `IsPseudoReductive (geometricFiber G s)`.

  This is Conrad's Definition 3.1.1 (p. 81): "a reductive `S`-group is a smooth `S`-affine group
  scheme `G → S` such that the geometric fibers `G_{s̄}` are connected reductive groups". Two
  points about the implementation:
  - The fibre condition uses `IsPseudoReductive` over the algebraically closed field
    `AlgebraicClosure κ(s)`. That is Conrad's Definition 1.1.11 together with connectedness. It
    avoids a second algebraic closure, which `IsConnectedReductive` of the fibre would introduce.
  - The fibre fields `smooth` and `isAffineHom` follow from the global ones by base change. They
    are kept so that the fibre condition is literally the field-level definition.

  Conrad's definition quantifies over all geometric points. Here there is one chosen geometric
  point over each `s ∈ S`. The remark after Definition 3.1.1 explains that one geometric point
  over each `s` suffices, because the unipotent radical commutes with extension of algebraically
  closed fields (Conrad, Exercise 3.4.1). That invariance is not proved here.

## Relation to other formalizations

TauCeti (pinned commit `8428d6217f74afa72531df0bc85d7b57ab72810f`) has
`TauCeti/Algebra/AlgebraicGroup/Reductive/Basic.lean` and `Reductive/Over.lean`. These state
reductivity for finite-type commutative Hopf algebras over a field, and for Hopf algebras over a
commutative ring with all algebraically closed field points as tests. This module is written
directly on `Langlands.GroupScheme` instead, and it allows non-affine bases. The reasons, from
the reuse ledger for this program: the import closures of those TauCeti modules have 173–215
modules, they need one Mathlib module absent from the pinned Mathlib, and their setting is only
affine. Comparing the two definitions for `S = Spec R` and `G = Spec H` is possible future work.
It is not part of this module.
