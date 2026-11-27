# The tree of \(\mathrm{GL}_2\) for KP building data

This module defines the vertex graph of the reduced building of building data
and states two regression examples for \(G=\mathrm{GL}_2\): the reduced building
is the \((q+1)\)-regular tree, and its vertices are the homothety classes of
\(\mathcal O_F\)-lattices in \(F^2\). It states them and does not prove them.

## Common setting

Both propositions quantify over a nonarchimedean local field \(F\) of either
characteristic (`IsNonarchimedeanLocalField F`, universe-polymorphic) and every
`D : KPBuildingDatum (GeneralLinear.groupScheme (Fin 2) (CommRingCat.of F))`
with `D.SatisfiesGroupAxioms` (the one-group clauses of the corrected KP
Definition 4.1.26). No other premise is used.

- `B` is `D.base.toValuationBuildingData`, whose reduced building
  `B.ReducedBuilding` carries the action of \(G(F)\).
- A *vertex* is a point `y` with `B.IsVertex y` (a \(G(F)\)-translate of a vertex
  of the apartment for its affine roots). A *chamber* is a building facet
  `C : BuildingFacet B` with `B.IsChamber C.val`.
- The vertices *incident to* a facet `C` are `B.buildingFacetVertices C`
  (`BuildingFacetVertices`): the vertices lying in the combinatorial closure
  `B.buildingFacetClosure C`, the union of the facets `C'` with
  `FacetPrecedes B C' C`. This is the Library's facet incidence.
- \(q\) is `Nat.card 𝓀[F]`, the order of the residue field, and \(\mathfrak m\)
  is `IsLocalRing.maximalIdeal 𝒪[F]`.
- \(\rho:G(F)\to\mathrm{GL}_2(F)\) is the matrix of a point,
  `(GeneralLinear.rationalPointsEquiv 2 (CommRingCat.of F)).toMonoidHom`.
  Matrices act on lattices and on their classes as in
  [`LatticeHomothetyClasses`](LatticeHomothetyClasses.md), on column vectors.

## The vertex graph

**`ValuationBuildingData.chamberVertexGraph B`** is the simple graph on the
type `{y // B.IsVertex y}` of vertices of the reduced building, for any
building data `B`, in which `v` and `w` are adjacent when \(v\ne w\) and both
belong to `B.buildingFacetVertices C` for one chamber `C`. The relation is
symmetric and irreflexive by its form. For a tree, where the chambers are the
edges, this is the graph of the tree.

## The propositions

**`GeneralLinearTwoTreeStatement`.** With \(\Gamma\) the vertex graph of `B`:

1. \(\Gamma\) is a tree (`SimpleGraph.IsTree`: connected, with a vertex, and
   without cycles);
2. every vertex has exactly \(q+1\) neighbours: `(Γ.neighborSet v).encard`
   equals \(q+1\) (so in particular the neighbour set is finite);
3. for every chamber `C` there are vertices `v`, `w` with
   `B.buildingFacetVertices C = {v, w}` and `Γ.Adj v w` (so \(v\ne w\)): each
   chamber is incident to exactly two vertices, and they are adjacent.

**`GeneralLinearTwoLatticeClassStatement`.** There is a bijection \(\Phi\) from
the vertices to `LatticeClass F (Fin 2)`, the homothety classes \([L]\) of
\(\mathcal O_F\)-lattices \(L\subset F^2\), such that

1. \(\Phi\) is \(G(F)\)-equivariant: if `w.val = g • v.val`, then
   \(\Phi(w)=\rho(g)\cdot\Phi(v)\);
2. `v` and `w` are adjacent in \(\Gamma\) if and only if there are lattices
   \(L,L'\) with \(\Phi(v)=[L]\), \(\Phi(w)=[L']\) and
   \(\mathfrak mL\subsetneq L'\subsetneq L\) (as `𝒪[F]`-submodules, with
   \(\mathfrak mL\) the ideal multiple `IsLocalRing.maximalIdeal 𝒪[F] • L.carrier`,
   which is \(\varpi L\) for a uniformizer \(\varpi\));
3. for every vertex `v`, every building facet `x` with `x.val = {v}` (the facet
   of the vertex; `IsVertex.isFacet_singleton`), and every lattice \(L\) with
   \(\Phi(v)=[L]\), the depth-zero parahoric `D.parahoric x` of
   [`DepthZero.Definitions`](DepthZero/Definitions.md) (the integral points of
   the neutral facet model) equals \(\rho^{-1}(\mathrm{Stab}(L))\), the elements
   \(g\) with \(\rho(g)L=L\).

The parahoric is asserted to be the stabilizer of *every* representative: the
stabilizers of \(L\) and \(aL\) coincide because scalars commute with matrices.

## Premises and the choice of datum

The only premise is `D.SatisfiesGroupAxioms`. The building statements use the
datum's reduced building, facets and vertices. By the Library's
`ValuationBuildingData.exists_isEquivariantBuildingIso_id`, the reduced
buildings of any two valuation building data of the same group are identified
by a bijection that maps facets onto facets, apartments onto apartments, and
commutes with \(G(F)\); so the graph and the tree property do not depend on the
datum. The parahoric clause uses the datum's integral models: Axiom 4.1.20,
part of the one-group axioms (`ModelAxiomClauses.neutral_points`), makes the
neutral integral points of the model of `x` equal to
\(G(F)^0\cap G(F)_x\), the elements of \(G(F)^0\) fixing `x` pointwise.

A datum's maximal split torus need not be the diagonal torus, so the
comparison with lattices is through an equivariant bijection \(\Phi\) and not a
fixed identification of a standard apartment.

## Why these hold

For \(\mathrm{GL}(X)\), \(X=F^2\), the reduced building is the building of
norms up to homothety, and its simplicial structure is given by periodic
lattice chains (KP 15.1.23): the vertices are the chains \(\{\varpi^kL\}\) of a
single homothety class \([L]\), and the chambers are the chains whose segments
\(\varpi L_0\subsetneq L_1\subsetneq L_0\) have one-dimensional successive
quotients; the two vertices of such a chamber are \([L_0]\) and \([L_1]\). This
gives the bijection \(\Phi\), its equivariance, the adjacency criterion and the
fact that each chamber has exactly two vertices. The lattices \(L'\) with
\(\varpi L\subsetneq L'\subsetneq L\) correspond to the lines of
\(L/\varpi L\cong k_F^2\), so a vertex has \(\#\mathbb P^1(k_F)=q+1\) neighbours,
and the building is a locally finite tree (KP §3.1 for \(\mathrm{SL}_2\), whose
building is the same tree, and Example 1.5.10). The parahoric subgroup
\(G(F)^0\cap G(F)_x\) of the vertex of \([L]\) is the stabilizer of \(L\), which
is \(\mathrm{GL}(L)\) (KP Proposition 15.1.31 and 15.1.33, where
\(G(F)^0=G(F)^1=\{g:\det g\in\mathcal O_F^\times\}\)): the stabilizer of the
class \([L]\) is \(F^\times\mathrm{GL}(L)\), and \(a k\) with \(a\in F^\times\),
\(k\in\mathrm{GL}(L)\) has unit determinant \(a^2\det k\) exactly when
\(a\in\mathcal O_F^\times\).

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source
`kaletha-prasad-2023-bruhat-tits-new-approach` (PDF page = printed page + 31):

- Example 1.5.10 (a tree as an affine building), printed p. 59;
- §3.1, the example of \(\mathrm{SL}_2\): the building is a tree, locally
  finite with \(\#\mathbb P^1(\mathfrak f)=\#\mathfrak f+1\) edges at each
  vertex, printed pp. 141–146;
- 15.1.23 (facets, vertices and chambers as lattice chains), printed p. 521;
  Proposition 15.1.31 and Remark 15.1.32, printed pp. 523–524; 15.1.33, printed
  p. 524.

The 2024 corrections (`kaletha-prasad-2024-corrections`, version of 1 November
2024) have no entry for Chapter 15; their one entry for §3.1 completes a
sentence before Notation 3.1.1 (on the maximal bounded subgroup of \(T(k)\)) and
does not concern the tree.
