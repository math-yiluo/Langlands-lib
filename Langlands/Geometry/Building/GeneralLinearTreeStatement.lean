import Langlands.Geometry.Building.LatticeHomothetyClasses
import Langlands.Geometry.Building.BuildingFacetVertices
import Langlands.Geometry.Building.DepthZero.Definitions
import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # The tree of `GL_2` for KP building data

For a nonarchimedean local field `F` with residue field `𝓀[F]` of `q` elements and building
data `D : KPBuildingDatum G` of `G = GL_2` over `F` satisfying the one-group axioms, these
statements describe the reduced building `B(G)` as the `(q + 1)`-regular tree of homothety
classes of lattices in `F²` (Kaletha–Prasad, Example 1.5.10, §3.1, 15.1.23, Proposition 15.1.31
and 15.1.33):

* `ValuationBuildingData.chamberVertexGraph B` is the simple graph on the vertices of the
  reduced building of building data `B` in which two distinct vertices are adjacent when both
  are incident to one chamber, that is, both lie in its combinatorial closure
  (`buildingFacetVertices`);
* `GeneralLinearTwoTreeStatement`: for `GL_2` this graph is a tree, every vertex has exactly
  `q + 1` neighbours, and the vertices incident to a chamber are two adjacent vertices;
* `GeneralLinearTwoLatticeClassStatement`: there is a `G(F)`-equivariant bijection from the
  vertices to the homothety classes of `𝒪[F]`-lattices in `F²` (`LatticeClass F (Fin 2)`),
  under which adjacency is `𝔪 L ⊊ L' ⊊ L` for representatives, and the parahoric `D.parahoric x`
  of a vertex facet `x = {y}` is the stabilizer in `G(F)` of any lattice representing `y`.

Elements of `G(F)` act on lattices through the matrix of the point
(`GeneralLinear.rationalPointsEquiv`), on column vectors. The two propositions state the
comparisons and do not prove them.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open BruhatTits.IntegralModels

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The vertex graph of the reduced building: the simple graph on the vertices `y`
(`B.IsVertex y`) of the reduced building in which two distinct vertices are adjacent when both
are incident to one chamber, that is, both belong to the vertex set
`B.buildingFacetVertices C` of the combinatorial closure of a chamber `C`. -/
def chamberVertexGraph : SimpleGraph {y : B.ReducedBuilding // B.IsVertex y} where
  Adj v w := v ≠ w ∧ ∃ C : BuildingFacet B, B.IsChamber C.val ∧
    v.val ∈ B.buildingFacetVertices C ∧ w.val ∈ B.buildingFacetVertices C
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ hC => ⟨hC.1, hC.2.2, hC.2.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end ValuationBuildingData

/-- **The building of `GL_2` is the `(q + 1)`-regular tree.** For building data `D` of
`G = GL_2` over a nonarchimedean local field `F` satisfying the one-group axioms, let `Γ` be the
vertex graph `chamberVertexGraph` of the reduced building and `q = |𝓀[F]|`. Then `Γ` is a tree,
every vertex of `Γ` has exactly `q + 1` neighbours, and the vertices incident to any chamber `C`
of the reduced building are exactly two vertices, which are adjacent in `Γ` (Kaletha–Prasad,
Example 1.5.10 and §3.1; 15.1.23). -/
def GeneralLinearTwoTreeStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (D : KPBuildingDatum (GeneralLinear.groupScheme (Fin 2) (CommRingCat.of F))),
    D.SatisfiesGroupAxioms →
      let B := D.base.toValuationBuildingData
      let Γ := B.chamberVertexGraph
      Γ.IsTree ∧
        (∀ v, (Γ.neighborSet v).encard = ((Nat.card 𝓀[F] + 1 : ℕ) : ℕ∞)) ∧
        ∀ C : BuildingFacet B, B.IsChamber C.val →
          ∃ v w, B.buildingFacetVertices C = {v.val, w.val} ∧ Γ.Adj v w

/-- **The vertices of the tree of `GL_2` are the homothety classes of lattices.** For building
data `D` of `G = GL_2` over a nonarchimedean local field `F` satisfying the one-group axioms,
write `ρ : G(F) → GL_2(F)` for the matrix of a point and `𝔪` for the maximal ideal of `𝒪[F]`.
There is a bijection `Φ` from the vertices of the reduced building to the homothety classes
`[L]` of `𝒪[F]`-lattices `L ⊆ F²` such that

* `Φ` is `G(F)`-equivariant: `Φ(g y) = ρ(g) Φ(y)`;
* two vertices `v`, `w` are adjacent in `chamberVertexGraph` if and only if `Φ v = [L]` and
  `Φ w = [L']` for lattices with `𝔪 L ⊊ L' ⊊ L`;
* for every vertex `y`, the parahoric `D.parahoric x` of the facet `x = {y}` is the stabilizer
  `{g | ρ(g) L = L}` of every lattice `L` with `Φ y = [L]`

(Kaletha–Prasad, 15.1.23, Proposition 15.1.31, Remark 15.1.32 and 15.1.33). -/
def GeneralLinearTwoLatticeClassStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (D : KPBuildingDatum (GeneralLinear.groupScheme (Fin 2) (CommRingCat.of F))),
    D.SatisfiesGroupAxioms →
      let B := D.base.toValuationBuildingData
      let ρ : rationalPoints (GeneralLinear.groupScheme (Fin 2) (CommRingCat.of F)) →*
          GL (Fin 2) F :=
        (GeneralLinear.rationalPointsEquiv 2 (CommRingCat.of F)).toMonoidHom
      ∃ Φ : {y : B.ReducedBuilding // B.IsVertex y} ≃ LatticeClass F (Fin 2),
        (∀ g (v w : {y : B.ReducedBuilding // B.IsVertex y}),
          w.val = g • v.val → Φ w = ρ g • Φ v) ∧
        (∀ v w, B.chamberVertexGraph.Adj v w ↔
          ∃ L L' : ValuationRingLattice F (Fin 2), Φ v = LatticeClass.mk L ∧
            Φ w = LatticeClass.mk L' ∧
            IsLocalRing.maximalIdeal 𝒪[F] • L.carrier < L'.carrier ∧ L'.carrier < L.carrier) ∧
        ∀ (v : {y : B.ReducedBuilding // B.IsVertex y}) (x : BuildingFacet B), x.val = {v.val} →
          ∀ L : ValuationRingLattice F (Fin 2), Φ v = LatticeClass.mk L →
            D.parahoric x = (MulAction.stabilizer (GL (Fin 2) F) L).comap ρ

end Langlands.Geometry.Building
