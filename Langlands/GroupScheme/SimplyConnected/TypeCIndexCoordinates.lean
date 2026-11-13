import Langlands.GroupScheme.Reductive.TitsIndexIndependenceProof
import Langlands.LinearAlgebra.CartanCNumbering
import Langlands.LinearAlgebra.TypeCBlockWeights

/-! # Type C distinguished vertices from actual restriction coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K : Type u} [Field K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- Actual simple-root restrictions, expressed in a numbered type C base and
in integer coordinates of the actual maximal split torus. -/
def HasTypeCRestrictionCoordinates (d : TitsIndexData G) (n degree r : ℕ) : Prop :=
  ∃ (e : d.Vertex ≃ Fin n)
    (F : characterLattice d.splitTorus ≃+ (Fin r → ℤ)),
    IsTypeCNumbering d.cartan e ∧
      ∀ a, F (d.rootRestriction a.val) =
        TypeCBlockWeights.simpleRestriction degree r (e a)

namespace HasTypeCRestrictionCoordinates

/-- The coordinate comparison computes the distinguished vertices of its
supplied actual index data. -/
theorem exists_numbering {d : TitsIndexData G} {n degree r : ℕ}
    (h : HasTypeCRestrictionCoordinates d n degree r)
    (hd : 0 < degree) (hrn : r * degree ≤ n) :
    ∃ e : d.Vertex ≃ Fin n, IsTypeCNumbering d.cartan e ∧
      ∀ a, a ∈ d.distinguishedVertices ↔
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ (e a).val + 1 = j * degree := by
  obtain ⟨e, F, he, hF⟩ := h
  refine ⟨e, he, fun a => ?_⟩
  change d.rootRestriction a.val ≠ 0 ↔ _
  have hz : F (d.rootRestriction a.val) = 0 ↔ d.rootRestriction a.val = 0 :=
    F.map_eq_zero_iff
  refine (not_congr hz).symm.trans ?_
  rw [hF a]
  exact TypeCBlockWeights.simpleRestriction_ne_zero_iff hd hrn (e a)

end HasTypeCRestrictionCoordinates

namespace TitsIndexEquiv

/-- An index comparison preserves the precise type C numbering, since the
oriented Cartan matrix has no nonidentity automorphism. -/
theorem typeC_numbering_eq {d : TitsIndexData G} {d' : TitsIndexData H}
    (f : TitsIndexEquiv d d') {n : ℕ} (hn : 2 ≤ n)
    (e : d.Vertex ≃ Fin n) (e' : d'.Vertex ≃ Fin n)
    (he : IsTypeCNumbering d.cartan e) (he' : IsTypeCNumbering d'.cartan e') :
    ∀ a, e a = e' (f.vertices a) := by
  have heq : e = f.vertices.trans e' :=
    CartanCNumbering.unique hn e (f.vertices.trans e') he (fun a b => by
      change d.cartan a b = CartanMatrix.C n (e' (f.vertices a)) (e' (f.vertices b))
      rw [← f.cartan_eq a b, he'])
  intro a
  exact congrArg (fun g : d.Vertex ≃ Fin n => g a) heq

/-- Transport a computed type C marked set to the exact supplied numbering. -/
theorem typeC_distinguished_iff {d : TitsIndexData G} {d' : TitsIndexData H}
    (f : TitsIndexEquiv d d') {n degree r : ℕ} (hn : 2 ≤ n)
    (e : d.Vertex ≃ Fin n) (e' : d'.Vertex ≃ Fin n)
    (he : IsTypeCNumbering d.cartan e) (he' : IsTypeCNumbering d'.cartan e')
    (hmark : ∀ a, a ∈ d'.distinguishedVertices ↔
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ (e' a).val + 1 = j * degree) (a : d.Vertex) :
    a ∈ d.distinguishedVertices ↔
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ (e a).val + 1 = j * degree := by
  have hdist : a ∈ d.distinguishedVertices ↔ f.vertices a ∈ d'.distinguishedVertices :=
    not_congr (f.zero_iff a)
  rw [hdist, hmark, f.typeC_numbering_eq hn e e' he he' a]

end TitsIndexEquiv

/-- One convenient actual index with proved restriction coordinates suffices
for every actual index of the same group and its given type C numbering. -/
theorem typeC_distinguished_of_coordinates
    (d d' : TitsIndexData G) {n degree r : ℕ} (hn : 2 ≤ n)
    (e : d.Vertex ≃ Fin n) (he : IsTypeCNumbering d.cartan e)
    (hcoords : HasTypeCRestrictionCoordinates d' n degree r)
    (hd : 0 < degree) (hrn : r * degree ≤ n) (a : d.Vertex) :
    a ∈ d.distinguishedVertices ↔
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ (e a).val + 1 = j * degree := by
  obtain ⟨e', he', hmark⟩ := hcoords.exists_numbering hd hrn
  obtain ⟨f⟩ := titsIndexIndependence K G d d'
  exact f.typeC_distinguished_iff hn e e' he he' hmark a

end Langlands.GroupScheme
