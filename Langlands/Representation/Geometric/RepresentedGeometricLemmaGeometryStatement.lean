import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Mathlib.Data.Fintype.EquivFin

/-! # The geometric prerequisites of the represented geometric lemma -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The geometric part of Renard VI.5.1: finite double cosets with representatives
having the intersection data of V.4.7. This contains no filtration assertion. -/
def RepresentedGeometricLemmaGeometryStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q L U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      ∃ (m : ℕ)
        (c : Fin m ≃ DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
          (pointImage q : Set (rationalPoints G)))
        (z : Fin m → rationalPoints G),
        (∀ i, DoubleCoset.mk (pointImage p) (pointImage q) (z i) = c i) ∧
        Nonempty (∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
          q lQ rQ hq hrQ hlQ hmulQ (z i))

section Assembly

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))

/-- Finiteness and a good representative in each actual double coset give the
enumerated geometric data required by the represented geometric lemma. The
intersection data are chosen together with the representatives. -/
theorem exists_enumerated_geometricLemmaIntersectionDatum
    (hfinite : Finite (DoubleCoset.Quotient
      (pointImage p : Set (rationalPoints G)) (pointImage q : Set (rationalPoints G))))
    (hdata : ∀ a : DoubleCoset.Quotient
      (pointImage p : Set (rationalPoints G)) (pointImage q : Set (rationalPoints G)),
      ∃ z : rationalPoints G,
        DoubleCoset.mk (pointImage p) (pointImage q) z = a ∧
        Nonempty (GeometricLemmaIntersectionDatum p l r hp hr hl hmul
          q lQ rQ hq hrQ hlQ hmulQ z)) :
    ∃ (m : ℕ)
      (c : Fin m ≃ DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
        (pointImage q : Set (rationalPoints G)))
      (z : Fin m → rationalPoints G),
      (∀ i, DoubleCoset.mk (pointImage p) (pointImage q) (z i) = c i) ∧
      Nonempty (∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
        q lQ rQ hq hrQ hlQ hmulQ (z i)) := by
  classical
  let A := DoubleCoset.Quotient
    (pointImage p : Set (rationalPoints G)) (pointImage q : Set (rationalPoints G))
  let : Finite A := hfinite
  let : Fintype A := Fintype.ofFinite A
  let c : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  choose z hz hD using fun i : Fin (Fintype.card A) => hdata (c i)
  exact ⟨Fintype.card A, c, z, hz, ⟨fun i => Classical.choice (hD i)⟩⟩

end Assembly

/-- The full represented geometric lemma implies its geometric prerequisite,
by forgetting only the natural filtration. -/
theorem representedGeometricLemmaGeometry_of_geometricLemma
    (h : RepresentedGeometricLemmaStatement.{u, u}) :
    RepresentedGeometricLemmaGeometryStatement.{u} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  obtain ⟨m, c, z, hz, D, _⟩ :=
    h k G hG P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  exact ⟨m, c, z, hz, ⟨D⟩⟩

end Langlands.Aubert.General.RepresentedParabolic
