import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
import Langlands.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.Representation.Filtration.ZeroFactorDeletionStatement

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric CategoryTheory

universe uF uV uR uG uC vC

private def evaluatedObjectFiltration
    {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
    {D : Type uC} [Category.{vC} D] {H : D ⥤ Rep.{uV} R G} {m : ℕ}
    (s : RepFunctorFiltration H m) (X : D) : ObjectRepFiltration (H.obj X) m :=
  ObjectRepFiltration.ofSubrepresentations (fun i => (s.step i).obj X)
    (s.monotone X) (s.zero X) (s.top X)

private def evaluatedGradedEquiv
    {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
    {D : Type uC} [Category.{vC} D] {H : D ⥤ Rep.{uV} R G} {m : ℕ}
    (s : RepFunctorFiltration H m) (X : D) (i : Fin m) :
    ((evaluatedObjectFiltration s X).gradedRepresentation i).ρ.Equiv
      ((s.graded i).obj X).ρ :=
  Representation.Equiv.refl _

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) (n : ℕ)

set_option maxHeartbeats 800000 in
/-- Conditional assembly of the associated filtration, preserving every
conjugating occurrence and quasicuspidality of each actual graded quotient. -/
theorem associatedFiltration_of_geometricPieces
    (hgeo : ∀ B C : BlockShape n, GeometricLemmaTheorem.{uF, uV} T B C)
    (hvan : AssociatedGeometricPieceVanishingTheorem.{uF, uV} F T n)
    (hequiv : AssociatedGeometricPieceEquivalenceTheorem.{uF, uV} F T n)
    (htransport : MinimalWeylTransportQuasicuspidalTheorem.{uF, uV} F T n)
    (hdelete : ObjectRepFiltration.ZeroFactorDeletionTheorem.{0, uF, max uF uV}) :
    letI := T.topology
    ∀ (B C : BlockShape n) (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      IsLeviQuasicuspidal B ρ.representation →
      LevisAssociated (F := F.Carrier) B C →
      let A := (T.normalizedJacquetFunctor C).obj
        ((T.normalizedParabolicInductionFunctor B).obj ρ)
      ∃ (r : ℕ) (e : Fin r ≃ MinimalConjugatingPermutations (F := F.Carrier) B C)
        (s : ObjectRepFiltration (Rep.of A.representation) r),
        (∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
          (transport B C (e i).val.val (e i).property ρ.representation))) ∧
        (∀ i, IsLeviQuasicuspidal C (s.gradedRepresentation i).ρ) := by
  let := T.topology
  intro B C ρ hρ hBC
  obtain ⟨S, R, hS, hR, m, e, order, s, hs⟩ := hgeo B C
  let enum : Fin m ≃ MinimalRepresentatives B C := order.trans e
  let evaluated := evaluatedObjectFiltration s ρ
  have graded (i : Fin m) :
      Nonempty ((evaluated.gradedRepresentation i).ρ.Equiv
        ((geometricPieceFunctor T B C (enum i).val (S (enum i)) (R (enum i))
          (hS (enum i)).2.1 (hR (enum i)).2.1).obj ρ).ρ) := by
    obtain ⟨iso⟩ := hs i
    exact ⟨(evaluatedGradedEquiv s ρ i).trans (Representation.equivOfIso (iso.app ρ))⟩
  let P : Fin m → Prop := fun i => ConjugatesLevi (F := F.Carrier) B C (enum i).val
  have zero (i : Fin m) (hi : ¬ P i) : Subsingleton (evaluated.gradedRepresentation i) := by
    let := hvan B C ρ hρ hBC (enum i) (S (enum i)) (R (enum i))
      (hS (enum i)) (hR (enum i)) hi
    obtain ⟨f⟩ := graded i
    exact f.toLinearEquiv.injective.subsingleton
  obtain ⟨r, retained, t, ht⟩ := hdelete ℂ (C.Levi F.Carrier) _ m evaluated P zero
  let selected : {i : Fin m // P i} ≃
      MinimalConjugatingPermutations (F := F.Carrier) B C :=
    enum.subtypeEquiv (fun _ => Iff.rfl)
  let indexing := retained.trans selected
  have identified (j : Fin r) : Nonempty ((t.gradedRepresentation j).ρ.Equiv
      (transport B C (indexing j).val.val (indexing j).property ρ.representation)) := by
    obtain ⟨f⟩ := ht j
    obtain ⟨g⟩ := graded (retained j).val
    obtain ⟨h⟩ := hequiv B C ρ hρ hBC (enum (retained j).val)
      (S (enum (retained j).val)) (R (enum (retained j).val))
      (hS (enum (retained j).val)) (hR (enum (retained j).val)) (retained j).property
    exact ⟨(f.trans g).trans h⟩
  refine ⟨r, indexing, t, identified, ?_⟩
  intro j
  obtain ⟨f⟩ := identified j
  exact (isLeviQuasicuspidal_iff_of_equiv C f).mpr
    (htransport B C ρ hρ (indexing j).val (indexing j).property)

end Langlands.CuspidalSupport
