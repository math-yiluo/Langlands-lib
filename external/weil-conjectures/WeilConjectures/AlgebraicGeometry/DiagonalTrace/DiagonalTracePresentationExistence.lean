/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceComparisonPresentation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceTwistedSplittingComponents
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalTraceCompletedHomBijection

/-! # Geometric presentations of the projective-line trace

Source: blueprint latest, diagonal-tower trace proof, paragraph (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- The unit and the hyperplane Chern class admit compatible strict-system and
completed-coefficient presentations on a specified projective-line model.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
construction of the splitting and the direct-image/limit comparisons; expanded
DAG proof steps 1--6.
(blueprint: lem-sfb-diagonal-trace-presentation-existence).

Proof: construct the Chern morphism on the whole varying-coefficient system by
reducing the integral line-bundle extension, and use the hyperplane bundle of
this model. Its class is the class of the section [1:0]: on the standard charts
the equations are x1/x0 and 1, with transition x0/x1 for their inverses. The
finite Cartier normalization therefore has positive degree one. The unit/Chern
map evaluates to the finite projective-line decomposition. Its cone has zero
cohomology at every level, so it is invertible in the system derived category.
Twisting its inverse and taking the second projection gives a map which kills
the twisted unit and sends the Chern class to one, also after every evaluation.
Restrict the varying coefficient systems to constant Z_l scalars, retaining their
sections and transitions. Exact restriction and the ringed-topos composition
comparison give the normalized varying and completed direct-image squares.
The canonical direct-image/derived-limit comparison supplies the limit square.
The quotient tower and root tower have epimorphic transitions, so their Milnor
comparisons are invertible. Their ordinary limits are the completed unit and
Tate line by their defining projections. These comparisons give precisely the
unit_limit and line_limit fields. The completed line and unit are derived complete;
derived direct image preserves completeness. Restriction from completed to constant
scalars is an equivalence on these complete objects, so its map on the indicated
Hom set is bijective. No completed trace morphism is chosen here. -/
theorem exists_diagonalTracePresentation (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsNoetherian X]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (m : X ≅ ProjectiveLine S) (hm : m.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (l : Γ(S, ⊤))) :
    ∃ p : Presentation l (ULift.{u} (Padic l)) f,
      p.model.model = m ∧
      ∃ hs : IsIso (p.model.bq l (ULift.{u} (Padic l))),
        letI := hs
        (∀ n : ℕ,
          (SpTowerShriek.Ev l (ULift.{u} (Padic l)) S n).map
            (p.model.twistedUnit l (ULift.{u} (Padic l)) ≫
              p.model.trace l (ULift.{u} (Padic l))) = 0) ∧
        (∀ n : ℕ,
          (SpTowerShriek.Ev l (ULift.{u} (Padic l)) S n).map
            (p.model.chernAdjoint l (ULift.{u} (Padic l)) ≫
              p.model.trace l (ULift.{u} (Padic l))) =
                𝟙 ((SpTowerShriek.Ev l (ULift.{u} (Padic l)) S n).obj
                  (SpTowerClasses.unit S (SpTowerClasses.Arings l (ULift.{u} (Padic l)) S)))) ∧
        Function.Bijective (fun t : p.Rc.R.obj ((completedLine l X)⟦(2 : ℤ)⟧) ⟶
            completedUnit l S ↦ (diagonalCompletedUnderlying l S).map t) := by
  obtain ⟨p, hp⟩ := exists_diagonalTraceComparisonPresentation l f m hm hS
  let E := ULift.{u} (Padic l)
  let T := p.twistS.T l E ⋙
    shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S)) (2 : ℤ)
  let a := (shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
    (2 : ℤ)).mapIso (p.twistS.positiveUnit l E).symm
  let b := (shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
      (2 : ℤ)).mapIso
        (((p.twistS.T l E).commShiftIso (-2 : ℤ)).app
          (SpTowerClasses.inverseLine l E p.chernS)) ≪≫
    (shiftFunctorCompIsoId (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
      (-2 : ℤ) 2 (by decide)).app
        ((p.twistS.T l E).obj (SpTowerClasses.inverseLine l E p.chernS)) ≪≫
    p.twistS.contract l E
  obtain ⟨heval, hu, hc⟩ := diagonalTrace_twistedSplitting_components l p hS
  change p.model.twistedUnit l E =
    a.hom ≫ T.map biprod.inl ≫ T.map (p.model.bq l E) ≫
      (p.model.twistedPush l E).hom at hu
  change p.model.chernAdjoint l E =
    b.inv ≫ T.map biprod.inr ≫ T.map (p.model.bq l E) ≫
      (p.model.twistedPush l E).hom at hc
  have hs : IsIso (p.model.bq l E) :=
    (p.base.calculus S).detects (p.model.bq l E) heval
  have ht : p.model.trace l E = (p.model.twistedPush l E).inv ≫
      T.map (inv (p.model.bq l E)) ≫ T.map biprod.snd ≫ b.hom := by
    rfl
  have hunit : p.model.twistedUnit l E ≫ p.model.trace l E = 0 := by
    calc
      _ = a.hom ≫ T.map
          (biprod.inl ≫ p.model.bq l E ≫ inv (p.model.bq l E) ≫ biprod.snd) ≫
            b.hom := by
        rw [hu, ht]
        simp only [T.map_comp, Category.assoc,
          (p.model.twistedPush l E).hom_inv_id_assoc]
      _ = 0 := by
        simp only [IsIso.hom_inv_id_assoc, biprod.inl_snd, Functor.map_zero,
          comp_zero, zero_comp]
  have hchern : p.model.chernAdjoint l E ≫ p.model.trace l E = 𝟙 _ := by
    calc
      _ = b.inv ≫ T.map
          (biprod.inr ≫ p.model.bq l E ≫ inv (p.model.bq l E) ≫ biprod.snd) ≫
            b.hom := by
        rw [hc, ht]
        simp only [T.map_comp, Category.assoc,
          (p.model.twistedPush l E).hom_inv_id_assoc]
      _ = 𝟙 _ := by
        simp only [IsIso.hom_inv_id_assoc, biprod.inr_snd]
        rw [T.map_id]
        exact (congrArg (fun k ↦ b.inv ≫ k) (Category.id_comp b.hom)).trans
          b.inv_hom_id
  refine ⟨p, hp, hs, ?_, ?_, diagonalTrace_completedHom_bijective l p hS⟩
  · intro n
    rw [hunit]
    exact (SpTowerShriek.Ev l E S n).map_zero _ _
  · intro n
    rw [hchern]
    exact (SpTowerShriek.Ev l E S n).map_id _

end AlgebraicGeometry.ProEtale.DiagonalTrace
