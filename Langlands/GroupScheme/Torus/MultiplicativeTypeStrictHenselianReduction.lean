import Langlands.GroupScheme.Torus.MultiplicativeTypeStrictHenselianLiftStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeClopenTorsionReduction
import Langlands.GroupScheme.Torus.LocalSpecialGeometricFiber
import Langlands.GroupScheme.ClopenConnectedFibers

/-! # The two strict-Henselian fibral branches from clopen lifting -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.StrictHenselianFibral

open Langlands.AlgebraicGeometry.FiniteEtale RelativeMultiplicativeType

variable (hLift : MultiplicativeTypeStrictHenselianLiftStatement.{u})
  (A : Type u) [CommRing A] [HenselianLocalRing A]
  [IsSepClosed (IsLocalRing.ResidueField A)]
  (H : GroupScheme (Spec (CommRingCat.of A)))
  [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom] [IsAffineHom H.X.hom]
  (hH : ∀ s : Spec (CommRingCat.of A),
    _root_.Langlands.GroupScheme.IsMultiplicativeType (geometricFiber H s))
  (M : Type u) [AddCommGroup M] [AddGroup.FG M]

/-- Given the clopen-lifting proposition, a prescribed special-fibre
diagonalization lifts to an actual diagonalization when the target fibres
are connected. The forward map retains the exact specified reduction. -/
def connectedDiagonalization
    (hconn : ∀ s : Spec (CommRingCat.of A),
      ConnectedSpace (RelativeIdentityComponent.residueFiber H s).X.left)
    (e : (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj
        (diagonalizable (Spec (CommRingCat.of A)) M) ≅
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj H) :
    {E : diagonalizable (Spec (CommRingCat.of A)) M ≅ H //
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map E.hom =
        e.hom} :=
  Classical.choice (by
    obtain ⟨j, hj, ho, hc⟩ := hLift A H hH M e
    let := ho
    let := hc
    let E := clopenConnectedFibersIso j hconn
    refine ⟨⟨E, ?_⟩⟩
    change (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map j =
      e.hom
    exact hj)

/-- Given clopen lifting and torsion determination, a prescribed special-fibre
diagonalization lifts to an actual diagonalization in the commutative
locally-constant-torsion branch. -/
def commutativeDiagonalization
    (hDetermination : MultiplicativeTypeTorsionDeterminationStatement.{u})
    [IsCommMonObj H.X]
    (hOrder : ∀ (n : ℕ), 0 < n → IsLocallyConstant fun s : Spec (CommRingCat.of A) =>
      letI := coordinateAlgebra (torsion (geometricFiber H s) (n : ℤ)).X.hom
      Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of A)).residueField s))
        Γ((torsion (geometricFiber H s) (n : ℤ)).X.left, ⊤))
    (e : (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj
        (diagonalizable (Spec (CommRingCat.of A)) M) ≅
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj H) :
    {E : diagonalizable (Spec (CommRingCat.of A)) M ≅ H //
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map E.hom =
        e.hom} :=
  Classical.choice (by
    obtain ⟨j, hj, ho, hc⟩ := hLift A H hH M e
    let := ho
    let := hc
    have hD : RelativeMultiplicativeType.IsMultiplicativeType
        (diagonalizable (Spec (CommRingCat.of A)) M) :=
      IsMultiplicativeType.of_isDiagonalizable
        ⟨M, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
    have : IsIso ((GroupScheme.baseChange
        (Spec.algebraMap A (IsLocalRing.ResidueField A))).map j) := by
      rw [hj]
      infer_instance
    have : IsIso ((GroupScheme.baseChange
        (geometricPoint (Spec (CommRingCat.of A)) (IsLocalRing.closedPoint A))).map j) :=
      LocalSpecialGeometricFiber.isIso_geometric_of_special A j
    have : PreconnectedSpace (Spec (CommRingCat.of A)) := by
      apply preconnectedSpace_of_forall_constant
      intro f hf x y
      exact ((IsLocalRing.specializes_closedPoint x).map hf).eq.trans
        ((IsLocalRing.specializes_closedPoint y).map hf).eq.symm
    let E := FibralClopen.isoOfLocallyConstantTorsionOrders
      hDetermination j hD hH (IsLocalRing.closedPoint A) hOrder (by
        intro n hn
        let s := IsLocalRing.closedPoint A
        let Gs := geometricFiber (diagonalizable (Spec (CommRingCat.of A)) M) s
        let Hs := geometricFiber H s
        have hGs : RelativeMultiplicativeType.IsMultiplicativeType Gs :=
          hD.baseChange (geometricPoint (Spec (CommRingCat.of A)) s)
        have hHs : RelativeMultiplicativeType.IsMultiplicativeType Hs :=
          FibralClopen.relative_of_field_of_isSepClosed Hs (hH s)
        obtain ⟨hfG, hflG, -⟩ := hGs.torsion_geometry n hn
        obtain ⟨hfH, hflH, -⟩ := hHs.torsion_geometry n hn
        let := hfG
        let := hflG
        let := hfH
        let := hflH
        let x := IsLocalRing.closedPoint
          (AlgebraicClosure ((Spec (CommRingCat.of A)).residueField s))
        let En := torsionMapIso
          (asIso ((GroupScheme.baseChange (geometricPoint (Spec (CommRingCat.of A)) s)).map j))
          (n : ℤ)
        have hRank := Scheme.Hom.finrank_comp_left_of_isIso
          En.hom.hom.hom.left (torsion Hs (n : ℤ)).X.hom
        rw [Over.w En.hom.hom.hom] at hRank
        exact (homFinrank_eq_coordinateFinrank (torsion Gs (n : ℤ)).X.hom x).symm.trans
          ((congrFun hRank x).trans
            (homFinrank_eq_coordinateFinrank (torsion Hs (n : ℤ)).X.hom x)))
    refine ⟨⟨E, ?_⟩⟩
    change (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map j =
      e.hom
    exact hj)

end Langlands.GroupScheme.StrictHenselianFibral
