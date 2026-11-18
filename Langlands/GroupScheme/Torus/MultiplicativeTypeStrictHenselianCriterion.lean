import Langlands.GroupScheme.Torus.MultiplicativeTypeStrictHenselianReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeSpecialFiberSplitting
import Langlands.GroupScheme.Torus.MultiplicativeTypeTorsionDeterminationProof
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeField

/-! # The strict-Henselian fibral criterion from the clopen lift -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.StrictHenselianFibral

/-- An actual diagonalizable model retaining the entire finitely generated
character group. -/
structure FibralDiagonalization {S : Scheme.{u}} (H : GroupScheme S) where
  characters : Type u
  [characterGroup : AddCommGroup characters]
  [finitelyGenerated : AddGroup.FG characters]
  iso : H ≅ RelativeMultiplicativeType.diagonalizable S characters

attribute [instance] FibralDiagonalization.characterGroup
  FibralDiagonalization.finitelyGenerated

theorem FibralDiagonalization.isDiagonalizable {S : Scheme.{u}} {H : GroupScheme S}
    (D : FibralDiagonalization H) : RelativeMultiplicativeType.IsDiagonalizable H :=
  ⟨D.characters, inferInstance, inferInstance, ⟨D.iso⟩⟩

variable (hLift : MultiplicativeTypeStrictHenselianLiftStatement.{u})
  (A : Type u) [CommRing A] [HenselianLocalRing A]
  [IsSepClosed (IsLocalRing.ResidueField A)]
  (H : GroupScheme (Spec (CommRingCat.of A)))
  [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom] [IsAffineHom H.X.hom]

/-- Clopen lifting alone supplies an actual diagonalization in the
connected-fibre branch; special-fibre splitting is constructed internally. -/
def connectedSplitting
    (hconn : ∀ s : Spec (CommRingCat.of A),
      ConnectedSpace (RelativeIdentityComponent.residueFiber H s).X.left)
    (hH : ∀ s : Spec (CommRingCat.of A), IsMultiplicativeType (geometricFiber H s)) :
    FibralDiagonalization H := by
  let D := LocalSpecialGeometricFiber.specialFiberDiagonalization A H
    (hH (IsLocalRing.closedPoint A))
  let E := connectedDiagonalization hLift A H hH D.characters hconn D.iso
  exact {
    characters := D.characters
    iso := E.val.symm }

/-- Clopen lifting alone supplies an actual diagonalization in the commutative
torsion-order branch. Torsion determination is the published theorem. -/
def commutativeSplitting [IsCommMonObj H.X]
    (hH : ∀ s : Spec (CommRingCat.of A), IsMultiplicativeType (geometricFiber H s))
    (hOrder : ∀ (n : ℕ), 0 < n → IsLocallyConstant fun s : Spec (CommRingCat.of A) =>
      letI := Langlands.AlgebraicGeometry.FiniteEtale.coordinateAlgebra
        (torsion (geometricFiber H s) (n : ℤ)).X.hom
      Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of A)).residueField s))
        Γ((torsion (geometricFiber H s) (n : ℤ)).X.left, ⊤)) :
    FibralDiagonalization H := by
  let D := LocalSpecialGeometricFiber.specialFiberDiagonalization A H
    (hH (IsLocalRing.closedPoint A))
  let E := commutativeDiagonalization hLift A H hH D.characters
    multiplicativeTypeTorsionDetermination hOrder D.iso
  exact {
    characters := D.characters
    iso := E.val.symm }

include hLift

/-- The entire connected-fibre equivalence over a strictly Henselian local
base, conditional only on the clopen-lifting proposition. -/
theorem connectedCriterion
    (hconn : ∀ s : Spec (CommRingCat.of A),
      ConnectedSpace (RelativeIdentityComponent.residueFiber H s).X.left) :
    RelativeMultiplicativeType.IsMultiplicativeType H ↔
      ∀ s : Spec (CommRingCat.of A), IsMultiplicativeType (geometricFiber H s) :=
  ⟨fun h s => h.geometricFiber s,
    fun h => RelativeMultiplicativeType.IsMultiplicativeType.of_isDiagonalizable
      (connectedSplitting hLift A H hconn h).isDiagonalizable⟩

/-- The entire commutative equivalence over a strictly Henselian local base,
conditional only on the clopen-lifting proposition. -/
theorem commutativeCriterion [IsCommMonObj H.X] :
    RelativeMultiplicativeType.IsMultiplicativeType H ↔
      (∀ s : Spec (CommRingCat.of A), IsMultiplicativeType (geometricFiber H s)) ∧
        ∀ (n : ℕ), 0 < n → IsLocallyConstant fun s : Spec (CommRingCat.of A) =>
          letI := Langlands.AlgebraicGeometry.FiniteEtale.coordinateAlgebra
            (torsion (geometricFiber H s) (n : ℤ)).X.hom
          Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of A)).residueField s))
            Γ((torsion (geometricFiber H s) (n : ℤ)).X.left, ⊤) :=
  ⟨fun h => ⟨fun s => h.geometricFiber s, fun n hn => h.isLocallyConstant_torsionFinrank n hn⟩,
    fun h => RelativeMultiplicativeType.IsMultiplicativeType.of_isDiagonalizable
      (commutativeSplitting hLift A H h.1 h.2).isDiagonalizable⟩

end Langlands.GroupScheme.StrictHenselianFibral
