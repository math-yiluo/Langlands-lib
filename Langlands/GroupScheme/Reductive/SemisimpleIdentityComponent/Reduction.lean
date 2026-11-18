import Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent.FieldReduction
import Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent.TensorCore
import Langlands.GroupScheme.Reductive.SemisimpleRepresentationIdentityComponentStatement
import Langlands.GroupScheme.AffineCartierSmoothProof

/-! # Milne 22.43 and 22.44 from Theorem 22.42 and Proposition 4.19 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SemisimpleIdentityComponent

open MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Base change commutes with tensor products on the point matrices. -/
theorem tensor_baseChange_pointMatrix {R' : CommRingCat.{u}} {n m : Type}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (b : Spec R' ⟶ Spec (CommRingCat.of k)) (T : Over (Spec R'))
    (x : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    ((ρ.tensor σ).baseChange b).pointMatrix T x =
      ((ρ.baseChange b).tensor (σ.baseChange b)).pointMatrix T x := by
  rw [pointMatrix_baseChange, tensor_pointMatrix, tensor_pointMatrix, pointMatrix_baseChange,
    pointMatrix_baseChange]
  rfl

/-- Base change commutes with tensor products on the rational-point representations. -/
theorem tensor_baseChange_rationalRepresentation {K : Type u} [Field K] [Algebra k K]
    {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m) :
    ((ρ.tensor σ).baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).rationalRepresentation =
      ((ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).tensor
        (σ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))))).rationalRepresentation := by
  refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
  rw [rationalRepresentation_apply, rationalRepresentation_apply]
  congr 2
  change Matrix.GeneralLinearGroup.map _ (MatrixRepresentation.pointMatrix _ _ g) =
    Matrix.GeneralLinearGroup.map _ (MatrixRepresentation.pointMatrix _ _ g)
  rw [tensor_baseChange_pointMatrix]

variable [CharZero k] [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]

/-- **Milne 22.44**, given Theorem 22.42 and Proposition 4.19: over a field of characteristic
zero, the tensor product of two semisimple matrix representations is semisimple. -/
theorem tensor_isSemisimpleStable
    (h22 : CharZeroReductiveSemisimpleRepresentationStatement.{u})
    (h419 : SemisimpleRepresentationFieldExtensionStatement.{u}) {n m : ℕ}
    (ρ : MatrixRepresentation G (Fin n)) (σ : MatrixRepresentation G (Fin m))
    (hρ : ρ.IsSemisimpleStable) (hσ : σ.IsSemisimpleStable) :
    (ρ.tensor σ).IsSemisimpleStable := by
  have : Smooth G.X.hom := affineCartierSmooth k G inferInstance inferInstance
  apply isSemisimpleStable_of_geometric_rational h419
  rw [tensor_baseChange_rationalRepresentation]
  exact tensor_rationalRepresentation_isSemisimple h22 _ _
    (geometric_rational_of_isSemisimpleStable h419 ρ hρ)
    (geometric_rational_of_isSemisimpleStable h419 σ hσ)

omit [CharZero k] [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] in
/-- The target statement follows from Milne's Theorem 22.42 and Proposition 4.19. -/
theorem charZeroSemisimpleRepresentationIdentityComponent_of
    (h22 : CharZeroReductiveSemisimpleRepresentationStatement.{u})
    (h419 : SemisimpleRepresentationFieldExtensionStatement.{u}) :
    CharZeroSemisimpleRepresentationIdentityComponentStatement.{u} := by
  intro k _ _ G _ _ IsSemisimpleRep
  refine ⟨⟨fun h => identityComponent_isConnectedReductive h22 h419 h,
    fun hG n ρ => isSemisimpleStable_of_identityComponent h419 hG ρ⟩,
    fun n m ρ σ hρ hσ => tensor_isSemisimpleStable h22 h419 ρ σ hρ hσ⟩

end Langlands.GroupScheme.SemisimpleIdentityComponent
