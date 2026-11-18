import Langlands.GroupScheme.Torus.LinearlyReductiveMultiplicativeTypeStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeCharacterizationProof
import Langlands.GroupScheme.Rational.MultiplicativeTypeRepresentationProof
import Langlands.GroupScheme.MatrixRepresentation.SemisimpleAdditiveRoot
import Langlands.GroupScheme.VectorGroupAffineHomExt

/-! # Commutative linear reductivity and multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- All representations being semisimple forces uniqueness of additive characters. -/
theorem subsingleton_additiveHom_of_forall_semisimple
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left]
    (hss : ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
      sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
          U = ⊥ ∨ U = W} = ⊤) :
    Subsingleton (G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1) := by
  apply VectorGroup.subsingleton_hom_of_affineCoordinates_eq_zero
  intro f A x i
  fin_cases i
  exact MatrixRepresentation.additiveRootRepresentation_affineCoordinates_eq_zero
    f (hss 2 (MatrixRepresentation.additiveRootRepresentation f)) A x

/-- A commutative affine group scheme of finite type over any field is linearly
reductive if and only if it is of multiplicative type (Milne, Proposition 12.54). -/
theorem commutativeLinearlyReductiveMultiplicativeType :
    CommutativeLinearlyReductiveMultiplicativeTypeStatement.{u} := by
  intro k _ G _ _ hcomm
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  constructor
  · intro hss
    have hcriterion :
        (IsCommMonObj G.X ∧
          Subsingleton (G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)) ↔
        IsMultiplicativeType G :=
      (multiplicativeTypeCharacterization k G (SeparableClosure k)).out 2 1
    exact hcriterion.mp ⟨hcomm, subsingleton_additiveHom_of_forall_semisimple hss⟩
  · intro hG
    exact (multiplicativeTypeRepresentationGaloisOrbit k G hG (SeparableClosure k)).1

end Langlands.GroupScheme
