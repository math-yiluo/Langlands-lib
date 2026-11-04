import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Reductive.ToPseudoReductive

/-! # Pseudo-reductive and connected reductive groups over algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, triviality of the ground-field radical
already implies triviality of the geometric radical. -/
theorem IsPseudoReductive.isConnectedReductive_of_isAlgClosed
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsPseudoReductive G) :
    IsConnectedReductive G where
  smooth := hG.smooth
  isAffineHom := hG.isAffineHom
  connectedSpace := hG.connectedSpace
  hasTrivialGeometricUnipotentRadical :=
    hG.hasTrivialUnipotentRadical.baseChange_of_bijective
      (algebraMap k (AlgebraicClosure k)) IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Pseudo-reductivity and connected reductivity coincide over an algebraically
closed field. -/
theorem isPseudoReductive_iff_isConnectedReductive_of_isAlgClosed
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    IsPseudoReductive G ↔ IsConnectedReductive G :=
  ⟨IsPseudoReductive.isConnectedReductive_of_isAlgClosed,
    IsConnectedReductive.isPseudoReductive⟩

/-- The identity on group schemes identifies the pseudo-reductive and connected
reductive subtypes over an algebraically closed field. -/
def pseudoReductiveEquivConnectedReductive
    (k : Type u) [Field k] [IsAlgClosed k] :
    {G : GroupScheme (Spec (CommRingCat.of k)) // IsPseudoReductive G} ≃
      {G : GroupScheme (Spec (CommRingCat.of k)) // IsConnectedReductive G} where
  toFun G := ⟨G.val, G.property.isConnectedReductive_of_isAlgClosed⟩
  invFun G := ⟨G.val, G.property.isPseudoReductive⟩
  left_inv _G := Subtype.ext rfl
  right_inv _G := Subtype.ext rfl

@[simp] theorem pseudoReductiveEquivConnectedReductive_apply_val
    (G : {G : GroupScheme (Spec (CommRingCat.of k)) // IsPseudoReductive G}) :
    (pseudoReductiveEquivConnectedReductive k G).val = G.val := rfl

@[simp] theorem pseudoReductiveEquivConnectedReductive_symm_apply_val
    (G : {G : GroupScheme (Spec (CommRingCat.of k)) // IsConnectedReductive G}) :
    ((pseudoReductiveEquivConnectedReductive k).symm G).val = G.val := rfl

end Langlands.GroupScheme
