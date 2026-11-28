import Langlands.GroupScheme.Rational.CyclicCenterKernelModel
import Langlands.GroupScheme.Rational.CentralSplitTorsionCocycleLift
import Langlands.GroupScheme.SimplyConnected.CenterCharacterCartan
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # The full centre in simply connected inner type E6 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

/-- The simply connected inner E6 group has full centre `μ₃`, with innerness
expressed as fixedness of every vertex under the actual star action. -/
def TypeE6InnerCenterStatement : Prop :=
  ∀ (F : Type u) [Field F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    IsSimplyConnected G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    (∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex), d.star σ a = a) →
    ∀ (Z : GroupScheme (Spec (CommRingCat.of F))) (z : Z ⟶ G),
      IsSchemeTheoreticCenter z →
      Nonempty (Z ≅ splitRootsOfUnityProduct F (fun _ : PUnit.{u + 1} => 3))

theorem typeE6InnerCenter : TypeE6InnerCenterStatement.{u} := by
  classical
  intro F _ G _ _ d e hsc hcart hinner Z z hz
  let Ω := SeparableClosure F
  let C := d.toralCenter.group
  let X := characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F Ω)).obj C)
  have hcard : Nat.card X = 3 := by
    have h := d.natCard_centerCharacter_eq_cartanDet hsc e (CartanMatrix.E 6) hcart
    rw [CartanMatrix.E₆_det] at h
    exact h
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsAddCyclic X := isAddCyclic_of_prime_card hcard
  let φ : ZMod 3 ≃+ X := addEquivOfAddCyclicCardEq ((Nat.card_zmod 3).trans hcard.symm)
  let ψ : (PUnit.{u + 1} → ZMod 3) ≃+ X :=
    (AddEquiv.piUnique (fun _ : PUnit.{u + 1} => ZMod 3)).trans φ
  have hfix (σ : Ω ≃ₐ[F] Ω) (x : X) :
      characterLattice.galoisRepresentation F Ω C σ x = x := by
    obtain ⟨c, hc⟩ := d.exists_centerCharacter_sum_fundamental hsc x
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, d.centerFundamentalCharacter_galois hsc, hinner]
  let iso := characterLattice.isoOfConstantAbsoluteEquiv d.toralCenter_isMultiplicativeType ψ
    (fun σ y => hfix σ (ψ y))
  exact ⟨d.isoToralCenter hz ≪≫ MultiplicativeTypeGaloisExactness.grpIso iso ≪≫
    HomScheme.FiniteDiagonalizable.diagonalizableIso F PUnit.{u + 1} 3⟩

end Langlands.GroupScheme
