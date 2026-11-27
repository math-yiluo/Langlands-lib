import Langlands.GroupScheme.Rational.CyclicCenterKernelModel
import Langlands.GroupScheme.Rational.CentralSplitTorsionCocycleLift
import Langlands.GroupScheme.SimplyConnected.CenterCharacterCartan
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # The centre of a simply connected group of type `E_7` is `μ_2` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- In an additive group with two elements every injective endomorphism is the identity. -/
theorem eq_self_of_natCard_eq_two {X : Type*} [AddGroup X] (h : Nat.card X = 2) (f : X →+ X)
    (hf : Function.Injective f) (x : X) : f x = x := by
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  by_cases hx : x = 0
  · rw [hx, map_zero]
  have hfx : f x ≠ 0 := fun h0 => hx (hf (h0.trans (map_zero f).symm))
  by_contra hne
  have hinj : Function.Injective (![0, x, f x] : Fin 3 → X) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, h] at this
  omega

namespace TitsIndexData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

local notation "Ω" => SeparableClosure k
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)

/-- The full centre of a simply connected group whose Tits index is numbered by the Cartan
matrix of type `E_7` is isomorphic over the ground field to `μ_2`, in the form of a split
product of roots-of-unity groups with one factor. -/
theorem nonempty_center_iso_of_typeE7 (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 7)
    (hE7 : ∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b))
    {Z : GroupScheme (Spec (CommRingCat.of k))} {z : Z ⟶ G} (hz : IsSchemeTheoreticCenter z) :
    Nonempty (Z ≅ splitRootsOfUnityProduct k (fun _ : PUnit.{u + 1} => 2)) := by
  classical
  let C := d.toralCenter.group
  have hZ : IsMultiplicativeType C.toGrp := d.toralCenter_isMultiplicativeType
  have hcard : Nat.card (characterLattice ((BC).obj C)) = 2 := by
    have hc := d.natCard_centerCharacter_eq_cartanDet hsc e (CartanMatrix.E 7) hE7
    rw [CartanMatrix.E₇_det] at hc
    exact hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsAddCyclic (characterLattice ((BC).obj C)) := isAddCyclic_of_prime_card hcard
  let eC : ZMod 2 ≃+ characterLattice ((BC).obj C) :=
    addEquivOfAddCyclicCardEq ((Nat.card_zmod 2).trans hcard.symm)
  let ρ := characterLattice.galoisRepresentation k Ω C
  have hfix (σ : Ω ≃ₐ[k] Ω) (x : characterLattice ((BC).obj C)) : ρ σ x = x := by
    have hinj : Function.Injective (ρ σ) := by
      intro x y hxy
      have h := congrArg (ρ σ⁻¹) hxy
      rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
        ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
    exact eq_self_of_natCard_eq_two hcard (ρ σ).toAddMonoidHom hinj x
  let eM : (PUnit.{u + 1} → ZMod 2) ≃+ characterLattice ((BC).obj C) :=
    (AddEquiv.piUnique (fun _ : PUnit.{u + 1} => ZMod 2)).trans eC
  let eZ := characterLattice.isoOfConstantAbsoluteEquiv hZ eM (fun σ m => hfix σ (eM m))
  exact ⟨d.isoToralCenter hz ≪≫ MultiplicativeTypeGaloisExactness.grpIso eZ ≪≫
    HomScheme.FiniteDiagonalizable.diagonalizableIso k PUnit.{u + 1} 2⟩

end TitsIndexData

end Langlands.GroupScheme
