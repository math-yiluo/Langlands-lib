import Langlands.Global.Arithmetic.GeneralPositionMackeyProof
import Langlands.Global.Arithmetic.HarrisCyclicPrimeTowerProof
import Mathlib.Order.Fin.Basic

/-!
# Harris's sufficient condition for general position

The published cyclic prime-step tower theorem and the exact-stabilizer
irreducibility criterion apply to the actual Galois-closure Weil subgroup.
-/

noncomputable section

universe uF

namespace Langlands.Global

open LocalFactor.CommonClosure GeneralPosition

private theorem generalPosition_of_irreducible_mackey
    (tower_exists : HarrisCyclicPrimeTowerStatement.{uF})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (χ : weilSubgroup F F' →ₜ* ℂˣ)
    (hirr : ∀ (K : Subgroup (Weil.Local.localWeilGroup F)),
      weilSubgroup F (galoisClosure F F') ≤ K →
      ∀ g : Weil.Local.localWeilGroup F,
        (mackeyConstituent (weilSubgroup F F') K
          (FiniteRepresentation.characterLine.{uF, 0} χ.toMonoidHom) g).IsIrreducible) :
    IsInGeneralPosition F F' χ := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : IsGalois F.Carrier (galoisClosure F F').field := by
    change IsGalois F.Carrier
      (IntermediateField.normalClosure F.Carrier F'.field (AlgebraicClosure F.Carrier))
    infer_instance
  obtain ⟨t, tower, htop, hbot, hstep⟩ := tower_exists p F (galoisClosure F F')
  refine ⟨t, tower, htop, hbot, hstep, ?_⟩
  have hanti : Antitone (fun i => (tower i).field) :=
    Fin.antitone_iff_succ_le.mpr (fun i => (hstep i).choose)
  intro i g
  have hfield : (tower i).field ≤ (galoisClosure F F').field := by
    rw [← htop]
    exact hanti (Fin.zero_le i)
  exact hirr (weilSubgroup F (tower i))
    (weilSubgroup_antitone F (tower i) (galoisClosure F F') hfield) g

/-- Harris's exact Weil stabilizer condition implies general position at every
level of a cyclic prime-step tower from the actual Galois closure to the base. -/
theorem generalPositionOfExactStabilizer :
    GeneralPositionOfExactStabilizerStatement.{uF} := by
  intro p _ F F' χ hexact
  apply generalPosition_of_irreducible_mackey harrisCyclicPrimeTower F F' χ
  intro K hNK g
  exact mackeyConstituent_irreducible_of_exactStabilizer
    (weilSubgroup F (galoisClosure F F')) (weilSubgroup F F') K
    (galoisClosure_weilSubgroup_le F F') hNK χ.toMonoidHom hexact g

end Langlands.Global
