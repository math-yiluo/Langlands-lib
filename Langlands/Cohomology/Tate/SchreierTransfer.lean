import Langlands.Cohomology.Tate.HomologyTransferRepresentatives
import Langlands.Cohomology.Tate.LowDegree

noncomputable section

universe u v

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {G : Type u} [Group G] [Fintype G]
variable (H : Subgroup G) [Fintype (G ⧸ H)]

/-- Mathlib's group-theoretic transfer is the product of the chosen Schreier factors. -/
lemma groupTransfer_schreier {B : Type v} [CommGroup B] (φ : H →* B) (g : G) :
    MonoidHom.transfer φ g = ∏ q : G ⧸ H, φ (schreierElement H g q) := by
  classical
  let T : H.LeftTransversal :=
    ⟨Set.range (fun q : G ⧸ H => q.out),
      Subgroup.isComplement_range_left (fun q => Quotient.out_eq' q)⟩
  have hT (q : G ⧸ H) : (T.2.leftQuotientEquiv q : G) = q.out :=
    Subgroup.IsComplement.leftQuotientEquiv_apply (fun q => Quotient.out_eq' q) q
  rw [MonoidHom.transfer_def φ T]
  dsimp only [Subgroup.leftTransversals.diff]
  rw [show H.fintypeQuotientOfFiniteIndex = (inferInstance : Fintype (G ⧸ H))
    from Subsingleton.elim _ _]
  apply Finset.prod_congr rfl
  intro q _
  congr 1
  apply Subtype.ext
  change (T.2.leftQuotientEquiv q : G)⁻¹ * ((g • T).2.leftQuotientEquiv q : G) =
    q.out⁻¹ * g * (g⁻¹ • q).out
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, hT, hT]
  simp only [smul_eq_mul, mul_assoc]

/-- The additive form of the actual abelianization transfer on a group representative. -/
lemma abelianizationTransfer_schreier (g : G) :
    abelianizationTransfer H (Additive.ofMul (Abelianization.of g)) =
      ∑ q : G ⧸ H, Additive.ofMul (Abelianization.of (schreierElement H g q)) := by
  change Additive.ofMul (MonoidHom.transfer (Abelianization.of : H →* Abelianization H) g) = _
  rw [groupTransfer_schreier]
  rfl

omit [Fintype G] [Fintype (G ⧸ H)] in
/-- In dimension one the standard chain formula has exactly the group-transfer factors. -/
lemma transferTuple_one (g : G) (q : G ⧸ H) :
    transferTuple H 1 (fun _ => g) q = fun _ => schreierElement H g q := by
  funext i
  fin_cases i
  change (cosetCoordinate H (q.out⁻¹ * Fin.partialProd (fun _ : Fin 1 => g) 0))⁻¹ *
      cosetCoordinate H (q.out⁻¹ * Fin.partialProd (fun _ : Fin 1 => g) 1) =
    schreierElement H g q
  have hp : Fin.partialProd (fun _ : Fin 1 => g) (1 : Fin 2) = g := by
    have hs := Fin.partialProd_succ (fun _ : Fin 1 => g) (0 : Fin 1)
    change Fin.partialProd (fun _ : Fin 1 => g) 1 =
      Fin.partialProd (fun _ : Fin 1 => g) 0 * g at hs
    simpa only [Fin.partialProd_zero, one_mul] using hs
  rw [Fin.partialProd_zero, mul_one, hp]
  rw [cosetCoordinate_inverse_out, inv_one, one_mul, cosetCoordinate_inverse_out_mul]

end Langlands.Tate
