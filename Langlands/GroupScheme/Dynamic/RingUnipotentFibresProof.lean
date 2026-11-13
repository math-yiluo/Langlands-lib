import Langlands.GroupScheme.Dynamic.RingUnipotentFibresStatement
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Proof: unipotent fibres of dynamic unipotent subgroups over a ring -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Fibral unipotence of `U_G(χ)` over a ring** (CGP Lemma 2.1.5; Conrad,
*Reductive group schemes*, Theorem 4.1.7(4), last sentence). Base change of a representative
of `U_G(χ)` along a field point `y` represents `U_{G_K}(χ_K)`, which is unipotent by the
published field case. -/
theorem dynamicRingUnipotentFibres : DynamicRingUnipotentFibresStatement.{u} := by
  intro R _ G _ _ χ H j hj K _ y
  have hGa : IsAffineHom ((GroupScheme.baseChange y).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom y)
    infer_instance
  have hGf : LocallyOfFiniteType ((GroupScheme.baseChange y).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom y)
    infer_instance
  have hrep : (Dynamic.unipotent (Dynamic.baseChangeCocharacter y χ)).IsRepresentedBy
      ((GroupScheme.baseChange y).map j) := by
    rw [Dynamic.unipotent_baseChange]
    exact hj.baseChange y
  exact dynamicUnipotentUnipotence K ((GroupScheme.baseChange y).obj G)
    (Dynamic.baseChangeCocharacter y χ) ((GroupScheme.baseChange y).obj H)
    ((GroupScheme.baseChange y).map j) hrep

end Langlands.GroupScheme
