import Langlands.BaseChange.ExactNormAssociatedMeasure
import Langlands.BaseChange.LeviBlockCentralizer
import Langlands.BaseChange.RegularLeviNormRepresentative
import Langlands.Analysis.Local.LeftQuotientProduct

/-! Exact block norms and the two ways to identify the twisted centralizer. -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.GeneralLinear Langlands.JacquetLanglands Langlands.QuotientIntegration

universe u v

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
  {n l : ℕ} {σ : E ≃ₐ[F] E} (B : BlockShape n) (L : B.Levi F) (D : B.Levi E)

/-- Exact block norms give the exact norm of the block diagonal element. -/
theorem cyclicNorm_leviEmbedding_eq_of_blockwise
    (hn : ∀ i, cyclicNorm σ l (D i) = baseChange F E (B.size i) (L i)) :
    cyclicNorm σ l (B.leviEmbedding E D) = baseChange F E n (B.leviEmbedding F L) := by
  rw [cyclicNorm_leviEmbedding, baseChange_leviEmbedding]
  exact congrArg (B.leviEmbedding E) (funext hn)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]

local notation "C" => fun i => glCentralizer (L i)
local notation "Cσ" => fun i => sigmaCentralizer σ (B.size i) (D i)

variable (hσ : IsCyclicAlgebra σ l) (hReg : ∀ i, IsRegularSemisimple (L i))
  (hn : ∀ i, cyclicNorm σ l (D i) = baseChange F E (B.size i) (L i))

/-- The subgroup of ordinary block centralizers maps to the subgroup of twisted block
centralizers by the product of the exact-norm isomorphisms. -/
def exactNormBlockCentralizerEquiv :
    (Subgroup.pi Set.univ C) ≃ₜ* (Subgroup.pi Set.univ Cσ) := by
  let e i := exactNormCentralizerEquiv hσ (hReg i) (hn i)
  let ePi : (∀ i, C i) ≃ₜ* ∀ i, Cσ i :=
    { toMulEquiv := MulEquiv.piCongrRight fun i => (e i).toMulEquiv
      continuous_toFun := continuous_pi fun i => (e i).continuous.comp (continuous_apply i)
      continuous_invFun := continuous_pi fun i => (e i).symm.continuous.comp (continuous_apply i) }
  exact (piSubgroupHomeomorph C).trans (ePi.trans (piSubgroupHomeomorph Cσ).symm)

@[simp] theorem exactNormBlockCentralizerEquiv_coordinate
    (a : Subgroup.pi Set.univ C) (i : Fin B.length) :
    piSubgroupHomeomorph Cσ (exactNormBlockCentralizerEquiv B L D hσ hReg hn a) i =
      exactNormCentralizerEquiv hσ (hReg i) (hn i) (piSubgroupHomeomorph C a i) := rfl

variable (hΓ : IsRegularSemisimple (B.leviEmbedding F L))
  (hCop : Pairwise fun i j => IsCoprime (L i).val.charpoly (L j).val.charpoly)

/-- Identify the subgroup of twisted block centralizers with the ambient twisted
centralizer. The route passes through the ordinary block and ambient centralizers. -/
def sigmaLeviCentralizerEquiv :
    (Subgroup.pi Set.univ Cσ) ≃ₜ* sigmaCentralizer σ n (B.leviEmbedding E D) :=
  (exactNormBlockCentralizerEquiv B L D hσ hReg hn).symm.trans
    ((piSubgroupHomeomorph C).trans ((glCentralizerLeviPiEquiv B L hCop).symm.trans
      (exactNormCentralizerEquiv hσ hΓ (cyclicNorm_leviEmbedding_eq_of_blockwise B L D hn))))

/-- On elements, the twisted centralizer isomorphism is the actual Levi embedding. -/
theorem sigmaLeviCentralizerEquiv_apply_val (a : Subgroup.pi Set.univ Cσ) :
    (sigmaLeviCentralizerEquiv B L D hσ hReg hn hΓ hCop a).val = B.leviEmbedding E a.val := by
  let e := exactNormBlockCentralizerEquiv B L D hσ hReg hn
  let b := e.symm a
  have hb (i : Fin B.length) : baseChange F E (B.size i) (b.val i) = a.val i := by
    have he := exactNormBlockCentralizerEquiv_coordinate B L D hσ hReg hn b i
    change piSubgroupHomeomorph Cσ (e (e.symm a)) i = _ at he
    rw [ContinuousMulEquiv.apply_symm_apply] at he
    have hVal := congrArg Subtype.val he
    rw [exactNormCentralizerEquiv_apply_val] at hVal
    exact hVal.symm
  change (exactNormCentralizerEquiv hσ hΓ (cyclicNorm_leviEmbedding_eq_of_blockwise B L D hn)
    ((glCentralizerLeviPiEquiv B L hCop).symm (piSubgroupHomeomorph C b))).val = _
  rw [exactNormCentralizerEquiv_apply_val, glCentralizerLeviPiEquiv_symm_apply_val,
    baseChange_leviEmbedding]
  exact congrArg (B.leviEmbedding E) (funext hb)

end Langlands.BaseChange
