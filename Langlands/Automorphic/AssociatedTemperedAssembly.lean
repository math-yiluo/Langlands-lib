import Langlands.Automorphic.AssociatedTemperedLocalProof
import Langlands.Global.Factors.TemperedPoleRegions
import Langlands.ClassFieldTheory.Local.ReciprocitySystemStatement

/-! # Global assembly of the associated tempered factor comparison -/

noncomputable section

universe u uV uP uQ uE

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open LocalFactor LocalFactor.CommonClosure Correspondence

/-- Select one actual local-constant system from normalized reciprocity and
the existence theorem for each supplied normalized family. -/
def localConstantSystemOfExistence {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)
    (hrec : ∃ eC : ReciprocityFamily K, NormalizedReciprocity K eC)
    (hsys : ∀ eC : ReciprocityFamily K, NonabelianSystem.Exists.{u, uE} K eC) :
    Σ eC : ReciprocityFamily K,
      {ε : NonabelianSystem.Assignment.{u, uE} K // NonabelianSystem.IsSystem K eC ε} := by
  let eC := Classical.choose hrec
  have heC : NormalizedReciprocity K eC := Classical.choose_spec hrec
  let hε := hsys eC heC
  exact ⟨eC, Classical.choose hε, Classical.choose_spec hε⟩

/-- Conditional assembly with the exact global conclusion. The three input
theorems remain explicit until their unconditional proofs are published. -/
theorem associatedTemperedFactor_of_gamma_and_existence
    (hgamma : AssociatedGammaStatement.{u, uV, uP, uQ, uE})
    (hrec : LocalClassField.CommonClosureReciprocityExistence.{u})
    (hsys : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{u} p)
      (eC : ReciprocityFamily K), NonabelianSystem.Exists.{u, uE} K eC) :
    AssociatedTemperedFactorStatement.{u, uV, uP, uQ, uE} := by
  intro c hc F E _ _ _ _ _ _ _ ψ hψ r t S S' T T' hS hS'
    P P' v hI hA hI' hA' ht ht' w e ι hι hu hu' ψv hψv
  obtain ⟨eC₀, ε₀, hε₀⟩ := localConstantSystemOfExistence (padicField v)
    (hrec _ (padicField v) (padicField v).canonicalTopologicalData)
    (hsys _ (padicField v))
  have hpoles := Global.FactorSeparation.certifiedAutomorphicPoleRegions_of_tempered
    (padicField v) ψv ((P.localComponent v).padicObject hI hA)
    ((P'.localComponent v).padicObject hI' hA') ht ht'
  exact isPairFactorMatch_localPairClass_of_unitary_gamma S S' ι ψv
    ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA')
    hu hu' hpoles eC₀ ε₀ hε₀
    (hgamma c hc F E ψ hψ S S' T T' hS hS' P P' v hI hA hI' hA'
      w e ι hι ψv hψv)

end Langlands.ClassField.Global.RelativeWeilGroup
