import Langlands.GroupScheme.Trigonalizable.ExtensionSplitPerfectSmooth
import Langlands.GroupScheme.Trigonalizable.EtaleExtensionSplitProof

/-! # Splitting of trigonalizable groups (Milne 16.26), proof -/

universe u

namespace Langlands.GroupScheme

/-- **Milne 2017, Theorem 16.26.** The extension `e → U → G → D(Λ) → e` of a
trigonalizable group splits when (a) `k` is algebraically closed, (b) `k` is perfect and
`U` is smooth and connected, or (c) `k` is perfect and `D(Λ)` is connected. The
reduction `trigonalizableExtensionSplit_of_etale` proves cases (a) and (c) outright and
case (b) from its single premise, which `etaleDiagonalizableExtensionSplit` proves. -/
theorem trigonalizableExtensionSplit : TrigonalizableExtensionSplitStatement.{u} :=
  trigonalizableExtensionSplit_of_etale etaleDiagonalizableExtensionSplit.{u}

end Langlands.GroupScheme
