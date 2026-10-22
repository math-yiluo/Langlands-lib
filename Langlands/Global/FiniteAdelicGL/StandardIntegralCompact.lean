import Langlands.Global.FiniteAdelicGL.StandardIntegralStatement
import Langlands.Global.IntegralFiniteAdeles
import Langlands.Group.GL.IntegralSubgroup

noncomputable section

universe u

namespace Langlands.Global.FiniteAdelicGL

open NumberField IsDedekindDomain
open scoped RestrictedProduct

variable (K : Type u) [Field K] [NumberField K]

/-- The two integral-adele subrings have the same coordinatewise carrier. -/
theorem integralAdeles_eq_integralFiniteAdeles :
    integralAdeles K = Langlands.Global.integralFiniteAdeles K := by
  ext a
  rfl

/-- The matrix locus with everywhere-integral entries is compact, including rank zero. -/
theorem isCompact_integralMatrices (n : ℕ) :
    IsCompact (integralMatrices K n :
      Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) := by
  rw [integralMatrices_eq_pi]
  exact isCompact_univ_pi fun _ : Fin n =>
    isCompact_univ_pi fun _ : Fin n => Langlands.Global.isCompact_integralFiniteAdeles K

/-- The standard integral subgroup is compact for the actual finite adelic units topology. -/
theorem isCompact_standardIntegral (n : ℕ) :
    IsCompact (standardIntegral K n : Set (Langlands.Global.FiniteAdelicGL K n)) := by
  let : T2Space (FiniteAdeleRing (𝓞 K) K) := inferInstanceAs
    (T2Space (Πʳ v : HeightOneSpectrum (𝓞 K),
      [v.adicCompletion K, v.adicCompletionIntegers K]))
  exact Langlands.GeneralLinearGroup.isCompact_integralSubgroup
    (Fin n) (integralAdeles K) (Langlands.Global.isCompact_integralFiniteAdeles K)

/-- The published compactness statement for all number fields and all natural ranks. -/
theorem standardIntegralCompact : StandardIntegralCompactStatement.{u} := by
  intro K _ _ n
  exact isCompact_standardIntegral K n

end Langlands.Global.FiniteAdelicGL
