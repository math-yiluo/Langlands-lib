import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.Global.HeckeNormPower
import Langlands.Global.IdeleNormAbsoluteValue
import Langlands.ClassField.Global.LocalRelativeWeilMap

/-! # Norms of completions and of norm powers -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global Langlands.Global.CompletionPadic Langlands.Global.AdelicFunctoriality
open scoped NumberField

variable {k M : Type u} [Field k] [Field M] [NumberField k] [NumberField M] [Algebra k M]

/-- The local norm of the completions is the field norm for the standalone embedding of the
canonical packages. -/
theorem localUnitNorm_eq_units_map_norm (z : HeightOneSpectrum (𝓞 k))
    (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver z.asIdeal] (x : (u.adicCompletion M)ˣ) :
    FiniteExtension.localUnitNorm z u x =
      Units.map (@Algebra.norm (padicField z).Carrier (towerPadicField z u).Carrier _ _
        (Weil.Local.extensionAlgebra (padicField z) (towerPadicField z u)
          (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z u))) x :=
  rfl

/-- `‖·‖^t ∘ N_{M/k} = ‖·‖^t`: the idelic norm preserves the normalized absolute value. -/
theorem normComp_normPower (t : ℂ) :
    HeckeCharacter.normComp (L := M) (HeckeCharacter.normPower k t) =
      HeckeCharacter.normPower M t := by
  refine DFunLike.ext _ _ fun a => ?_
  induction a using QuotientGroup.induction_on with
  | H x =>
    apply Units.ext
    change ((HeckeCharacter.normPower k t) (ideleClassNorm (K := k) (L := M)
      (QuotientGroup.mk x)) : ℂ) = _
    rw [HeckeCharacter.normPower_apply, HeckeCharacter.normPower_apply, ideleClassNorm_mk]
    change Complex.exp (t * ((Real.log ((IdeleAbsoluteValue.full k (ideleNorm x) : NNReal) :
      ℝ) : ℝ) : ℂ)) = Complex.exp (t * ((Real.log ((IdeleAbsoluteValue.full M x : NNReal) :
        ℝ) : ℝ) : ℂ))
    rw [full_ideleNorm]

end Langlands.LocalFactor.NonabelianBrauer
