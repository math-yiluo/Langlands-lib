import Langlands.Representation.Induction.InducingRepresentationRecovery
import Langlands.Representation.Induction.IrreducibilityReflection
import Langlands.Group.GL.Nonarchimedean
import Langlands.Group.GL.LocalFieldTopology
import Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.Representation.Classification.ProductLeviTemperedFactorizationAdapter
import Langlands.Representation.Smooth.Schur.Proof

/-!
# Recovering the inducing data of an irreducible admissible block induction

Over a nonarchimedean local field, the smooth Levi representation underlying an
irreducible admissible unnormalized smooth block induction is itself irreducible
and admissible. Schur's lemma then gives a scalar character on the block scalars.
See the paired Markdown.
-/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

universe u w

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {n : ℕ} (B : BlockShape n)
variable {X : Type w} [AddCommGroup X] [Module ℂ X]

/-- If the unnormalized smooth induction of a smooth Levi representation `Ξ` from the standard
block parabolic subgroup is irreducible and admissible, then so is `Ξ`. -/
theorem isIrreducible_isAdmissible_of_smoothInduced {Ξ : Representation ℂ (B.Levi F) X}
    (hΞ : IsSmooth Ξ)
    (hirr : (Induction.smoothInduced (B.parabolic F) (Ξ.comp (B.leviProjection F))).IsIrreducible)
    (hadm : IsAdmissible
      (Induction.smoothInduced (B.parabolic F) (Ξ.comp (B.leviProjection F)))) :
    Ξ.IsIrreducible ∧ IsAdmissible Ξ := by
  have := valuativeGeneralLinearNonarchimedean F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have hm := (B.leviProjectionContinuous F).continuous
  have hmo : IsOpenMap (B.leviProjection F) :=
    isOpenMap_snd.comp (B.decompositionHomeomorph F).isOpenMap
  have hms : Function.Surjective (B.leviProjection F) :=
    fun m => ⟨B.leviInParabolic F m, B.leviProjection_section F m⟩
  have hτ := isSmooth_comp (B.leviProjection F) hm hΞ
  exact ⟨Induction.isIrreducible_of_comp_surjective _ hms Ξ
      (Induction.isIrreducible_of_smoothInduced _ _ hτ hirr),
    (isAdmissible_comp_iff_of_open_surjective Ξ _ hm hmo hms).mp
      (Induction.isAdmissible_of_smoothInduced _ _ hτ hadm)⟩

/-- The block scalars act on an irreducible admissible Levi representation through a character
of `(F^×)^{B.length}` with open kernel (Schur's lemma). -/
theorem exists_blockScalarCharacter {Ξ : Representation ℂ (B.Levi F) X}
    (hadm : IsAdmissible Ξ) (hirr : Ξ.IsIrreducible) :
    ∃ χ : (Fin B.length → Fˣ) →* ℂˣ, IsOpen (χ.ker : Set (Fin B.length → Fˣ)) ∧
      Classification.HasScalarCharacter Ξ (B.blockScalarLevi F) χ := by
  obtain ⟨ω, ⟨-, hω⟩, -⟩ := admissibleSchur_centralCharacter Ξ hadm hirr
  let χ : (Fin B.length → Fˣ) →* ℂˣ := ω.comp (B.blockScalarToCenter F)
  have hχ : Classification.HasScalarCharacter Ξ (B.blockScalarLevi F) χ :=
    fun a v => hω (B.blockScalarToCenter F a) v
  have : IsSimpleModule (MonoidAlgebra ℂ (B.Levi F)) Ξ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule Ξ).mp hirr
  have : Nontrivial X := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (B.Levi F)) Ξ.asModule
  exact ⟨χ, hχ.isOpen_ker
    (ProductLeviTemperedFactorization.continuous_blockScalarLevi B F) hadm.1, hχ⟩

end Langlands.GeneralLinear.BlockShape
