import Langlands.Representation.RankinSelberg.InducedWhittakerQuotient
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.RankinSelberg.AnalyticBridge
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
/-! # Actual induced quotients onto block coefficient models -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker
open Langlands.AllField.Whittaker

universe uR uG uV uW


end Langlands.AllField.Whittaker

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.GeneralLinear hiding SupercuspidalClass blockSum rankInclusion

universe uF uV uW

variable {F : Type uF} [Field F]
  (T : LocalFieldData F)

/-- The actual normalized parabolic map is surjective for smooth endpoints
in independent carrier universes. -/
theorem normalizedParabolicInducedMap_surjective {n : ℕ} (B : BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (B.Levi F) V)
    (τ : Representation ℂ (B.Levi F) W)
    (hσ : letI := T.topology; IsSmooth σ)
    (hτ : letI := T.topology; IsSmooth τ)
    (f : σ.IntertwiningMap τ) (hf : Function.Surjective f) :
    letI := T.topology
    Function.Surjective (T.normalizedParabolicInducedMap B f) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  let χ := B.inflateCharacter (T.leviHalfCharacter B)
  apply Induction.smoothInductionSurjectivity (GeneralLinear n F)
  · intro K
    let L := T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L.1, L.2.1, L.2.2⟩
  · exact B.isClosed_parabolic F
  · exact (isSmooth_twist_iff χ.toMonoidHom _ χ.isOpen_ker).mpr
      (isSmooth_comp (B.leviProjection F)
        (B.leviProjectionContinuous F).continuous hσ)
  · exact (isSmooth_twist_iff χ.toMonoidHom _ χ.isOpen_ker).mpr
      (isSmooth_comp (B.leviProjection F)
        (B.leviProjectionContinuous F).continuous hτ)
  · exact hf

/-- The actual normalized product map from a block family to its specified
coefficient-image family. -/
def normalizedProductModelMap {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    {N : ∀ i, Subgroup (GeneralLinear (B.size i) F)}
    {θ : ∀ i, N i →* ℂˣ}
    (ℓ : ∀ i, Whittaker.functionals (N i) (θ i) (σ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B σ).IntertwiningMap
      (T.normalizedProductInduced B
        (V := fun i => (Whittaker.coefficientModel (σ i) (ℓ i)).toSubmodule)
        (fun i => Whittaker.modelRepresentation (σ i) (ℓ i))) := by
  let := T.topology
  let W : Fin B.length → Type uF :=
    fun i => (Whittaker.coefficientModel (σ i) (ℓ i)).toSubmodule
  let : ∀ i, AddCommGroup (W i) := fun i => inferInstance
  let : ∀ i, Module ℂ (W i) := fun i => inferInstance
  let τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i) :=
    fun i => Whittaker.modelRepresentation (σ i) (ℓ i)
  let f : ∀ i, (σ i).IntertwiningMap (τ i) :=
    fun i => Whittaker.modelMap (σ i) (ℓ i)
  exact T.normalizedProductInducedMap B (V := V) (W := W) (σ := σ) (τ := τ) f

/-- Normalized induction of the actual block coefficient quotient maps is a
surjection; neither the originals nor their coefficient maps need be injective. -/
theorem normalizedProductModelMap_surjective {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (hσ : letI := T.topology; ∀ i, IsSmooth (σ i))
    {N : ∀ i, Subgroup (GeneralLinear (B.size i) F)}
    {θ : ∀ i, N i →* ℂˣ}
    (ℓ : ∀ i, Whittaker.functionals (N i) (θ i) (σ i)) :
    letI := T.topology
    Function.Surjective (T.normalizedProductModelMap B σ ℓ) := by
  let := T.topology
  let W : Fin B.length → Type uF :=
    fun i => (Whittaker.coefficientModel (σ i) (ℓ i)).toSubmodule
  let : ∀ i, AddCommGroup (W i) := fun i => inferInstance
  let : ∀ i, Module ℂ (W i) := fun i => inferInstance
  let τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (W i) :=
    fun i => Whittaker.modelRepresentation (σ i) (ℓ i)
  let f : ∀ i, (σ i).IntertwiningMap (τ i) :=
    fun i => Whittaker.modelMap (σ i) (ℓ i)
  have hτ : ∀ i, IsSmooth (τ i) := by
    intro i
    exact Whittaker.model_isSmooth (σ i) (hσ i) (ℓ i)
  have hf : ∀ i, Function.Surjective (f i) := by
    intro i
    exact Whittaker.modelMap_surjective (σ i) (ℓ i)
  exact T.normalizedParabolicInducedMap_surjective B
    (B.blockTensor σ) (B.blockTensor τ)
    (FiniteTensor.isSmooth_external σ hσ) (FiniteTensor.isSmooth_external τ hτ)
    (FiniteTensor.externalMap f)
    (FiniteTensor.externalMapSurjectivity ℂ _ _ _ _ _ _ f hf)

end Langlands.LocalFieldData

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.Whittaker
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear

universe uF uV uW


end Langlands.AllField.RankinSelberg
