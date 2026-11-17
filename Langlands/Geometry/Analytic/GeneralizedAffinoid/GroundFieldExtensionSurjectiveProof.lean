import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionSurjectiveStatement
import Langlands.Geometry.Analytic.ValuedField.TensorSeminorm
import Langlands.Geometry.Analytic.Spectrum.NonarchimedeanDominationProof
import Langlands.Geometry.Analytic.ValuedField.SeminormRealizationProof
import Langlands.Geometry.Analytic.Spectrum.ResidueField

/-! # Proof that the spectrum projection of a ground field extension is surjective -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open scoped TensorProduct
open BanachSpectrum

/-- A ring map between normed fields that does not increase norms preserves
them: the pulled-back norm is a bounded multiplicative seminorm on the source
field, hence equal to its norm. -/
theorem norm_map_eq_of_norm_map_le {F : Type*} {M : Type*} [NormedField F] [NormedField M]
    (f : F →+* M) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) (a : F) : ‖f a‖ = ‖a‖ := by
  let x : BanachSpectrum F := {
    toFun := fun a => ‖f a‖
    map_zero' := by simp only [map_zero, norm_zero]
    map_one' := by simp only [map_one, norm_one]
    map_mul' := fun a b => by rw [map_mul, norm_mul]
    add_le' := fun a b => by rw [map_add]; exact norm_add_le _ _
    neg' := fun a => by rw [map_neg, norm_neg]
    le_norm := hf
  }
  exact BanachSpectrum.field_apply x a

/-- Every point of the spectrum of a presented `K`-affinoid algebra `A` lifts
to the spectrum of its ground field extension `A_L`. -/
theorem spectrumProjection_surjective : SpectrumProjectionSurjectiveStatement.{u, v} := by
  intro K _ _ _ L _ _ _ _ A x
  -- The completed residue field of `x` and the canonical map `A → 𝓗(x)`.
  let H := CompletedResidueField K x
  let χ : BoundedAlgHom K A H := completedResidueMap K x
  -- A normalized ultrametric seminorm on `𝓗(x) ⊗_K L`, a multiplicative
  -- seminorm below it, and a complete field realizing the latter.
  obtain ⟨p, hp1, hpna, hpH, hpL⟩ :=
    exists_ultrametricTensorSeminorm (E := K) (F := H) (G := L)
  obtain ⟨q, hqna, hqp⟩ := BanachSpectrum.nonarchimedeanDomination (H ⊗[K] L) p hp1 hpna
  obtain ⟨M, _, _, _, r, hr⟩ := seminormRealization (H ⊗[K] L) q hqna
  let f₀ : H →+* M := r.comp Algebra.TensorProduct.includeLeftRingHom
  let g₀ : L →+* M := r.comp Algebra.TensorProduct.includeRight.toRingHom
  have hf (a : H) : ‖f₀ a‖ = ‖a‖ :=
    norm_map_eq_of_norm_map_le f₀
      (fun a => (hr _).le.trans ((hqp _).trans (hpH a))) a
  have hg (b : L) : ‖g₀ b‖ = ‖b‖ :=
    norm_map_eq_of_norm_map_le g₀
      (fun b => (hr _).le.trans ((hqp _).trans (hpL b))) b
  have hcomm (c : K) : f₀ (algebraMap K H c) = g₀ (algebraMap K L c) := by
    change r (Algebra.TensorProduct.includeLeftRingHom (algebraMap K H c)) =
      r (Algebra.TensorProduct.includeRight.toRingHom (algebraMap K L c))
    exact congrArg r (RingHom.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := K) (A := H) (B := L)) c)
  -- `M` as a complete normed `L`-algebra and `K`-algebra.
  let : Algebra L M := g₀.toAlgebra
  let : NormedAlgebra L M := {
    norm_smul_le := fun c m => by
      rw [Algebra.smul_def, norm_mul]
      change ‖g₀ c‖ * ‖m‖ ≤ ‖c‖ * ‖m‖
      rw [hg] }
  let : Algebra K M := (g₀.comp (algebraMap K L)).toAlgebra
  let : NormedAlgebra K M := {
    norm_smul_le := fun c m => by
      rw [Algebra.smul_def, norm_mul]
      change ‖g₀ (algebraMap K L c)‖ * ‖m‖ ≤ ‖c‖ * ‖m‖
      rw [hg, norm_algebraMap'] }
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- The bounded `K`-algebra map `A → 𝓗(x) → M`.
  let φ : BoundedAlgHom K A M := {
    toRingHom := f₀.comp χ.toAlgHom.toRingHom
    commutes' := fun c => by
      change f₀ (χ.toAlgHom (algebraMap K A c)) = g₀ (algebraMap K L c)
      rw [χ.toAlgHom.commutes c]
      exact hcomm c
    bounded := by
      obtain ⟨C, hC, hχ⟩ := χ.bounded
      exact ⟨C, hC, fun a => (hf _).le.trans (hχ a)⟩ }
  -- Its extension `A_L → M` and the pulled-back norm.
  let ψ := lift K L A M φ
  refine ⟨BanachSpectrum.comap ψ.toBoundedRingHom (fieldPoint M), ?_⟩
  apply BanachSpectrum.ext
  intro a
  change ‖ψ (iota K L A a)‖ = x a
  rw [lift_iota]
  change ‖f₀ (χ a)‖ = x a
  rw [hf]
  exact norm_completedResidueMap K x a

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
