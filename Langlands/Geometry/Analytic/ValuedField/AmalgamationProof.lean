import Langlands.Geometry.Analytic.ValuedField.AmalgamationStatement
import Langlands.Geometry.Analytic.ValuedField.TensorSeminormStatement
import Langlands.Geometry.Analytic.ValuedField.TensorSeminorm
import Langlands.Geometry.Analytic.Spectrum.NonarchimedeanDominationProof
import Langlands.Geometry.Analytic.ValuedField.SeminormRealizationProof
import Langlands.Geometry.Analytic.Spectrum.Properties

/-! # Isometric amalgamation of complete ultrametric fields -/

noncomputable section

universe u

namespace Langlands.Analytic

open scoped TensorProduct

/-- The projective tensor construction supplies the complete-field tensor interface. -/
theorem tensorSeminormStatement : TensorSeminormStatement.{u} := by
  intro E F G hE hEultra hEc hF hFultra hFc hEF hG hGultra hGc hEG
  exact exists_ultrametricTensorSeminorm (E := E) (F := F) (G := G)

private theorem norm_eq_of_contracting_ringHom
    {F L : Type u} [NormedField F] [NormedField L]
    (f : F →+* L) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) (a : F) : ‖f a‖ = ‖a‖ := by
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

/-- The tensor-seminorm construction suffices for complete field amalgamation. -/
theorem completeFieldAmalgamation_of_tensorSeminorm
    (ht : TensorSeminormStatement.{u})
    (hd : BanachSpectrum.NonarchimedeanDominationStatement.{u})
    (hr : SeminormRealizationStatement.{u}) :
    CompleteFieldAmalgamationStatement.{u} := by
  intro K _ _ _ E F G _ _ _ _ _ _ _ _ _ _ _ _
    i j hi hj
  let : Algebra E F := i.toAlgHom.toRingHom.toAlgebra
  let : Algebra E G := j.toAlgHom.toRingHom.toAlgebra
  have hni (a : E) : ‖algebraMap E F a‖ = ‖a‖ :=
    hi.norm_map_of_map_zero (map_zero i.toAlgHom) a
  have hnj (a : E) : ‖algebraMap E G a‖ = ‖a‖ :=
    hj.norm_map_of_map_zero (map_zero j.toAlgHom) a
  let : NormedAlgebra E F := {
    norm_smul_le a b := by
      rw [Algebra.smul_def, norm_mul, hni]
  }
  let : NormedAlgebra E G := {
    norm_smul_le a b := by
      rw [Algebra.smul_def, norm_mul, hnj]
  }
  obtain ⟨p, hp1, hpna, hpF, hpG⟩ := ht E F G
  obtain ⟨q, hqna, hqp⟩ := hd (F ⊗[E] G) p hp1 hpna
  obtain ⟨L, _, _, _, r, hr⟩ := hr (F ⊗[E] G) q hqna
  let l : F →+* F ⊗[E] G := Algebra.TensorProduct.includeLeftRingHom
  let t : G →+* F ⊗[E] G := Algebra.TensorProduct.includeRight.toRingHom
  let f₀ : F →+* L := r.comp l
  let g₀ : G →+* L := r.comp t
  have hfle (a : F) : ‖f₀ a‖ ≤ ‖a‖ :=
    (hr (l a)).le.trans ((hqp (l a)).trans (hpF a))
  have hgle (b : G) : ‖g₀ b‖ ≤ ‖b‖ :=
    (hr (t b)).le.trans ((hqp (t b)).trans (hpG b))
  have hf (a : F) : ‖f₀ a‖ = ‖a‖ := norm_eq_of_contracting_ringHom f₀ hfle a
  have hg (b : G) : ‖g₀ b‖ = ‖b‖ := norm_eq_of_contracting_ringHom g₀ hgle b
  have hcomm (a : E) : f₀ (i a) = g₀ (j a) := by
    change r (l (algebraMap E F a)) = r (t (algebraMap E G a))
    exact congrArg r (RingHom.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := E) (A := F) (B := G)) a)
  let : Algebra K L := (f₀.comp (algebraMap K F)).toAlgebra
  let : NormedAlgebra K L := {
    norm_smul_le c a := by
      rw [Algebra.smul_def, norm_mul]
      change ‖f₀ (algebraMap K F c)‖ * ‖a‖ ≤ ‖c‖ * ‖a‖
      rw [hf, norm_algebraMap, norm_one, mul_one]
  }
  let f : BoundedAlgHom K F L := {
    toRingHom := f₀
    commutes' := fun _ => rfl
    bounded := ⟨1, zero_lt_one, fun a => by rw [one_mul]; exact hfle a⟩
  }
  let g : BoundedAlgHom K G L := {
    toRingHom := g₀
    commutes' := fun c => by
      change g₀ (algebraMap K G c) = f₀ (algebraMap K F c)
      rw [← j.toAlgHom.commutes c, ← i.toAlgHom.commutes c]
      exact (hcomm (algebraMap K E c)).symm
    bounded := ⟨1, zero_lt_one, fun b => by rw [one_mul]; exact hgle b⟩
  }
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, f, g, ?_, ?_, ?_⟩
  · exact BoundedAlgHom.ext hcomm
  · exact AddMonoidHomClass.isometry_of_norm f.toAlgHom hf
  · exact AddMonoidHomClass.isometry_of_norm g.toAlgHom hg

/-- Complete ultrametric fields admit commuting isometric embeddings over a common field. -/
theorem completeFieldAmalgamation : CompleteFieldAmalgamationStatement.{u} :=
  completeFieldAmalgamation_of_tensorSeminorm tensorSeminormStatement
    BanachSpectrum.nonarchimedeanDomination seminormRealization

end Langlands.Analytic
