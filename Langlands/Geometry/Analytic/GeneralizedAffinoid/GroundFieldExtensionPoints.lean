import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionSurjectiveProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.PointAmalgamationReduction

/-! # Compatible points under affinoid ground field extension -/

noncomputable section

universe u v e f g

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open BanachSpectrum
open scoped TensorProduct

private theorem exists_commonField {E : Type e} {F : Type f} {G : Type g}
    [NormedField E] [NormedField F] [IsUltrametricDist F] [NormedField G]
    [IsUltrametricDist G] [NormedAlgebra E F] [NormedAlgebra E G] :
    ∃ (M : Type (max f g)) (_ : NormedField M) (_ : IsUltrametricDist M)
      (_ : CompleteSpace M) (p : F →+* M) (q : G →+* M),
      (∀ a : E, p (algebraMap E F a) = q (algebraMap E G a)) ∧ Isometry p ∧ Isometry q := by
  obtain ⟨s, hs1, hsna, hsF, hsG⟩ := exists_ultrametricTensorSeminorm (E := E) (F := F) (G := G)
  obtain ⟨t, htna, hts⟩ := nonarchimedeanDomination (F ⊗[E] G) s hs1 hsna
  obtain ⟨M, _, _, _, r, hr⟩ := seminormRealization (F ⊗[E] G) t htna
  let i : F →+* F ⊗[E] G := Algebra.TensorProduct.includeLeftRingHom
  let j : G →+* F ⊗[E] G := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨M, inferInstance, inferInstance, inferInstance, r.comp i, r.comp j, ?_, ?_, ?_⟩
  · intro a
    exact congrArg r (RingHom.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := E) (A := F) (B := G)) a)
  · apply AddMonoidHomClass.isometry_of_norm
    exact norm_map_eq_of_norm_map_le _ fun a => (hr (i a)).le.trans ((hts _).trans (hsF a))
  · apply AddMonoidHomClass.isometry_of_norm
    exact norm_map_eq_of_norm_map_le _ fun b => (hr (j b)).le.trans ((hts _).trans (hsG b))

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {A B : PresentedAffinoidAlgebra K} (φ : BoundedAlgHom K A B)

/-- The spectrum of `B_L` maps continuously to the compatible pairs in
`M(B) × M(A_L)`. -/
def spectrumComparison : C(BanachSpectrum (algebra K L B),
    {p : BanachSpectrum B × BanachSpectrum (algebra K L A) //
      comap φ.toBoundedRingHom p.1 = spectrumProjection K L A p.2}) where
  toFun z := ⟨⟨spectrumProjection K L B z, comap (map K L φ).toBoundedRingHom z⟩,
    (spectrumProjection_naturality K L φ z).symm⟩
  continuous_toFun := ((spectrumProjection K L B).continuous.prodMk
    (comapContinuous (map K L φ).toBoundedRingHom).continuous).subtype_mk _

/-- A point of `M(B)` and a point of `M(A_L)` with the same image in `M(A)`
lift to a point of `M(B_L)`. -/
theorem exists_spectrumPoint (y : BanachSpectrum B) (x : BanachSpectrum (algebra K L A))
    (h : comap φ.toBoundedRingHom y = spectrumProjection K L A x) :
    ∃ z : BanachSpectrum (algebra K L B), spectrumProjection K L B z = y ∧
      comap (map K L φ).toBoundedRingHom z = x := by
  let a := spectrumProjection K L A x
  let E := CompletedResidueField K a
  let F := CompletedResidueField K y
  let G := CompletedResidueField L x
  let χA := completedResidueMap K a
  let χB := completedResidueMap K y
  let χX := completedResidueMap L x
  let ev : A →+* G := χX.toAlgHom.toRingHom.comp (iota K L A).toAlgHom.toRingHom
  have hEv (b : A) : ‖ev b‖ = a b := norm_completedResidueMap L x (iota K L A b)
  let i := completedResidueComapOfEq K φ a y h
  let j := completedResidueLiftRingHom K a ev hEv
  let : NormedAlgebra E F := {
    __ := i.toAlgHom.toRingHom.toAlgebra
    norm_smul_le b c := by
      change ‖i b * c‖ ≤ ‖b‖ * ‖c‖
      rw [norm_mul, (isometry_completedResidueComapOfEq K φ a y h).norm_map_of_map_zero
        (map_zero i.toAlgHom)] }
  let : NormedAlgebra E G := {
    __ := j.toAlgebra
    norm_smul_le b c := by
      change ‖j b * c‖ ≤ ‖b‖ * ‖c‖
      rw [norm_mul, (isometry_completedResidueLiftRingHom K a ev hEv).norm_map_of_map_zero
        (map_zero j)] }
  obtain ⟨M, _, _, _, p, q, hpq, hp, hq⟩ := exists_commonField (E := E) (F := F) (G := G)
  have agree (b : A) : p (χB (φ b)) = q (χX (iota K L A b)) := by
    have hb := hpq (χA b)
    change p (i (χA b)) = q (j (χA b)) at hb
    rw [show i (χA b) = χB (φ b) from completedResidueComapOfEq_map K φ a y h b,
      show j (χA b) = χX (iota K L A b) from completedResidueLiftRingHom_map K a ev hEv b] at hb
    exact hb
  let scalar : L →+* M := q.comp (algebraMap L G)
  have hscalar (c : L) : ‖scalar c‖ = ‖c‖ := by
    change ‖q (algebraMap L G c)‖ = ‖c‖
    rw [hq.norm_map_of_map_zero (map_zero q), norm_algebraMap']
  let : NormedAlgebra L M := {
    __ := scalar.toAlgebra
    norm_smul_le c b := by
      change ‖scalar c * b‖ ≤ ‖c‖ * ‖b‖
      rw [norm_mul, hscalar] }
  let : NormedAlgebra K M := {
    __ := (scalar.comp (algebraMap K L)).toAlgebra
    norm_smul_le c b := by
      change ‖scalar (algebraMap K L c) * b‖ ≤ ‖c‖ * ‖b‖
      rw [norm_mul, hscalar, norm_algebraMap'] }
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ψ₀ : BoundedAlgHom K B M := {
    toRingHom := p.comp χB.toAlgHom.toRingHom
    commutes' c := by
      have hc := agree (algebraMap K A c)
      rw [φ.toAlgHom.commutes, χB.toAlgHom.commutes, (iota K L A).toAlgHom.commutes] at hc
      rw [IsScalarTower.algebraMap_apply K L (algebra K L A), χX.toAlgHom.commutes] at hc
      exact hc
    bounded := ⟨1, zero_lt_one, fun b => by
      change ‖p (χB b)‖ ≤ 1 * ‖b‖
      rw [hp.norm_map_of_map_zero (map_zero p), one_mul]
      exact (norm_completedResidueMap K y b).le.trans (y.le_norm b)⟩ }
  let ξ : BoundedAlgHom L (algebra K L A) M := {
    toRingHom := q.comp χX.toAlgHom.toRingHom
    commutes' c := by
      change q (χX (algebraMap L (algebra K L A) c)) = q (algebraMap L G c)
      rw [χX.toAlgHom.commutes]
    bounded := ⟨1, zero_lt_one, fun b => by
      change ‖q (χX b)‖ ≤ 1 * ‖b‖
      rw [hq.norm_map_of_map_zero (map_zero q), one_mul]
      exact (norm_completedResidueMap L x b).le.trans (x.le_norm b)⟩ }
  let ψ := lift K L B M ψ₀
  have hψ : ψ.comp (map K L φ) = ξ := by
    apply hom_ext K L A
    apply BoundedAlgHom.ext
    intro b
    simp only [BoundedAlgHom.comp_apply, overBase_apply, map_iota, ψ, lift_iota]
    exact agree b
  refine ⟨comap ψ.toBoundedRingHom (fieldPoint M), ?_, ?_⟩
  · apply BanachSpectrum.ext
    intro b
    change ‖ψ (iota K L B b)‖ = y b
    rw [lift_iota]
    change ‖p (χB b)‖ = y b
    rw [hp.norm_map_of_map_zero (map_zero p)]
    exact norm_completedResidueMap K y b
  · apply BanachSpectrum.ext
    intro b
    change ‖(ψ.comp (map K L φ)) b‖ = x b
    rw [hψ]
    change ‖q (χX b)‖ = x b
    rw [hq.norm_map_of_map_zero (map_zero q)]
    exact norm_completedResidueMap L x b

/-- The spectrum comparison is surjective. -/
theorem spectrumComparison_surjective : Function.Surjective (spectrumComparison K L φ) := by
  rintro ⟨⟨y, x⟩, h⟩
  obtain ⟨z, hz, hz'⟩ := exists_spectrumPoint K L φ y x h
  exact ⟨z, Subtype.ext (Prod.ext hz hz')⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
