import Langlands.Shimura.Unitary.DeligneNonSplitStatement
import Langlands.Shimura.Unitary.DeligneSplitTorus
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Proof that the real Deligne torus is a non-split torus -/

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.DeligneTorus

/-- The complex point of the real base is faithfully flat and quasi-compact. -/
theorem complexBaseMap_fpqc :
    Surjective complexBaseMap ∧ Flat complexBaseMap ∧ QuasiCompact complexBaseMap := by
  have h : Flat complexBaseMap ∧ Surjective complexBaseMap := by
    apply (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap ℝ ℂ))).2
    change (algebraMap ℝ ℂ).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  exact ⟨h.2, h.1, inferInstance⟩

/-- The complex pullback of the real Deligne group scheme is smooth. -/
theorem smooth_complexGroupScheme : Smooth complexGroupScheme.X.hom :=
  isSplitTorus_complexGroupScheme.smooth

/-- Smoothness descends from the complex pullback to the real Deligne group scheme. -/
theorem smooth_groupScheme : Smooth groupScheme.X.hom := by
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := groupScheme.X.hom) (g := complexBaseMap)
  · exact ⟨⟨complexBaseMap_fpqc.1, complexBaseMap_fpqc.2.1⟩, complexBaseMap_fpqc.2.2⟩
  · exact smooth_complexGroupScheme

/-- In `ℝˣ`, an element whose fourth power is one already has square one. -/
theorem real_units_sq_eq_one_of_pow_four {x : ℝˣ} (h : x ^ 4 = 1) : x ^ 2 = 1 := by
  apply Units.ext
  have h4 : (x : ℝ) ^ 4 = 1 := by simpa using congrArg Units.val h
  have h' : ((x : ℝ) ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact h4
  push_cast
  exact (pow_eq_one_iff_of_nonneg (sq_nonneg _) two_ne_zero).1 h'

/-- The unit `i` of `ℂ` has order four, not two. -/
theorem complex_I_unit_pow : (Units.mk0 Complex.I Complex.I_ne_zero) ^ 4 = 1 ∧
    (Units.mk0 Complex.I Complex.I_ne_zero) ^ 2 ≠ 1 := by
  constructor
  · apply Units.ext
    simp [Complex.I_pow_four]
  · intro h
    have h' := congrArg Units.val h
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Complex.I_sq, Units.val_one] at h'
    have := congrArg Complex.re h'
    norm_num at this

/-- The real Deligne group scheme is not a split torus over `Spec ℝ`: its real points contain
`i`, an element of order four, while the real points `(ℝˣ)^I` of a split torus have no such
element. -/
theorem not_isSplitTorus_groupScheme : ¬ GroupScheme.IsSplitTorus groupScheme := by
  rintro ⟨I, hI, ⟨e⟩⟩
  let Φ : ℂˣ ≃* (I → ℝˣ) :=
    realPointsEquiv.symm.trans ((affinePointsEquiv (CommAlgCat.of ℝ ℝ)).symm.trans
      ((GroupScheme.isoPointsEquiv e _).trans
        (GroupScheme.splitTorus.affinePointsEquiv I
          (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℝ))))))
  obtain ⟨hw4, hw2⟩ := complex_I_unit_pow
  apply hw2
  apply Φ.injective
  rw [map_pow, map_one]
  funext i
  apply real_units_sq_eq_one_of_pow_four
  have := congrFun (congrArg Φ hw4) i
  rwa [map_pow, map_one] at this

/-- The real Deligne torus is smooth, split over `ℂ`, and not split over `ℝ`. -/
theorem nonSplitTorusStatement : NonSplitTorusStatement :=
  ⟨smooth_groupScheme, isSplitTorus_complexGroupScheme, not_isSplitTorus_groupScheme⟩

end Langlands.Shimura.DeligneTorus
