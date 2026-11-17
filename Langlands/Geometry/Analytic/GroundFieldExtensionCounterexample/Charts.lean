import Langlands.Geometry.Analytic.GroundFieldExtensionCounterexample.Fields
import Langlands.Geometry.Analytic.PolynomialLocusTrivialNorm
import Langlands.Geometry.Analytic.Spectrum.Properties

/-! # The two finite affinoid algebras of the counterexample

Over the trivially normed field `F₂`, the source algebra is `F₄ × F₄` and the target
algebra is `F₄⁴`, each realized as the unit-radius chart of a finite polynomial
presentation.  The map `restrictMap` from the target to the source keeps the first
two factors, and `frobenius` is the `F₂`-linear Frobenius endomorphism of the
source.  Every point of either spectrum takes only the values `0` and `1`, so the
Frobenius endomorphism fixes every point of the source spectrum.
-/

noncomputable section

namespace Langlands.Analytic.GroundFieldExtensionCounterexample

open PresentedAffinoidAlgebra

theorem norm_eq_one_of_ne_zero : ∀ c : F₂, c ≠ 0 → ‖c‖ = 1 :=
  fun _ hc => norm_F₂_of_ne_zero hc

/-- The finite `F₂`-algebra `F₄ × F₄`. -/
abbrev SourceRing := Fin 2 → F₄

/-- The finite `F₂`-algebra `F₄⁴`. -/
abbrev TargetRing := Fin 4 → F₄

/-- A chosen finite polynomial presentation of the source ring. -/
def sourcePresentation : FinitePolynomialPresentation F₂ SourceRing :=
  FinitePolynomialPresentation.ofFiniteType F₂ SourceRing

/-- A chosen finite polynomial presentation of the target ring. -/
def targetPresentation : FinitePolynomialPresentation F₂ TargetRing :=
  FinitePolynomialPresentation.ofFiniteType F₂ TargetRing

/-- The source ring as a presented affinoid `F₂`-algebra. -/
abbrev sourceAlgebra : PresentedAffinoidAlgebra F₂ :=
  PolynomialLocus.chart sourcePresentation (PositivePolyradius.unit _)

/-- The target ring as a presented affinoid `F₂`-algebra. -/
abbrev targetAlgebra : PresentedAffinoidAlgebra F₂ :=
  PolynomialLocus.chart targetPresentation (PositivePolyradius.unit _)

/-- The algebra map from the source ring onto the source affinoid algebra. -/
def sourceInclusion : SourceRing →ₐ[F₂] sourceAlgebra :=
  PolynomialLocus.algebraMap sourcePresentation _

/-- The algebra map from the target ring onto the target affinoid algebra. -/
def targetInclusion : TargetRing →ₐ[F₂] targetAlgebra :=
  PolynomialLocus.algebraMap targetPresentation _

theorem sourceInclusion_surjective : Function.Surjective sourceInclusion :=
  PolynomialLocus.algebraMap_surjective sourcePresentation norm_eq_one_of_ne_zero

theorem targetInclusion_surjective : Function.Surjective targetInclusion :=
  PolynomialLocus.algebraMap_surjective targetPresentation norm_eq_one_of_ne_zero

theorem norm_source_le_one (s : sourceAlgebra) : ‖s‖ ≤ 1 :=
  PolynomialLocus.norm_le_one sourcePresentation norm_eq_one_of_ne_zero s

theorem norm_target_le_one (s : targetAlgebra) : ‖s‖ ≤ 1 :=
  PolynomialLocus.norm_le_one targetPresentation norm_eq_one_of_ne_zero s

/-- Keep the first two factors of `F₄⁴`. -/
def restrict : TargetRing →ₐ[F₂] SourceRing :=
  AlgHom.pi fun i : Fin 2 =>
    Pi.evalAlgHom F₂ (fun _ : Fin 4 => F₄) (Fin.castLE (by norm_num) i)

@[simp]
theorem restrict_apply (a : TargetRing) (i : Fin 2) :
    restrict a i = a (Fin.castLE (by norm_num) i) := rfl

/-- The bounded map from the target algebra to the source algebra keeping the first
two factors. -/
def restrictMap : BoundedAlgHom F₂ targetAlgebra sourceAlgebra :=
  PolynomialLocus.lift targetPresentation (sourceInclusion.comp restrict)
    (fun _ => norm_source_le_one _)

@[simp]
theorem restrictMap_targetInclusion (a : TargetRing) :
    restrictMap (targetInclusion a) = sourceInclusion (restrict a) :=
  PolynomialLocus.lift_algebraMap targetPresentation _ _ a

/-- The `F₂`-linear Frobenius endomorphism of the source algebra. -/
def frobenius : BoundedAlgHom F₂ sourceAlgebra sourceAlgebra :=
  PolynomialLocus.lift sourcePresentation
    (sourceInclusion.comp (FiniteField.frobeniusAlgHom F₂ SourceRing))
    (fun _ => norm_source_le_one _)

theorem frobenius_sourceInclusion (a : SourceRing) :
    frobenius (sourceInclusion a) = sourceInclusion (a ^ Fintype.card F₂) :=
  PolynomialLocus.lift_algebraMap sourcePresentation _ _ a

theorem frobenius_apply (s : sourceAlgebra) : frobenius s = s ^ Fintype.card F₂ := by
  obtain ⟨a, rfl⟩ := sourceInclusion_surjective s
  rw [frobenius_sourceInclusion, map_pow]

/-- Evaluation of the source algebra at one of its two factors. -/
def sourceEvaluation (k : Fin 2) : BoundedAlgHom F₂ sourceAlgebra F₄ :=
  PolynomialLocus.lift sourcePresentation (Pi.evalAlgHom F₂ (fun _ : Fin 2 => F₄) k)
    (fun _ => norm_F₄_le_one _)

/-- Evaluation of the target algebra at one of its four factors. -/
def targetEvaluation (k : Fin 4) : BoundedAlgHom F₂ targetAlgebra F₄ :=
  PolynomialLocus.lift targetPresentation (Pi.evalAlgHom F₂ (fun _ : Fin 4 => F₄) k)
    (fun _ => norm_F₄_le_one _)

/-- The point of the source spectrum given by one of the two factors. -/
def sourcePoint (k : Fin 2) : BanachSpectrum sourceAlgebra :=
  BanachSpectrum.comap (sourceEvaluation k).toBoundedRingHom (BanachSpectrum.fieldPoint F₄)

/-- The point of the target spectrum given by one of the four factors. -/
def targetPoint (k : Fin 4) : BanachSpectrum targetAlgebra :=
  BanachSpectrum.comap (targetEvaluation k).toBoundedRingHom (BanachSpectrum.fieldPoint F₄)

@[simp]
theorem sourceEvaluation_sourceInclusion (k : Fin 2) (a : SourceRing) :
    sourceEvaluation k (sourceInclusion a) = a k :=
  PolynomialLocus.lift_algebraMap sourcePresentation
    (Pi.evalAlgHom F₂ (fun _ : Fin 2 => F₄) k) (fun _ => norm_F₄_le_one _) a

@[simp]
theorem targetEvaluation_targetInclusion (k : Fin 4) (a : TargetRing) :
    targetEvaluation k (targetInclusion a) = a k :=
  PolynomialLocus.lift_algebraMap targetPresentation
    (Pi.evalAlgHom F₂ (fun _ : Fin 4 => F₄) k) (fun _ => norm_F₄_le_one _) a

@[simp]
theorem sourcePoint_sourceInclusion (k : Fin 2) (a : SourceRing) :
    sourcePoint k (sourceInclusion a) = ‖a k‖ := by
  change ‖sourceEvaluation k (sourceInclusion a)‖ = ‖a k‖
  rw [sourceEvaluation_sourceInclusion]

@[simp]
theorem targetPoint_targetInclusion (k : Fin 4) (a : TargetRing) :
    targetPoint k (targetInclusion a) = ‖a k‖ := by
  change ‖targetEvaluation k (targetInclusion a)‖ = ‖a k‖
  rw [targetEvaluation_targetInclusion]

/-- A point of any normed ring takes the value `0` or `1` at an element `s` with
`s ^ n = s` for some `n ≥ 2`. -/
theorem apply_eq_zero_or_one {B : Type*} [NormedCommRing B] (x : BanachSpectrum B)
    {s : B} {n : ℕ} (hn : 2 ≤ n) (hs : s ^ n = s) : x s = 0 ∨ x s = 1 := by
  have hpow : x s ^ n = x s := by
    rw [← map_pow, hs]
  rcases eq_or_ne (x s) 0 with h | h
  · exact Or.inl h
  · right
    have h1 : x s ^ (n - 1) = 1 := by
      apply mul_left_cancel₀ h
      rw [← pow_succ', Nat.sub_add_cancel (by omega), hpow, mul_one]
    exact (pow_eq_one_iff_of_nonneg (apply_nonneg x.toMulRingSeminorm s)
      (by omega)).mp h1

theorem two_le_card_F₄ : 2 ≤ Fintype.card F₄ := Fintype.one_lt_card

theorem source_pow_card (s : sourceAlgebra) : s ^ Fintype.card F₄ = s := by
  obtain ⟨a, rfl⟩ := sourceInclusion_surjective s
  rw [← map_pow]
  congr 1
  funext i
  exact FiniteField.pow_card (a i)

theorem target_pow_card (s : targetAlgebra) : s ^ Fintype.card F₄ = s := by
  obtain ⟨a, rfl⟩ := targetInclusion_surjective s
  rw [← map_pow]
  congr 1
  funext i
  exact FiniteField.pow_card (a i)

theorem source_apply_eq_zero_or_one (x : BanachSpectrum sourceAlgebra) (s : sourceAlgebra) :
    x s = 0 ∨ x s = 1 :=
  apply_eq_zero_or_one x two_le_card_F₄ (source_pow_card s)

theorem target_apply_eq_zero_or_one (x : BanachSpectrum targetAlgebra) (s : targetAlgebra) :
    x s = 0 ∨ x s = 1 :=
  apply_eq_zero_or_one x two_le_card_F₄ (target_pow_card s)

/-- The Frobenius endomorphism fixes every point of the source spectrum. -/
theorem comap_frobenius (x : BanachSpectrum sourceAlgebra) :
    BanachSpectrum.comap frobenius.toBoundedRingHom x = x := by
  apply BanachSpectrum.ext
  intro s
  change x (frobenius s) = x s
  rw [frobenius_apply]
  rw [map_pow]
  rcases source_apply_eq_zero_or_one x s with h | h
  · rw [h, zero_pow Fintype.card_ne_zero]
  · rw [h, one_pow]

end Langlands.Analytic.GroundFieldExtensionCounterexample
