import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalIntersectionUniversal.Statement

/-! # Bounded maps out of the positive-polyradius rational intersection quotient -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection

open GeneralizedTateAlgebra

section Radii

/-- The left factor of the product radii, read on the product index. -/
def leftFactorRadii {m : ℕ} (s : PositivePolyradius (Fin m)) (n : ℕ) :
    PositivePolyradius (Fin ((m + 1) * (n + 1))) where
  radius a := (Fin.cons 1 (fun i => s i) : Fin (m + 1) → ℝ) (finProdFinEquiv.symm a).1
  positive a := Fin.cases (by simp) (fun i => by simpa using s.positive i)
    (finProdFinEquiv.symm a).1

/-- The right factor of the product radii, read on the product index. -/
def rightFactorRadii (m : ℕ) {n : ℕ} (t : PositivePolyradius (Fin n)) :
    PositivePolyradius (Fin ((m + 1) * (n + 1))) where
  radius a := (Fin.cons 1 (fun j => t j) : Fin (n + 1) → ℝ) (finProdFinEquiv.symm a).2
  positive a := Fin.cases (by simp) (fun j => by simpa using t.positive j)
    (finProdFinEquiv.symm a).2

/-- Every product-radius weight splits as the two factor weights. -/
theorem weight_productRadii {m n : ℕ} (s : PositivePolyradius (Fin m))
    (t : PositivePolyradius (Fin n)) (d : Fin ((m + 1) * (n + 1)) →₀ ℕ) :
    (productRadii s t).weight d =
      (leftFactorRadii s n).weight d * (rightFactorRadii m t).weight d := by
  simp only [PositivePolyradius.weight, ← Finsupp.prod_mul]
  apply Finsupp.prod_congr
  intro a _
  exact mul_pow _ _ _

end Radii

section Monomials

variable {σ : Type*} {B : Type*} [NormedCommRing B]

/-- A monomial in a product tuple is the product of the two monomials. -/
theorem monomialValue_mul (x y : σ → B) (d : σ →₀ ℕ) :
    StrictTateAlgebra.monomialValue σ B (fun a => x a * y a) d =
      StrictTateAlgebra.monomialValue σ B x d * StrictTateAlgebra.monomialValue σ B y d := by
  simp only [StrictTateAlgebra.monomialValue, mul_pow, Finsupp.prod_mul]

/-- Algebra maps commute with monomial evaluation. -/
theorem map_monomialValue {K : Type*} {E : Type*} [NormedField K] [NormedCommRing E]
    [_root_.Algebra K B] [_root_.Algebra K E] (φ : B →ₐ[K] E) (x : σ → B) (d : σ →₀ ℕ) :
    φ (StrictTateAlgebra.monomialValue σ B x d) =
      StrictTateAlgebra.monomialValue σ E (fun a => φ (x a)) d := by
  simp only [StrictTateAlgebra.monomialValue, Finsupp.prod, map_prod, map_pow]

end Monomials

section Lift

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m n : ℕ}
  (s : PositivePolyradius (Fin m)) (t : PositivePolyradius (Fin n))
  (g h : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)
  (k : Fin n → GeneralizedTateAlgebra A.polyradius K)

/-- The original left fractions, extended by the unit in position zero. -/
def leftExtendedFraction : Fin (m + 1) → algebra K A s g f :=
  Fin.cons 1 (fraction K A s g f)

/-- The original right fractions, extended by the unit in position zero. -/
def rightExtendedFraction : Fin (n + 1) → algebra K A t h k :=
  Fin.cons 1 (fraction K A t h k)

theorem norm_leftExtendedFraction_le (i : Fin (m + 1)) :
    ‖leftExtendedFraction K A s g f i‖ ≤
      (Fin.cons 1 (fun i => s i) : Fin (m + 1) → ℝ) i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa only [leftExtendedFraction, Fin.cons_zero] using
      PresentedAffinoidAlgebra.norm_one_le K (algebra K A s g f)
  · simpa only [leftExtendedFraction, Fin.cons_succ] using norm_fraction_le K A s g f i

theorem norm_rightExtendedFraction_le (j : Fin (n + 1)) :
    ‖rightExtendedFraction K A t h k j‖ ≤
      (Fin.cons 1 (fun j => t j) : Fin (n + 1) → ℝ) j := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [rightExtendedFraction, Fin.cons_zero] using
      PresentedAffinoidAlgebra.norm_one_le K (algebra K A t h k)
  · simpa only [rightExtendedFraction, Fin.cons_succ] using norm_fraction_le K A t h k j

/-- The extended fraction equations, with the denominator equation in position zero. -/
theorem leftExtendedFraction_equation (i : Fin (m + 1)) :
    baseMap K A s g f (presentationMap K A g) * leftExtendedFraction K A s g f i =
      baseMap K A s g f (presentationMap K A
        ((Fin.cons g f : Fin (m + 1) → GeneralizedTateAlgebra A.polyradius K) i)) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [leftExtendedFraction, Fin.cons_zero, mul_one]
  · simpa only [leftExtendedFraction, Fin.cons_succ] using fraction_equation K A s g f i

theorem rightExtendedFraction_equation (j : Fin (n + 1)) :
    baseMap K A t h k (presentationMap K A h) * rightExtendedFraction K A t h k j =
      baseMap K A t h k (presentationMap K A
        ((Fin.cons h k : Fin (n + 1) → GeneralizedTateAlgebra A.polyradius K) j)) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [rightExtendedFraction, Fin.cons_zero, mul_one]
  · simpa only [rightExtendedFraction, Fin.cons_succ] using fraction_equation K A t h k j

variable (E : Type v) [NormedCommRing E] [NormedAlgebra K E]
  (α : BoundedAlgHom K (algebra K A s g f) E)
  (β : BoundedAlgHom K (algebra K A t h k) E)

/-- The prescribed images of the product coordinates. -/
def pairTuple : Fin ((m + 1) * (n + 1)) → E := fun a =>
  α (leftExtendedFraction K A s g f (finProdFinEquiv.symm a).1) *
    β (rightExtendedFraction K A t h k (finProdFinEquiv.symm a).2)

/-- The two bounded maps give the product-radius monomial bound, with
constant the product of their two bounds. -/
theorem pairTuple_bounded :
    HasBoundedMonomials (productRadii s t) E (pairTuple K A s t g h f k E α β) := by
  obtain ⟨Cα, hCα, hα⟩ := α.bounded
  obtain ⟨Cβ, hCβ, hβ⟩ := β.bounded
  refine ⟨Cα * Cβ, mul_pos hCα hCβ, fun d => ?_⟩
  have hx := monomialValue_norm_le_weight (leftFactorRadii s n) (algebra K A s g f)
    (PresentedAffinoidAlgebra.norm_one_le K (algebra K A s g f))
    (fun a => leftExtendedFraction K A s g f (finProdFinEquiv.symm a).1)
    (fun a => norm_leftExtendedFraction_le K A s g f _) d
  have hy := monomialValue_norm_le_weight (rightFactorRadii m t) (algebra K A t h k)
    (PresentedAffinoidAlgebra.norm_one_le K (algebra K A t h k))
    (fun a => rightExtendedFraction K A t h k (finProdFinEquiv.symm a).2)
    (fun a => norm_rightExtendedFraction_le K A t h k _) d
  have hm : StrictTateAlgebra.monomialValue _ E (pairTuple K A s t g h f k E α β) d =
      α (StrictTateAlgebra.monomialValue _ (algebra K A s g f)
          (fun a => leftExtendedFraction K A s g f (finProdFinEquiv.symm a).1) d) *
        β (StrictTateAlgebra.monomialValue _ (algebra K A t h k)
          (fun a => rightExtendedFraction K A t h k (finProdFinEquiv.symm a).2) d) := by
    rw [map_monomialValue α.toAlgHom, map_monomialValue β.toAlgHom]
    exact monomialValue_mul _ _ d
  rw [hm, weight_productRadii]
  calc
    _ ≤ ‖α (StrictTateAlgebra.monomialValue _ (algebra K A s g f)
          (fun a => leftExtendedFraction K A s g f (finProdFinEquiv.symm a).1) d)‖ *
        ‖β (StrictTateAlgebra.monomialValue _ (algebra K A t h k)
          (fun a => rightExtendedFraction K A t h k (finProdFinEquiv.symm a).2) d)‖ :=
      norm_mul_le _ _
    _ ≤ (Cα * (leftFactorRadii s n).weight d) * (Cβ * (rightFactorRadii m t).weight d) :=
      mul_le_mul ((hα _).trans (mul_le_mul_of_nonneg_left hx hCα.le))
        ((hβ _).trans (mul_le_mul_of_nonneg_left hy hCβ.le)) (norm_nonneg _)
        (mul_nonneg hCα.le ((leftFactorRadii s n).weight_pos d).le)
    _ = _ := by ring

variable {K A s t g h f k E α β}

/-- Agreement on the coefficient algebra gives the product fraction equations
over the common base map. -/
theorem pairTuple_equation
    (hcompat : α.comp (baseMap K A s g f) = β.comp (baseMap K A t h k))
    (a : Fin ((m + 1) * (n + 1))) :
    (α.comp (baseMap K A s g f)) (presentationMap K A (g * h)) *
        pairTuple K A s t g h f k E α β a =
      (α.comp (baseMap K A s g f)) (presentationMap K A (numerators K A g h f k a)) := by
  have hc (x : A) : α (baseMap K A s g f x) = β (baseMap K A t h k x) :=
    congrArg (fun χ => χ x) hcompat
  have hl := congrArg α (leftExtendedFraction_equation K A s g f (finProdFinEquiv.symm a).1)
  have hr := congrArg β (rightExtendedFraction_equation K A t h k (finProdFinEquiv.symm a).2)
  rw [map_mul α.toAlgHom] at hl
  rw [map_mul β.toAlgHom] at hr
  change α (baseMap K A s g f (presentationMap K A (g * h))) *
      (α (leftExtendedFraction K A s g f (finProdFinEquiv.symm a).1) *
        β (rightExtendedFraction K A t h k (finProdFinEquiv.symm a).2)) =
    α (baseMap K A s g f (presentationMap K A
      ((Fin.cons g f : Fin (m + 1) → GeneralizedTateAlgebra A.polyradius K)
          (finProdFinEquiv.symm a).1 *
        (Fin.cons h k : Fin (n + 1) → GeneralizedTateAlgebra A.polyradius K)
          (finProdFinEquiv.symm a).2)))
  simp only [map_mul]
  rw [hc (presentationMap K A h), hc (presentationMap K A ((Fin.cons h k : Fin (n + 1) →
      GeneralizedTateAlgebra A.polyradius K) (finProdFinEquiv.symm a).2)), ← hl, ← hr]
  ring

variable [IsUltrametricDist E] [CompleteSpace E]

/-- The bounded extension determined by two bounded maps agreeing on the base. -/
def pushoutLift (hcompat : α.comp (baseMap K A s g f) = β.comp (baseMap K A t h k)) :
    BoundedAlgHom K (Algebra K A s t g h f k) E :=
  liftFromBase K A (productRadii s t) (g * h) (numerators K A g h f k) E
    (α.comp (baseMap K A s g f)) (pairTuple K A s t g h f k E α β)
    (pairTuple_bounded K A s t g h f k E α β) (pairTuple_equation hcompat)

theorem pushoutLift_comp_base
    (hcompat : α.comp (baseMap K A s g f) = β.comp (baseMap K A t h k)) :
    (pushoutLift hcompat).comp (base K A s t g h f k) = α.comp (baseMap K A s g f) :=
  liftFromBase_comp_baseMap K A (productRadii s t) (g * h) (numerators K A g h f k) E
    (α.comp (baseMap K A s g f)) (pairTuple K A s t g h f k E α β)
    (pairTuple_bounded K A s t g h f k E α β) (pairTuple_equation hcompat)

variable [CompleteSpace K]
  (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k)

theorem pushoutLift_comp_leftMap
    (hcompat : α.comp (baseMap K A s g f) = β.comp (baseMap K A t h k)) :
    (pushoutLift hcompat).comp (leftMap K A s t g h f k hf hk) = α := by
  apply hom_ext_base K A s g f E hf
  apply BoundedAlgHom.ext
  intro a
  change pushoutLift hcompat (leftMap K A s t g h f k hf hk (baseMap K A s g f a)) =
    α (baseMap K A s g f a)
  rw [leftMap_base]
  exact congrArg (fun χ => χ a) (pushoutLift_comp_base hcompat)

theorem pushoutLift_comp_rightMap
    (hcompat : α.comp (baseMap K A s g f) = β.comp (baseMap K A t h k)) :
    (pushoutLift hcompat).comp (rightMap K A s t g h f k hf hk) = β := by
  apply hom_ext_base K A t h k E hk
  apply BoundedAlgHom.ext
  intro a
  change pushoutLift hcompat (rightMap K A s t g h f k hf hk (baseMap K A t h k a)) =
    β (baseMap K A t h k a)
  rw [rightMap_base]
  exact (congrArg (fun χ => χ a) (pushoutLift_comp_base hcompat)).trans
    (congrArg (fun χ => χ a) hcompat)

/-- The constructed extension is the only bounded map with both factorizations. -/
theorem existsUnique_pushoutLift
    (hcompat : α.comp (baseMap K A s g f) = β.comp (baseMap K A t h k)) :
    ∃! θ : BoundedAlgHom K (Algebra K A s t g h f k) E,
      θ.comp (leftMap K A s t g h f k hf hk) = α ∧
        θ.comp (rightMap K A s t g h f k hf hk) = β := by
  refine ⟨pushoutLift hcompat,
    ⟨pushoutLift_comp_leftMap hf hk hcompat, pushoutLift_comp_rightMap hf hk hcompat⟩, ?_⟩
  rintro θ ⟨hθ, -⟩
  apply hom_ext_base K A (productRadii s t) (g * h) (numerators K A g h f k) E
    (generatesUnitIdeal K A g h f k hf hk)
  apply BoundedAlgHom.ext
  intro a
  change θ (base K A s t g h f k a) = pushoutLift hcompat (base K A s t g h f k a)
  exact (congrArg θ (leftMap_base K A s t g h f k hf hk a)).symm.trans
    ((congrArg (fun χ => χ (baseMap K A s g f a)) hθ).trans
      (congrArg (fun χ => χ a) (pushoutLift_comp_base hcompat)).symm)

end Lift

/-- The constructed restriction maps of the positive-polyradius rational
intersection quotient have the bounded pushout property, with an independent
universe for the common target. -/
theorem boundedPushout : BoundedPushoutStatement.{u, v} := by
  intro K _ _ _ A m n s t g h f k hf hk
  refine ⟨leftMap_comp_baseMap K A s t g h f k hf hk,
    rightMap_comp_baseMap K A s t g h f k hf hk, ?_⟩
  intro E _ _ _ _ α β hcompat
  exact existsUnique_pushoutLift hf hk hcompat

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection
