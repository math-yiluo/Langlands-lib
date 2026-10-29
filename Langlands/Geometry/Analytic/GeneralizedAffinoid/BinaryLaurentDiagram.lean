import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalPresentation

/-! # The actual relative-series binary Laurent diagram -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) (f : A)

/-! ## The three quotients -/

/-- The upper quotient `A⟨X⟩ / closure(span{X - C(f)})`, as the denominator-one
relative rational quotient with numerator `f`. -/
abbrev Upper :=
  RelativeRationalPresentation.Algebra K A (PositivePolyradius.unit (Fin 1)) 1 (fun _ => f)

/-- The lower quotient `A⟨Y⟩ / closure(span{C(f) * Y - 1})`, as the relative rational
quotient with denominator `f` and numerator `1`. -/
abbrev Lower :=
  RelativeRationalPresentation.Algebra K A (PositivePolyradius.unit (Fin 1)) f (fun _ => 1)

/-- The two overlap equations `X - C(f)` and `C(f) * Y - 1` in `A⟨X,Y⟩`. -/
def overlapEquations : Set (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A) :=
  {X (PositivePolyradius.unit (Fin 2)) A 0 -
      constantAlgHom (PositivePolyradius.unit (Fin 2)) K A f,
    constantAlgHom (PositivePolyradius.unit (Fin 2)) K A f *
      X (PositivePolyradius.unit (Fin 2)) A 1 - 1}

/-- The overlap quotient `A⟨X,Y⟩ / closure(span{X - C(f), C(f) * Y - 1})`. -/
abbrev Overlap :=
  RelativeRelations.QuotientAlgebra K A (PositivePolyradius.unit (Fin 2))
    (overlapEquations K A f)

/-- The upper equations are exactly `{X - C(f)}`. -/
theorem upperEquations_eq :
    RelativeRationalPresentation.equations K A (PositivePolyradius.unit (Fin 1)) 1
        (fun _ => f) =
      {X (PositivePolyradius.unit (Fin 1)) A 0 -
        constantAlgHom (PositivePolyradius.unit (Fin 1)) K A f} := by
  ext h
  simp only [RelativeRationalPresentation.equations, Set.mem_range, Set.mem_singleton_iff,
    map_one, one_mul]
  constructor
  · rintro ⟨j, rfl⟩
    rw [Subsingleton.elim j 0]
  · rintro rfl
    exact ⟨0, rfl⟩

/-- The lower equations are exactly `{C(f) * Y - 1}`. -/
theorem lowerEquations_eq :
    RelativeRationalPresentation.equations K A (PositivePolyradius.unit (Fin 1)) f
        (fun _ => 1) =
      {constantAlgHom (PositivePolyradius.unit (Fin 1)) K A f *
        X (PositivePolyradius.unit (Fin 1)) A 0 - 1} := by
  ext h
  simp only [RelativeRationalPresentation.equations, Set.mem_range, Set.mem_singleton_iff,
    map_one]
  constructor
  · rintro ⟨j, rfl⟩
    rw [Subsingleton.elim j 0]
  · rintro rfl
    exact ⟨0, rfl⟩

/-! ## Coefficient maps and displayed coordinates -/

/-- The contractive coefficient map to the upper quotient. -/
def upperBase : BoundedAlgHom K A (Upper K A f) :=
  RelativeRationalPresentation.baseMap K A (PositivePolyradius.unit (Fin 1)) 1 (fun _ => f)

/-- The contractive coefficient map to the lower quotient. -/
def lowerBase : BoundedAlgHom K A (Lower K A f) :=
  RelativeRationalPresentation.baseMap K A (PositivePolyradius.unit (Fin 1)) f (fun _ => 1)

/-- The contractive coefficient map to the overlap quotient. -/
def overlapBase : BoundedAlgHom K A (Overlap K A f) :=
  RelativeRelations.baseMap K A (PositivePolyradius.unit (Fin 2)) (overlapEquations K A f)

/-- The image of the upper variable `X`. -/
def upperX : Upper K A f :=
  RelativeRationalPresentation.fraction K A (PositivePolyradius.unit (Fin 1)) 1
    (fun _ => f) 0

/-- The image of the lower variable `Y`. -/
def lowerY : Lower K A f :=
  RelativeRationalPresentation.fraction K A (PositivePolyradius.unit (Fin 1)) f
    (fun _ => 1) 0

/-- The image of the overlap variable `X`. -/
def overlapX : Overlap K A f :=
  RelativeRelations.newCoordinate K A (PositivePolyradius.unit (Fin 2))
    (overlapEquations K A f) 0

/-- The image of the overlap variable `Y`. -/
def overlapY : Overlap K A f :=
  RelativeRelations.newCoordinate K A (PositivePolyradius.unit (Fin 2))
    (overlapEquations K A f) 1

theorem upperBase_apply (a : A) :
    upperBase K A f a =
      RelativeRationalPresentation.quotientMap K A (PositivePolyradius.unit (Fin 1)) 1
        (fun _ => f) (constantAlgHom (PositivePolyradius.unit (Fin 1)) K A a) := rfl

theorem lowerBase_apply (a : A) :
    lowerBase K A f a =
      RelativeRationalPresentation.quotientMap K A (PositivePolyradius.unit (Fin 1)) f
        (fun _ => 1) (constantAlgHom (PositivePolyradius.unit (Fin 1)) K A a) := rfl

theorem overlapBase_apply (a : A) :
    overlapBase K A f a =
      RelativeRelations.quotientMap K A (PositivePolyradius.unit (Fin 2))
        (overlapEquations K A f) (constantAlgHom (PositivePolyradius.unit (Fin 2)) K A a) :=
  rfl

theorem upperX_def :
    upperX K A f =
      RelativeRationalPresentation.quotientMap K A (PositivePolyradius.unit (Fin 1)) 1
        (fun _ => f) (X (PositivePolyradius.unit (Fin 1)) A 0) := rfl

theorem lowerY_def :
    lowerY K A f =
      RelativeRationalPresentation.quotientMap K A (PositivePolyradius.unit (Fin 1)) f
        (fun _ => 1) (X (PositivePolyradius.unit (Fin 1)) A 0) := rfl

theorem overlapX_def :
    overlapX K A f =
      RelativeRelations.quotientMap K A (PositivePolyradius.unit (Fin 2))
        (overlapEquations K A f) (X (PositivePolyradius.unit (Fin 2)) A 0) := rfl

theorem overlapY_def :
    overlapY K A f =
      RelativeRelations.quotientMap K A (PositivePolyradius.unit (Fin 2))
        (overlapEquations K A f) (X (PositivePolyradius.unit (Fin 2)) A 1) := rfl

theorem norm_upperBase_le (a : A) : ‖upperBase K A f a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_baseMap_le K A _ _ _ a

theorem norm_lowerBase_le (a : A) : ‖lowerBase K A f a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_baseMap_le K A _ _ _ a

theorem norm_overlapBase_le (a : A) : ‖overlapBase K A f a‖ ≤ ‖a‖ :=
  RelativeRelations.norm_baseMap_le K A _ _ a

theorem norm_upperX_le : ‖upperX K A f‖ ≤ 1 :=
  RelativeRationalPresentation.norm_fraction_le K A _ _ _ 0

theorem norm_lowerY_le : ‖lowerY K A f‖ ≤ 1 :=
  RelativeRationalPresentation.norm_fraction_le K A _ _ _ 0

theorem norm_overlapX_le : ‖overlapX K A f‖ ≤ 1 :=
  RelativeRelations.norm_newCoordinate_le K A _ _ 0

theorem norm_overlapY_le : ‖overlapY K A f‖ ≤ 1 :=
  RelativeRelations.norm_newCoordinate_le K A _ _ 1

/-- The overlap unit has norm at most one; the zero quotient is allowed. -/
theorem norm_one_overlap_le : ‖(1 : Overlap K A f)‖ ≤ 1 := by
  have h := norm_overlapBase_le K A f 1
  rw [show overlapBase K A f 1 = 1 from (overlapBase K A f).toAlgHom.map_one] at h
  exact h.trans (PresentedAffinoidAlgebra.norm_one_le K A)

/-! ## The displayed generator equations -/

/-- In the upper quotient, `X = f`. -/
theorem upperX_eq : upperX K A f = upperBase K A f f :=
  RelativeRationalPresentation.weierstrass_fraction K A _ _ 0

/-- In the lower quotient, `f * Y = 1`. -/
theorem lowerBase_mul_lowerY : lowerBase K A f f * lowerY K A f = 1 := by
  have h := RelativeRationalPresentation.fraction_equation K A
    (PositivePolyradius.unit (Fin 1)) f (fun _ => 1) 0
  exact h.trans (lowerBase K A f).toAlgHom.map_one

/-- In the overlap quotient, `X = f`. -/
theorem overlapX_eq : overlapX K A f = overlapBase K A f f := by
  have h := RelativeRelations.quotientMap_equation K A (PositivePolyradius.unit (Fin 2))
    (overlapEquations K A f) (Set.mem_insert _ _)
  change (RelativeRelations.quotientMap K A (PositivePolyradius.unit (Fin 2))
    (overlapEquations K A f)).toAlgHom
      (X (PositivePolyradius.unit (Fin 2)) A 0 -
        constantAlgHom (PositivePolyradius.unit (Fin 2)) K A f) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h

/-- In the overlap quotient, `f * Y = 1`. -/
theorem overlapBase_mul_overlapY : overlapBase K A f f * overlapY K A f = 1 := by
  have h := RelativeRelations.quotientMap_equation K A (PositivePolyradius.unit (Fin 2))
    (overlapEquations K A f) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  change (RelativeRelations.quotientMap K A (PositivePolyradius.unit (Fin 2))
    (overlapEquations K A f)).toAlgHom
      (constantAlgHom (PositivePolyradius.unit (Fin 2)) K A f *
        X (PositivePolyradius.unit (Fin 2)) A 1 - 1) = 0 at h
  rw [map_sub, map_mul, map_one, sub_eq_zero] at h
  exact h

/-! ## Uniqueness of maps out of the quotients -/

section Uniqueness

variable {B : Type*} [NormedCommRing B] [NormedAlgebra K B]

/-- Bounded maps out of the upper quotient are determined by coefficients and `X`. -/
theorem upper_hom_ext (ψ χ : BoundedAlgHom K (Upper K A f) B)
    (hbase : ∀ a, ψ (upperBase K A f a) = χ (upperBase K A f a))
    (hX : ψ (upperX K A f) = χ (upperX K A f)) : ψ = χ :=
  RelativeRationalPresentation.hom_ext K A _ _ _ B ψ χ hbase fun j => by
    rw [Subsingleton.elim j 0]
    exact hX

/-- Bounded maps out of the lower quotient are determined by coefficients and `Y`. -/
theorem lower_hom_ext (ψ χ : BoundedAlgHom K (Lower K A f) B)
    (hbase : ∀ a, ψ (lowerBase K A f a) = χ (lowerBase K A f a))
    (hY : ψ (lowerY K A f) = χ (lowerY K A f)) : ψ = χ :=
  RelativeRationalPresentation.hom_ext K A _ _ _ B ψ χ hbase fun j => by
    rw [Subsingleton.elim j 0]
    exact hY

/-- Bounded maps out of the overlap quotient are determined by coefficients, `X` and `Y`. -/
theorem overlap_hom_ext (ψ χ : BoundedAlgHom K (Overlap K A f) B)
    (hbase : ∀ a, ψ (overlapBase K A f a) = χ (overlapBase K A f a))
    (hX : ψ (overlapX K A f) = χ (overlapX K A f))
    (hY : ψ (overlapY K A f) = χ (overlapY K A f)) : ψ = χ := by
  have h := relative_hom_ext (PositivePolyradius.unit (Fin 2))
    (ψ.comp (RelativeRelations.quotientMap K A _ (overlapEquations K A f)))
    (χ.comp (RelativeRelations.quotientMap K A _ (overlapEquations K A f))) hbase
    (fun i => by
      fin_cases i
      · exact hX
      · exact hY)
  apply RelativeRelations.hom_ext K A _ (overlapEquations K A f) B
  intro a
  exact congrArg (fun φ : BoundedAlgHom K _ B => φ a) h

end Uniqueness

/-! ## The left and right maps -/

/-- The relation `1 * X = f` used to define the left map. -/
theorem overlapBase_one_mul_overlapX (j : Fin 1) :
    overlapBase K A f 1 * (fun _ => overlapX K A f) j = overlapBase K A f f := by
  rw [show overlapBase K A f 1 = 1 from (overlapBase K A f).toAlgHom.map_one, one_mul]
  exact overlapX_eq K A f

/-- The relation `f * Y = 1` used to define the right map. -/
theorem overlapBase_mul_overlapY_fun (j : Fin 1) :
    overlapBase K A f f * (fun _ => overlapY K A f) j = overlapBase K A f 1 := by
  rw [show overlapBase K A f 1 = 1 from (overlapBase K A f).toAlgHom.map_one]
  exact overlapBase_mul_overlapY K A f

section Maps

variable [CompleteSpace K]

/-- The left map `Upper → Overlap`, sending coefficients to coefficients and `X` to `X`,
by contractive coefficient evaluation and closed-ideal descent. -/
def left : BoundedAlgHom K (Upper K A f) (Overlap K A f) :=
  RelativeRationalPresentation.evaluate K A (PositivePolyradius.unit (Fin 1)) 1 (fun _ => f)
    (Overlap K A f) (overlapBase K A f) (fun _ => overlapX K A f)
    (norm_overlapBase_le K A f)
    (monomialValue_norm_le_weight (PositivePolyradius.unit (Fin 1)) (Overlap K A f)
      (norm_one_overlap_le K A f) (fun _ => overlapX K A f)
      (fun _ => norm_overlapX_le K A f))
    (overlapBase_one_mul_overlapX K A f)

/-- The right map `Lower → Overlap`, sending coefficients to coefficients and `Y` to `Y`,
by contractive coefficient evaluation and closed-ideal descent. -/
def right : BoundedAlgHom K (Lower K A f) (Overlap K A f) :=
  RelativeRationalPresentation.evaluate K A (PositivePolyradius.unit (Fin 1)) f (fun _ => 1)
    (Overlap K A f) (overlapBase K A f) (fun _ => overlapY K A f)
    (norm_overlapBase_le K A f)
    (monomialValue_norm_le_weight (PositivePolyradius.unit (Fin 1)) (Overlap K A f)
      (norm_one_overlap_le K A f) (fun _ => overlapY K A f)
      (fun _ => norm_overlapY_le K A f))
    (overlapBase_mul_overlapY_fun K A f)

/-- On representatives, the left map is coefficient evaluation at `X`. -/
theorem left_quotientMap
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) :
    left K A f (RelativeRationalPresentation.quotientMap K A _ 1 (fun _ => f) h) =
      evaluateCoefficients (PositivePolyradius.unit (Fin 1)) (overlapBase K A f)
        (fun _ => overlapX K A f) h := rfl

/-- On representatives, the right map is coefficient evaluation at `Y`. -/
theorem right_quotientMap
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) :
    right K A f (RelativeRationalPresentation.quotientMap K A _ f (fun _ => 1) h) =
      evaluateCoefficients (PositivePolyradius.unit (Fin 1)) (overlapBase K A f)
        (fun _ => overlapY K A f) h := rfl

@[simp] theorem left_upperBase (a : A) : left K A f (upperBase K A f a) = overlapBase K A f a :=
  RelativeRationalPresentation.evaluate_baseMap K A _ _ _ _ _ _ _ _ _ a

@[simp] theorem left_upperX : left K A f (upperX K A f) = overlapX K A f :=
  RelativeRationalPresentation.evaluate_fraction K A _ _ _ _ _ _ _ _ _ 0

@[simp] theorem right_lowerBase (a : A) :
    right K A f (lowerBase K A f a) = overlapBase K A f a :=
  RelativeRationalPresentation.evaluate_baseMap K A _ _ _ _ _ _ _ _ _ a

@[simp] theorem right_lowerY : right K A f (lowerY K A f) = overlapY K A f :=
  RelativeRationalPresentation.evaluate_fraction K A _ _ _ _ _ _ _ _ _ 0

/-- The left map is compatible with the coefficient maps. -/
theorem left_comp_upperBase : (left K A f).comp (upperBase K A f) = overlapBase K A f :=
  BoundedAlgHom.ext (left_upperBase K A f)

/-- The right map is compatible with the coefficient maps. -/
theorem right_comp_lowerBase : (right K A f).comp (lowerBase K A f) = overlapBase K A f :=
  BoundedAlgHom.ext (right_lowerBase K A f)

theorem norm_left_le (a : Upper K A f) : ‖left K A f a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_evaluate_le K A _ _ _ _ _ _ _ _ _ a

theorem norm_right_le (a : Lower K A f) : ‖right K A f a‖ ≤ ‖a‖ :=
  RelativeRationalPresentation.norm_evaluate_le K A _ _ _ _ _ _ _ _ _ a

/-- The left map is the only bounded map with its coefficient and `X` values. -/
theorem eq_left (ψ : BoundedAlgHom K (Upper K A f) (Overlap K A f))
    (hbase : ∀ a, ψ (upperBase K A f a) = overlapBase K A f a)
    (hX : ψ (upperX K A f) = overlapX K A f) : ψ = left K A f :=
  upper_hom_ext K A f ψ (left K A f) (fun a => by rw [hbase, left_upperBase])
    (by rw [hX, left_upperX])

/-- The right map is the only bounded map with its coefficient and `Y` values. -/
theorem eq_right (ψ : BoundedAlgHom K (Lower K A f) (Overlap K A f))
    (hbase : ∀ a, ψ (lowerBase K A f a) = overlapBase K A f a)
    (hY : ψ (lowerY K A f) = overlapY K A f) : ψ = right K A f :=
  lower_hom_ext K A f ψ (right K A f) (fun a => by rw [hbase, right_lowerBase])
    (by rw [hY, right_lowerY])

end Maps

end Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent
