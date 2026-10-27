import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRelationsSpectrum
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RelativeEvaluation

/-! # Intrinsic weighted rational quotients over actual coefficient elements -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRationalPresentation

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (g : A) (f : Fin m → A)

/-- The relative rational equations, using actual elements of the coefficient algebra. -/
def equations : Set (GeneralizedTateAlgebra s A) :=
  Set.range fun j => constantAlgHom s K A g * X s A j - constantAlgHom s K A (f j)

/-- The denominator and numerators generate the unit ideal in the actual coefficient ring. -/
def GeneratesUnitIdeal : Prop := Ideal.span (insert g (Set.range f)) = ⊤

/-- The actual relative series quotient by the closed ideal of rational equations. -/
abbrev Algebra := RelativeRelations.QuotientAlgebra K A s (equations K A s g f)

/-- The contractive projection to the actual relative rational quotient. -/
def quotientMap : BoundedAlgHom K (GeneralizedTateAlgebra s A) (Algebra K A s g f) :=
  RelativeRelations.quotientMap K A s (equations K A s g f)

theorem quotientMap_surjective : Function.Surjective (quotientMap K A s g f) :=
  RelativeRelations.quotientMap_surjective K A s (equations K A s g f)

theorem quotientMap_eq_zero_iff (h : GeneralizedTateAlgebra s A) :
    quotientMap K A s g f h = 0 ↔
      h ∈ (Ideal.span (equations K A s g f)).closure :=
  RelativeRelations.quotientMap_eq_zero_iff K A s (equations K A s g f) h

theorem norm_quotientMap_le (h : GeneralizedTateAlgebra s A) :
    ‖quotientMap K A s g f h‖ ≤ ‖h‖ :=
  RelativeRelations.norm_quotientMap_le K A s (equations K A s g f) h

theorem exists_representative_norm_lt (a : Algebra K A s g f) {ε : ℝ} (hε : 0 < ε) :
    ∃ h, quotientMap K A s g f h = a ∧ ‖h‖ < ‖a‖ + ε :=
  RelativeRelations.exists_representative_norm_lt K A s (equations K A s g f) a hε

/-- The bounded coefficient map to the quotient. -/
def baseMap : BoundedAlgHom K A (Algebra K A s g f) :=
  RelativeRelations.baseMap K A s (equations K A s g f)

@[simp] theorem baseMap_apply (a : A) :
    baseMap K A s g f a = quotientMap K A s g f (constantAlgHom s K A a) := rfl

theorem baseMap_eq_algebraMap (a : A) :
    baseMap K A s g f a = algebraMap A (Algebra K A s g f) a := rfl

theorem norm_baseMap_le (a : A) : ‖baseMap K A s g f a‖ ≤ ‖a‖ :=
  RelativeRelations.norm_baseMap_le K A s (equations K A s g f) a

/-- The relative coordinate satisfying the denominator equation. -/
def fraction (j : Fin m) : Algebra K A s g f :=
  quotientMap K A s g f (X s A j)

theorem norm_fraction_le (j : Fin m) : ‖fraction K A s g f j‖ ≤ s j :=
  RelativeRelations.norm_newCoordinate_le K A s (equations K A s g f) j

theorem fraction_equation (j : Fin m) :
    baseMap K A s g f g * fraction K A s g f j = baseMap K A s g f (f j) := by
  have h := RelativeRelations.quotientMap_equation K A s (equations K A s g f)
    (Set.mem_range_self j)
  change (quotientMap K A s g f).toAlgHom
    (constantAlgHom s K A g * X s A j - constantAlgHom s K A (f j)) = 0 at h
  rw [map_sub, map_mul, sub_eq_zero] at h
  exact h

section Uniqueness

variable (B : Type v) [NormedCommRing B] [NormedAlgebra K B]

/-- All bounded maps from the relative rational quotient are determined by their
coefficient and fraction values. No completeness is needed for uniqueness. -/
theorem hom_ext (ψ χ : BoundedAlgHom K (Algebra K A s g f) B)
    (hbase : ∀ a, ψ (baseMap K A s g f a) = χ (baseMap K A s g f a))
    (hfrac : ∀ j, ψ (fraction K A s g f j) = χ (fraction K A s g f j)) : ψ = χ := by
  have h := relative_hom_ext s (ψ.comp (quotientMap K A s g f))
    (χ.comp (quotientMap K A s g f)) hbase hfrac
  apply RelativeRelations.hom_ext K A s (equations K A s g f) B
  intro a
  exact congrArg (fun φ : BoundedAlgHom K (GeneralizedTateAlgebra s A) B => φ a) h

end Uniqueness

section Evaluation

variable (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B]
  (φ : BoundedAlgHom K A B) (b : Fin m → B)
  (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
  (hb : ∀ d : Fin m →₀ ℕ,
    ‖StrictTateAlgebra.monomialValue (Fin m) B b d‖ ≤ s.weight d)
  (hrel : ∀ j, φ g * b j = φ (f j))

include hrel in
/-- Coefficient evaluation annihilates the actual relative rational equations. -/
theorem evaluateCoefficientsHom_equations :
    ∀ h ∈ equations K A s g f, evaluateCoefficientsHom s φ b hφ hb h = 0 := by
  rintro h ⟨j, rfl⟩
  change (evaluateCoefficientsHom s φ b hφ hb).toAlgHom
    (constantAlgHom s K A g * X s A j - constantAlgHom s K A (f j)) = 0
  rw [map_sub, map_mul]
  change evaluateCoefficients s φ b (constantAlgHom s K A g) *
    evaluateCoefficients s φ b (X s A j) -
      evaluateCoefficients s φ b (constantAlgHom s K A (f j)) = 0
  rw [evaluateCoefficients_constant, evaluateCoefficients_X,
    evaluateCoefficients_constant, sub_eq_zero]
  exact hrel j

/-- Actual bounded evaluation of the quotient from a contractive coefficient
map and weighted-bounded coordinates satisfying the rational equations. -/
def evaluate : BoundedAlgHom K (Algebra K A s g f) B :=
  RelativeRelations.descend K A s (equations K A s g f) B
    (evaluateCoefficientsHom s φ b hφ hb)
    (evaluateCoefficientsHom_equations K A s g f B φ b hφ hb hrel)

@[simp] theorem evaluate_quotientMap (h : GeneralizedTateAlgebra s A) :
    evaluate K A s g f B φ b hφ hb hrel (quotientMap K A s g f h) =
      evaluateCoefficients s φ b h := rfl

@[simp] theorem evaluate_baseMap (a : A) :
    evaluate K A s g f B φ b hφ hb hrel (baseMap K A s g f a) = φ a := by
  rw [baseMap_apply, evaluate_quotientMap, evaluateCoefficients_constant]

@[simp] theorem evaluate_fraction (j : Fin m) :
    evaluate K A s g f B φ b hφ hb hrel (fraction K A s g f j) = b j := by
  rw [fraction, evaluate_quotientMap, evaluateCoefficients_X]

theorem norm_evaluate_le (a : Algebra K A s g f) :
    ‖evaluate K A s g f B φ b hφ hb hrel a‖ ≤ ‖a‖ := by
  have h := RelativeRelations.norm_descend_le K A s (equations K A s g f) B
    (evaluateCoefficientsHom s φ b hφ hb)
    (evaluateCoefficientsHom_equations K A s g f B φ b hφ hb hrel)
    1 zero_lt_one
    (fun h => by
      change ‖evaluateCoefficients s φ b h‖ ≤ 1 * ‖h‖
      simpa only [one_mul] using norm_evaluateCoefficients_le s φ b hφ hb h) a
  simpa only [evaluate, one_mul] using h

/-- Uniqueness holds among all bounded maps with these coefficient and coordinate values. -/
theorem eq_evaluate (ψ : BoundedAlgHom K (Algebra K A s g f) B)
    (hbase : ∀ a, ψ (baseMap K A s g f a) = φ a)
    (hfrac : ∀ j, ψ (fraction K A s g f j) = b j) :
    ψ = evaluate K A s g f B φ b hφ hb hrel := by
  apply hom_ext K A s g f B
  · intro a
    rw [evaluate_baseMap, hbase]
  · intro j
    rw [evaluate_fraction, hfrac]

include hφ hb hrel in
theorem existsUnique_evaluate :
    ∃! ψ : BoundedAlgHom K (Algebra K A s g f) B,
      (∀ a, ψ (baseMap K A s g f a) = φ a) ∧
      (∀ j, ψ (fraction K A s g f j) = b j) := by
  refine ⟨evaluate K A s g f B φ b hφ hb hrel,
    ⟨evaluate_baseMap K A s g f B φ b hφ hb hrel,
      evaluate_fraction K A s g f B φ b hφ hb hrel⟩, ?_⟩
  intro ψ hψ
  exact eq_evaluate K A s g f B φ b hφ hb hrel ψ hψ.1 hψ.2

end Evaluation

/-- The weighted rational inequalities on the original coefficient spectrum. -/
def locus : Set (BanachSpectrum A) := {x | ∀ j, x (f j) ≤ s j * x g}

theorem isClosed_locus : IsClosed (locus K A s g f) := by
  simp only [locus, Set.ofPred_forall]
  exact isClosed_iInter fun j => isClosed_le (BanachSpectrum.evaluation (f j)).continuous
    (continuous_const.mul (BanachSpectrum.evaluation g).continuous)

theorem isCompact_locus : IsCompact (locus K A s g f) :=
  (isClosed_locus K A s g f).isCompact

/-- The continuous coefficient-spectrum pullback of the actual structural map. -/
def spectrumMap : C(BanachSpectrum (Algebra K A s g f), BanachSpectrum A) :=
  BanachSpectrum.comapContinuous (baseMap K A s g f).toBoundedRingHom

@[simp] theorem spectrumMap_apply (x : BanachSpectrum (Algebra K A s g f)) (a : A) :
    spectrumMap K A s g f x a = x (baseMap K A s g f a) := rfl

theorem spectrumMap_mem_locus (x : BanachSpectrum (Algebra K A s g f)) :
    spectrumMap K A s g f x ∈ locus K A s g f := by
  intro j
  change x (baseMap K A s g f (f j)) ≤ s j * x (baseMap K A s g f g)
  rw [← fraction_equation, map_mul, mul_comm (s j)]
  exact mul_le_mul_of_nonneg_left
    ((x.le_norm _).trans (norm_fraction_le K A s g f j))
    (apply_nonneg x.toMulRingSeminorm _)

/-- The forward structural map with its proved codomain restriction. -/
def spectrumToLocus : C(BanachSpectrum (Algebra K A s g f), locus K A s g f) where
  toFun x := ⟨spectrumMap K A s g f x, spectrumMap_mem_locus K A s g f x⟩
  continuous_toFun := (spectrumMap K A s g f).continuous.subtype_mk _

/-- The denominator-one quotient is the intrinsic weighted Weierstrass model. -/
abbrev WeierstrassAlgebra := Algebra K A s 1 f

theorem weierstrass_fraction (j : Fin m) :
    fraction K A s 1 f j = baseMap K A s 1 f (f j) := by
  simpa only [map_one, one_mul] using fraction_equation K A s 1 f j

/-- The denominator-one inequalities on the actual coefficient spectrum. -/
def weierstrassLocus : Set (BanachSpectrum A) := {x | ∀ j, x (f j) ≤ s j}

theorem locus_one : locus K A s 1 f = weierstrassLocus K A s f := by
  ext x
  simp only [locus, weierstrassLocus, Set.mem_ofPred_eq, map_one, mul_one]

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRationalPresentation
