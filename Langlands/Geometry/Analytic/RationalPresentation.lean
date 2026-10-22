import Langlands.Geometry.Analytic.RationalPresentation.Statement
import Langlands.Geometry.Analytic.TatePresentation

/-! # Actual rational quotient presentations -/

noncomputable section

universe u v

namespace Langlands.Analytic.RationalPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra
open WeierstrassPresentation (adjoinVariables adjoinVariables_X)

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
  (g : StrictTateAlgebra (Fin n) K) (f : Fin m → StrictTateAlgebra (Fin n) K)

/-- Invertibility of the denominator follows from the unit-ideal condition
and the equations; it is not imposed as a field of the construction. -/
theorem isUnit_baseMap_denominator (hunit : GeneratesUnitIdeal K n m S g f) :
    IsUnit (baseMap K n m S g f (presentationMap K (ofRelations K n S) g)) := by
  let J : Ideal (algebra K n m S g f) :=
    Ideal.span {baseMap K n m S g f (presentationMap K (ofRelations K n S) g)}
  have hle : Ideal.span (insert (presentationMap K (ofRelations K n S) g)
      (Set.range fun j => presentationMap K (ofRelations K n S) (f j))) ≤
      Ideal.comap (baseMap K n m S g f).toAlgHom.toRingHom J := by
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ⟨j, rfl⟩
    · exact Ideal.mem_span_singleton_self _
    · change baseMap K n m S g f
        (presentationMap K (ofRelations K n S) (f j)) ∈ J
      apply Ideal.mem_span_singleton.mpr
      exact ⟨coordinate K (algebra K n m S g f) (Fin.natAdd n j),
        (coordinate_equation K n m S g f j).symm⟩
  have h1 : (1 : algebra K n m S g f) ∈ J := by
    have h := hle (show (1 : ofRelations K n S) ∈
      Ideal.span (insert (presentationMap K (ofRelations K n S) g)
        (Set.range fun j => presentationMap K (ofRelations K n S) (f j))) by
          rw [hunit]
          trivial)
    simpa only [Ideal.mem_comap, map_one] using h
  exact Ideal.span_singleton_eq_top.mp (J.eq_top_iff_one.mpr h1)

omit [CompleteSpace K] in
/-- The denominator is nonzero at every point of the norm locus.
The unit-ideal condition rules out a common zero of all the generators. -/
theorem denominator_ne_zero (hunit : GeneratesUnitIdeal K n m S g f)
    (x : BanachSpectrum (ofRelations K n S)) (hx : x ∈ locus K n m S g f) :
    x (presentationMap K (ofRelations K n S) g) ≠ 0 := by
  intro hg
  have hle : Ideal.span (insert (presentationMap K (ofRelations K n S) g)
      (Set.range fun j => presentationMap K (ofRelations K n S) (f j))) ≤ x.kernel := by
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ⟨j, rfl⟩
    · exact hg
    · exact le_antisymm ((hx j).trans_eq hg) (apply_nonneg x.toMulRingSeminorm _)
  have h1 : x (1 : ofRelations K n S) = 0 :=
    hle (show (1 : ofRelations K n S) ∈
      Ideal.span (insert (presentationMap K (ofRelations K n S) g)
        (Set.range fun j => presentationMap K (ofRelations K n S) (f j))) by
          rw [hunit]
          trivial)
  exact one_ne_zero ((map_one x.toMulRingSeminorm).symm.trans h1)

/-- Every quotient point maps into the rational norm locus. -/
theorem comap_mem_locus (x : BanachSpectrum (algebra K n m S g f)) :
    BanachSpectrum.comap (baseMap K n m S g f).toBoundedRingHom x ∈
      locus K n m S g f := by
  intro j
  change x (baseMap K n m S g f (presentationMap K (ofRelations K n S) (f j))) ≤
    x (baseMap K n m S g f (presentationMap K (ofRelations K n S) g))
  rw [← coordinate_equation, map_mul]
  have hy : x (coordinate K (algebra K n m S g f) (Fin.natAdd n j)) ≤ 1 := by
    calc
      _ ≤ ‖coordinate K (algebra K n m S g f) (Fin.natAdd n j)‖ := x.le_norm _
      _ ≤ ‖X (Fin (n + m)) K (Fin.natAdd n j)‖ := Ideal.Quotient.norm_mk_le _ _
      _ = 1 := norm_X _ _ _
  exact mul_le_of_le_one_right (apply_nonneg x.toMulRingSeminorm _) hy

variable (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B]

/-- A tuple of the old coordinate images and proposed bounded fractions. -/
def solutionTuple (φ : BoundedAlgHom K (ofRelations K n S) B) (b : Fin m → B) :
    Fin (n + m) → B :=
  Fin.append (fun i => φ (coordinate K (ofRelations K n S) i)) b

omit [CompleteSpace K] [IsUltrametricDist B] [CompleteSpace B] in
theorem solutionTuple_bounded (φ : BoundedAlgHom K (ofRelations K n S) B)
    (b : Fin m → B) (hb : HasBoundedMonomials (Fin m) B b) :
    HasBoundedMonomials (Fin (n + m)) B (solutionTuple K n m S B φ b) := by
  apply (hasBoundedMonomials_iff_pow_bound _ _ _).mpr
  intro i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have h := hasBoundedMonomials_map_X (Fin n) K B
      (φ.comp (presentationMap K (ofRelations K n S)))
    have hi := h.pow_bound (Fin n) B i
    change ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ, ‖φ (coordinate K (ofRelations K n S) i) ^ r‖ ≤ C at hi
    simpa only [solutionTuple, Fin.append_left] using hi
  · simpa only [solutionTuple, Fin.append_right] using hb.pow_bound (Fin m) B j

theorem evaluate_included (φ : BoundedAlgHom K (ofRelations K n S) B)
    (b : Fin m → B)
    (hb : HasBoundedMonomials (Fin (n + m)) B (solutionTuple K n m S B φ b))
    (h : StrictTateAlgebra (Fin n) K) :
    evaluate (Fin (n + m)) K B (solutionTuple K n m S B φ b)
      (adjoinVariables K n m h) = φ (presentationMap K (ofRelations K n S) h) := by
  have hmaps :
      (evaluateHom (Fin (n + m)) K B (solutionTuple K n m S B φ b) hb).comp
        (adjoinVariables K n m) = φ.comp (presentationMap K (ofRelations K n S)) := by
    apply StrictTateAlgebra.hom_ext
    intro i
    change evaluate (Fin (n + m)) K B (solutionTuple K n m S B φ b)
      (adjoinVariables K n m (X (Fin n) K i)) = _
    rw [adjoinVariables_X, evaluate_X]
    exact Fin.append_left _ _ i
  exact congrArg (fun χ => χ h) hmaps

theorem solutionTuple_relations (φ : BoundedAlgHom K (ofRelations K n S) B)
    (b : Fin m → B)
    (hb : HasBoundedMonomials (Fin (n + m)) B (solutionTuple K n m S B φ b))
    (heq : ∀ j, φ (presentationMap K (ofRelations K n S) g) * b j =
      φ (presentationMap K (ofRelations K n S) (f j))) :
    ∀ h ∈ relations K n m S g f,
      evaluate (Fin (n + m)) K B (solutionTuple K n m S B φ b) h = 0 := by
  intro h hh
  rcases hh with hh | hh
  · obtain ⟨h, hh, rfl⟩ := hh
    rw [evaluate_included K n m S B φ b hb, presentationMap_relation K n S hh]
    exact map_zero φ.toAlgHom
  · obtain ⟨j, rfl⟩ := hh
    change (evaluateHom (Fin (n + m)) K B (solutionTuple K n m S B φ b) hb).toAlgHom
      (_ * _ - _) = 0
    rw [map_sub, map_mul]
    change evaluate (Fin (n + m)) K B (solutionTuple K n m S B φ b)
      (adjoinVariables K n m g) *
        evaluate (Fin (n + m)) K B (solutionTuple K n m S B φ b)
          (X (Fin (n + m)) K (Fin.natAdd n j)) -
            evaluate (Fin (n + m)) K B (solutionTuple K n m S B φ b)
              (adjoinVariables K n m (f j)) = 0
    rw [evaluate_included K n m S B φ b hb, evaluate_X,
      evaluate_included K n m S B φ b hb]
    simpa only [solutionTuple, Fin.append_right, sub_eq_zero] using heq j

/-- Actual convergent evaluation and quotient descent for bounded solutions
of the denominator equations. -/
def liftFromBase (φ : BoundedAlgHom K (ofRelations K n S) B)
    (b : Fin m → B) (hb : HasBoundedMonomials (Fin m) B b)
    (heq : ∀ j, φ (presentationMap K (ofRelations K n S) g) * b j =
      φ (presentationMap K (ofRelations K n S) (f j))) :
    BoundedAlgHom K (algebra K n m S g f) B :=
  liftRelations K (n + m) (relations K n m S g f) B
    (solutionTuple K n m S B φ b) (solutionTuple_bounded K n m S B φ b hb)
    (solutionTuple_relations K n m S g f B φ b (solutionTuple_bounded K n m S B φ b hb) heq)

theorem liftFromBase_comp_baseMap (φ : BoundedAlgHom K (ofRelations K n S) B)
    (b : Fin m → B) (hb : HasBoundedMonomials (Fin m) B b)
    (heq : ∀ j, φ (presentationMap K (ofRelations K n S) g) * b j =
      φ (presentationMap K (ofRelations K n S) (f j))) :
    (liftFromBase K n m S g f B φ b hb heq).comp (baseMap K n m S g f) = φ := by
  apply BoundedAlgHom.ext
  intro a
  obtain ⟨h, rfl⟩ := presentationMap_surjective K (ofRelations K n S) a
  change evaluate (Fin (n + m)) K B (solutionTuple K n m S B φ b)
    (adjoinVariables K n m h) = φ (presentationMap K (ofRelations K n S) h)
  exact evaluate_included K n m S B φ b (solutionTuple_bounded K n m S B φ b hb) h

theorem liftFromBase_coordinate (φ : BoundedAlgHom K (ofRelations K n S) B)
    (b : Fin m → B) (hb : HasBoundedMonomials (Fin m) B b)
    (heq : ∀ j, φ (presentationMap K (ofRelations K n S) g) * b j =
      φ (presentationMap K (ofRelations K n S) (f j))) (j : Fin m) :
    liftFromBase K n m S g f B φ b hb heq
      (coordinate K (algebra K n m S g f) (Fin.natAdd n j)) = b j := by
  change evaluate (Fin (n + m)) K B (solutionTuple K n m S B φ b)
    (X (Fin (n + m)) K (Fin.natAdd n j)) = b j
  rw [evaluate_X]
  exact Fin.append_right _ _ j

omit [IsUltrametricDist B] [CompleteSpace B] in
/-- With the genuine unit-ideal condition, restriction to the base determines
every bounded morphism out of the rational quotient. -/
theorem hom_ext_base (hunit : GeneratesUnitIdeal K n m S g f)
    (φ ψ : BoundedAlgHom K (algebra K n m S g f) B)
    (h : φ.comp (baseMap K n m S g f) = ψ.comp (baseMap K n m S g f)) : φ = ψ := by
  apply hom_ext_coordinates K (n + m) (relations K n m S g f) B
  intro i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · exact (congrArg φ (baseMap_coordinate K n m S g f i)).symm.trans
      ((congrArg (fun χ => χ (coordinate K (ofRelations K n S) i)) h).trans
        (congrArg ψ (baseMap_coordinate K n m S g f i)))
  · have hu : IsUnit (φ (baseMap K n m S g f
        (presentationMap K (ofRelations K n S) g))) :=
      (isUnit_baseMap_denominator K n m S g f hunit).map φ.toAlgHom
    apply hu.mul_left_cancel
    have hg := congrArg (fun χ => χ (presentationMap K (ofRelations K n S) g)) h
    calc
      _ = φ (baseMap K n m S g f
          (presentationMap K (ofRelations K n S) (f j))) := by
        exact (φ.toAlgHom.map_mul _ _).symm.trans
          (congrArg φ (coordinate_equation K n m S g f j))
      _ = ψ (baseMap K n m S g f
          (presentationMap K (ofRelations K n S) (f j))) :=
        congrArg (fun χ => χ (presentationMap K (ofRelations K n S) (f j))) h
      _ = ψ (baseMap K n m S g f (presentationMap K (ofRelations K n S) g)) *
          ψ (coordinate K (algebra K n m S g f) (Fin.natAdd n j)) := by
        exact (congrArg ψ (coordinate_equation K n m S g f j)).symm.trans
          (ψ.toAlgHom.map_mul _ _)
      _ = _ := congrArg (fun a => a *
        ψ (coordinate K (algebra K n m S g f) (Fin.natAdd n j))) hg.symm

/-- The actual rational quotient has the expected bounded extension property
for bounded solutions of its denominator equations. -/
theorem existsUnique_extension (hunit : GeneratesUnitIdeal K n m S g f)
    (φ : BoundedAlgHom K (ofRelations K n S) B)
    (b : Fin m → B) (hb : HasBoundedMonomials (Fin m) B b)
    (heq : ∀ j, φ (presentationMap K (ofRelations K n S) g) * b j =
      φ (presentationMap K (ofRelations K n S) (f j))) :
    ∃! ψ : BoundedAlgHom K (algebra K n m S g f) B,
      ψ.comp (baseMap K n m S g f) = φ := by
  refine ⟨liftFromBase K n m S g f B φ b hb heq,
    liftFromBase_comp_baseMap K n m S g f B φ b hb heq, fun ψ hψ => ?_⟩
  apply hom_ext_base K n m S g f B hunit
  rw [hψ, liftFromBase_comp_baseMap]

/-- Denominator control, forward spectrum inclusion, and the bounded extension
property of the constructed rational presentation. -/
theorem boundedExtension : BoundedExtensionStatement.{u, v} := by
  intro K _ _ _ n m S g f
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isUnit_baseMap_denominator K n m S g f
  · intro hunit x hx
    exact denominator_ne_zero K n m S g f hunit x hx
  · exact comap_mem_locus K n m S g f
  · intro B _ _ hunit φ ψ h
    exact hom_ext_base K n m S g f B hunit φ ψ h
  · intro B _ _ _ _ hunit φ b hb heq
    exact existsUnique_extension K n m S g f B hunit φ b hb heq

end Langlands.Analytic.RationalPresentation
