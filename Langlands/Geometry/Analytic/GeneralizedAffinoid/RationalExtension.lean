import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalExtensionStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelationsUniversalProperty
import Mathlib.Algebra.BigOperators.Fin

/-! # Bounded extension for weighted rational presentations -/

noncomputable section

universe u v

namespace Langlands.Analytic

open GeneralizedTateAlgebra

/-- Concatenating two bounded weighted tuples preserves the monomial bound,
including empty blocks and targets whose unit is not normalized. -/
theorem GeneralizedTateAlgebra.hasBoundedMonomials_append
    {n m : ℕ} (r : PositivePolyradius (Fin n)) (s : PositivePolyradius (Fin m))
    (B : Type v) [NormedCommRing B] (a : Fin n → B) (b : Fin m → B)
    (ha : HasBoundedMonomials r B a) (hb : HasBoundedMonomials s B b) :
    HasBoundedMonomials (r.append s) B (Fin.append a b) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := ha
  obtain ⟨D, hDpos, hD⟩ := hb
  refine ⟨C * D, mul_pos hCpos hDpos, fun d => ?_⟩
  let dl : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => d (Fin.castAdd m i))
  let dr : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => d (Fin.natAdd n j))
  have hm : StrictTateAlgebra.monomialValue (Fin (n + m)) B (Fin.append a b) d =
      StrictTateAlgebra.monomialValue (Fin n) B a dl *
        StrictTateAlgebra.monomialValue (Fin m) B b dr := by
    simp only [StrictTateAlgebra.monomialValue,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right, dl, dr,
      Finsupp.coe_equivFunOnFinite_symm]
  have hw : (r.append s).weight d = r.weight dl * s.weight dr := by
    simp only [PositivePolyradius.weight,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rw [Fin.prod_univ_add]
    simp only [PositivePolyradius.append_castAdd, PositivePolyradius.append_natAdd,
      dl, dr, Finsupp.coe_equivFunOnFinite_symm]
  rw [hm, hw]
  calc
    _ ≤ ‖StrictTateAlgebra.monomialValue (Fin n) B a dl‖ *
        ‖StrictTateAlgebra.monomialValue (Fin m) B b dr‖ := norm_mul_le _ _
    _ ≤ (C * r.weight dl) * (D * s.weight dr) :=
      mul_le_mul (hC dl) (hD dr) (norm_nonneg _)
        (mul_nonneg hCpos.le (r.weight_pos dl).le)
    _ = _ := by ring

namespace PresentedAffinoidAlgebra.RationalPresentation

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)

/-- The fraction equations and unit-ideal generation force a unit denominator. -/
theorem isUnit_baseMap_denominator (hunit : GeneratesUnitIdeal K A g f) :
    IsUnit (baseMap K A s g f (presentationMap K A g)) := by
  let J : Ideal (algebra K A s g f) :=
    Ideal.span {baseMap K A s g f (presentationMap K A g)}
  have hle : Ideal.span (insert (presentationMap K A g)
      (Set.range fun j => presentationMap K A (f j))) ≤
      Ideal.comap (baseMap K A s g f).toAlgHom.toRingHom J := by
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ⟨j, rfl⟩
    · exact Ideal.mem_span_singleton_self _
    · change baseMap K A s g f (presentationMap K A (f j)) ∈ J
      apply Ideal.mem_span_singleton.mpr
      exact ⟨fraction K A s g f j, (fraction_equation K A s g f j).symm⟩
  have h1 : (1 : algebra K A s g f) ∈ J := by
    have h := hle (show (1 : A) ∈ Ideal.span (insert (presentationMap K A g)
      (Set.range fun j => presentationMap K A (f j))) by
        rw [hunit]
        trivial)
    simpa only [Ideal.mem_comap, map_one] using h
  exact Ideal.span_singleton_eq_top.mp (J.eq_top_iff_one.mpr h1)

/-- A point in the weighted locus cannot kill the denominator under generation. -/
theorem denominator_ne_zero (hunit : GeneratesUnitIdeal K A g f)
    (x : BanachSpectrum A) (hx : x ∈ locus K A s g f) :
    x (presentationMap K A g) ≠ 0 := by
  intro hg
  have hle : Ideal.span (insert (presentationMap K A g)
      (Set.range fun j => presentationMap K A (f j))) ≤ x.kernel := by
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ⟨j, rfl⟩
    · exact hg
    · exact le_antisymm (by simpa only [hg, mul_zero] using hx j)
        (apply_nonneg x.toMulRingSeminorm _)
  have h1 : x (1 : A) = 0 :=
    hle (show (1 : A) ∈ Ideal.span (insert (presentationMap K A g)
      (Set.range fun j => presentationMap K A (f j))) by
        rw [hunit]
        trivial)
  exact one_ne_zero ((map_one x.toMulRingSeminorm).symm.trans h1)

variable (B : Type v) [NormedCommRing B] [NormedAlgebra K B]

/-- Base restriction and the new fraction coordinates determine a bounded map. -/
theorem hom_ext_base_fraction
    (φ ψ : BoundedAlgHom K (algebra K A s g f) B)
    (hbase : φ.comp (baseMap K A s g f) = ψ.comp (baseMap K A s g f))
    (hfrac : ∀ j, φ (fraction K A s g f j) = ψ (fraction K A s g f j)) : φ = ψ := by
  apply hom_ext_coordinate K B (algebra K A s g f)
  intro i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · exact (congrArg φ (baseMap_coordinate K A s g f i)).symm.trans
      ((congrArg (fun χ => χ (coordinate K A i)) hbase).trans
        (congrArg ψ (baseMap_coordinate K A s g f i)))
  · exact hfrac j

/-- Under generation, equal base restrictions force equal fraction coordinates. -/
theorem hom_ext_base (hunit : GeneratesUnitIdeal K A g f)
    (φ ψ : BoundedAlgHom K (algebra K A s g f) B)
    (h : φ.comp (baseMap K A s g f) = ψ.comp (baseMap K A s g f)) : φ = ψ := by
  apply hom_ext_base_fraction K A s g f B φ ψ h
  intro j
  have hu : IsUnit (φ (baseMap K A s g f (presentationMap K A g))) :=
    (isUnit_baseMap_denominator K A s g f hunit).map φ.toAlgHom
  apply hu.mul_left_cancel
  have hg := congrArg (fun χ => χ (presentationMap K A g)) h
  calc
    _ = φ (baseMap K A s g f (presentationMap K A (f j))) :=
      (φ.toAlgHom.map_mul _ _).symm.trans (congrArg φ (fraction_equation K A s g f j))
    _ = ψ (baseMap K A s g f (presentationMap K A (f j))) :=
      congrArg (fun χ => χ (presentationMap K A (f j))) h
    _ = ψ (baseMap K A s g f (presentationMap K A g)) * ψ (fraction K A s g f j) :=
      (congrArg ψ (fraction_equation K A s g f j)).symm.trans (ψ.toAlgHom.map_mul _ _)
    _ = _ := congrArg (fun a => a * ψ (fraction K A s g f j)) hg.symm

/-- The old coordinate images followed by the prescribed fractions. -/
def solutionTuple (φ : BoundedAlgHom K A B) (b : Fin m → B) : Fin (A.arity + m) → B :=
  Fin.append (fun i => φ (coordinate K A i)) b

theorem solutionTuple_bounded (φ : BoundedAlgHom K A B) (b : Fin m → B)
    (hb : HasBoundedMonomials s B b) :
    HasBoundedMonomials (A.polyradius.append s) B (solutionTuple K A B φ b) :=
  hasBoundedMonomials_append A.polyradius s B _ b
    (hasBoundedMonomials_coordinate K B A φ) hb

section CompleteTarget

variable [IsUltrametricDist B] [CompleteSpace B]

/-- Evaluation on the old-variable inclusion agrees with the given bounded map. -/
theorem evaluate_included (φ : BoundedAlgHom K A B) (b : Fin m → B)
    (hb : HasBoundedMonomials (A.polyradius.append s) B (solutionTuple K A B φ b))
    (h : GeneralizedTateAlgebra A.polyradius K) :
    evaluate (A.polyradius.append s) K B (solutionTuple K A B φ b)
      (appendLeft A.polyradius s K h) = φ (presentationMap K A h) := by
  have hmaps :
      (evaluateHom (A.polyradius.append s) K B (solutionTuple K A B φ b) hb).comp
        (appendLeft A.polyradius s K) = φ.comp (presentationMap K A) := by
    apply GeneralizedTateAlgebra.hom_ext
    intro i
    change evaluate (A.polyradius.append s) K B (solutionTuple K A B φ b)
      (appendLeft A.polyradius s K (X A.polyradius K i)) = _
    rw [appendLeft_X, evaluate_X]
    exact Fin.append_left _ _ i
  exact congrArg (fun χ => χ h) hmaps

theorem solutionTuple_relations (φ : BoundedAlgHom K A B) (b : Fin m → B)
    (hb : HasBoundedMonomials (A.polyradius.append s) B (solutionTuple K A B φ b))
    (heq : ∀ j, φ (presentationMap K A g) * b j = φ (presentationMap K A (f j))) :
    ∀ h ∈ Adjoin.relations K A s (equations K A s g f),
      evaluate (A.polyradius.append s) K B (solutionTuple K A B φ b) h = 0 := by
  intro h hh
  rcases hh with ⟨h, hh, rfl⟩ | ⟨j, rfl⟩
  · rw [evaluate_included K A s B φ b hb,
      (presentationMap_eq_zero_iff K A h).mpr hh]
    exact map_zero φ.toAlgHom
  · change (evaluateHom (A.polyradius.append s) K B (solutionTuple K A B φ b) hb).toAlgHom
      (_ * _ - _) = 0
    rw [map_sub, map_mul]
    change evaluate (A.polyradius.append s) K B (solutionTuple K A B φ b)
      (appendLeft A.polyradius s K g) *
        evaluate (A.polyradius.append s) K B (solutionTuple K A B φ b)
          (X (A.polyradius.append s) K (Fin.natAdd A.arity j)) -
            evaluate (A.polyradius.append s) K B (solutionTuple K A B φ b)
              (appendLeft A.polyradius s K (f j)) = 0
    rw [evaluate_included K A s B φ b hb, evaluate_X, evaluate_included K A s B φ b hb]
    simpa only [solutionTuple, Fin.append_right, sub_eq_zero] using heq j

/-- Bounded weighted evaluation descended through the actual rational relations. -/
def liftFromBase (φ : BoundedAlgHom K A B) (b : Fin m → B)
    (hb : HasBoundedMonomials s B b)
    (heq : ∀ j, φ (presentationMap K A g) * b j = φ (presentationMap K A (f j))) :
    BoundedAlgHom K (algebra K A s g f) B :=
  evaluateRelations K B (A.arity + m) (A.polyradius.append s)
    (Adjoin.relations K A s (equations K A s g f))
    (solutionTuple K A B φ b) (solutionTuple_bounded K A s B φ b hb)
    (solutionTuple_relations K A s g f B φ b (solutionTuple_bounded K A s B φ b hb) heq)

theorem liftFromBase_comp_baseMap (φ : BoundedAlgHom K A B) (b : Fin m → B)
    (hb : HasBoundedMonomials s B b)
    (heq : ∀ j, φ (presentationMap K A g) * b j = φ (presentationMap K A (f j))) :
    (liftFromBase K A s g f B φ b hb heq).comp (baseMap K A s g f) = φ := by
  apply BoundedAlgHom.ext
  intro a
  obtain ⟨h, rfl⟩ := presentationMap_surjective K A a
  change evaluate (A.polyradius.append s) K B (solutionTuple K A B φ b)
    (appendLeft A.polyradius s K h) = φ (presentationMap K A h)
  exact evaluate_included K A s B φ b (solutionTuple_bounded K A s B φ b hb) h

theorem liftFromBase_fraction (φ : BoundedAlgHom K A B) (b : Fin m → B)
    (hb : HasBoundedMonomials s B b)
    (heq : ∀ j, φ (presentationMap K A g) * b j = φ (presentationMap K A (f j))) (j : Fin m) :
    liftFromBase K A s g f B φ b hb heq (fraction K A s g f j) = b j := by
  change evaluate (A.polyradius.append s) K B (solutionTuple K A B φ b)
    (X (A.polyradius.append s) K (Fin.natAdd A.arity j)) = b j
  rw [evaluate_X]
  exact Fin.append_right _ _ j

/-- Prescribing the base and fractions gives a unique extension without generation. -/
theorem existsUnique_extension_fraction (φ : BoundedAlgHom K A B) (b : Fin m → B)
    (hb : HasBoundedMonomials s B b)
    (heq : ∀ j, φ (presentationMap K A g) * b j = φ (presentationMap K A (f j))) :
    ∃! ψ : BoundedAlgHom K (algebra K A s g f) B,
      ψ.comp (baseMap K A s g f) = φ ∧ ∀ j, ψ (fraction K A s g f j) = b j := by
  refine ⟨liftFromBase K A s g f B φ b hb heq,
    ⟨liftFromBase_comp_baseMap K A s g f B φ b hb heq,
      liftFromBase_fraction K A s g f B φ b hb heq⟩, ?_⟩
  intro ψ hψ
  apply hom_ext_base_fraction K A s g f B
  · rw [hψ.1, liftFromBase_comp_baseMap]
  · intro j
    rw [hψ.2 j, liftFromBase_fraction]

/-- Under generation, the base restriction alone specifies the unique extension. -/
theorem existsUnique_extension (hunit : GeneratesUnitIdeal K A g f)
    (φ : BoundedAlgHom K A B) (b : Fin m → B) (hb : HasBoundedMonomials s B b)
    (heq : ∀ j, φ (presentationMap K A g) * b j = φ (presentationMap K A (f j))) :
    ∃! ψ : BoundedAlgHom K (algebra K A s g f) B,
      ψ.comp (baseMap K A s g f) = φ := by
  refine ⟨liftFromBase K A s g f B φ b hb heq,
    liftFromBase_comp_baseMap K A s g f B φ b hb heq, fun ψ hψ => ?_⟩
  apply hom_ext_base K A s g f B hunit
  rw [hψ, liftFromBase_comp_baseMap]

end CompleteTarget

/-- All five clauses of the unchanged weighted rational bounded-extension target. -/
theorem boundedExtension : BoundedExtensionStatement.{u, v} := by
  intro K _ _ A m s g f
  refine ⟨isUnit_baseMap_denominator K A s g f, denominator_ne_zero K A s g f, ?_, ?_, ?_⟩
  · intro B _ _
    exact hom_ext_base K A s g f B
  · intro B _ _ _ _
    exact existsUnique_extension_fraction K A s g f B
  · intro B _ _ _ _
    exact existsUnique_extension K A s g f B

end PresentedAffinoidAlgebra.RationalPresentation
end Langlands.Analytic
