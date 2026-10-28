import Langlands.Geometry.Analytic.StrictTestDomain.FiniteRationalRefinementStatement
import Mathlib.Data.Fintype.EquivFin

/-! # Finite standard rational refinement -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open scoped BigOperators

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P : PresentedStrictAffinoidAlgebra K}

private def extendedEntry (d : RationalData K P) : Option (Fin d.arity) → P
  | none => d.denominator
  | some j => d.numerator j

private abbrev RefinementChoice {I : Type u} (D : I → RationalData K P) :=
  {φ : ∀ i, Option (Fin (D i).arity) // ∃ i, φ i = none}

private def refinementProduct {I : Type u} [Fintype I]
    (D : I → RationalData K P) (φ : RefinementChoice D) : P :=
  ∏ i, extendedEntry (D i) (φ.val i)

private theorem denominator_pos (d : RationalData K P) (x : BanachSpectrum P)
    (hx : x ∈ d.locus) : 0 < x d.denominator := by
  apply lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm _)
  intro hzero
  rcases d.no_common_zero x with hd | ⟨j, hj⟩
  · exact hd hzero.symm
  · exact hj (le_antisymm ((hx j).trans_eq hzero.symm)
      (apply_nonneg x.toMulRingSeminorm _))

private theorem extendedEntry_nonzero (d : RationalData K P) (x : BanachSpectrum P) :
    ∃ a, x (extendedEntry d a) ≠ 0 := by
  rcases d.no_common_zero x with hd | ⟨j, hj⟩
  · exact ⟨none, hd⟩
  · exact ⟨some j, hj⟩

private theorem eval_refinementProduct {I : Type u} [Fintype I]
    (D : I → RationalData K P) (φ : RefinementChoice D) (x : BanachSpectrum P) :
    x (refinementProduct D φ) = ∏ i, x (extendedEntry (D i) (φ.val i)) :=
  map_prod x.toMulRingSeminorm.toMonoidWithZeroHom _ _

private theorem refinementProduct_nonzero {I : Type u} [Fintype I]
    (D : I → RationalData K P)
    (hcover : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus)
    (x : BanachSpectrum P) :
    ∃ φ : RefinementChoice D, x (refinementProduct D φ) ≠ 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := hcover x
  choose φ hφ using fun i => extendedEntry_nonzero (D i) x
  let ψ := Function.update φ i₀ none
  refine ⟨⟨ψ, i₀, by simp [ψ]⟩, ?_⟩
  rw [eval_refinementProduct]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  by_cases hi : i = i₀
  · subst i
    simpa [ψ, extendedEntry] using (ne_of_gt (denominator_pos (D i₀) x hi₀))
  · simpa [ψ, hi] using hφ i

private theorem prod_two {I : Type u} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (i₀ i₁ : I) (hne : i₁ ≠ i₀) :
    (∏ i, a i) =
      a i₀ * a i₁ * ∏ i ∈ (Finset.univ.erase i₀).erase i₁, a i := by
  rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i₀)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase i₀) a
    (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i₁⟩)]
  exact (mul_assoc _ _ _).symm

private theorem refinementProduct_refines {I : Type u} [Fintype I]
    (D : I → RationalData K P)
    (hcover : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus)
    (φ : RefinementChoice D) (i₀ : I) (hi₀ : φ.val i₀ = none)
    (x : BanachSpectrum P)
    (hx : ∀ ψ : RefinementChoice D,
      x (refinementProduct D ψ) ≤ x (refinementProduct D φ)) :
    x ∈ (D i₀).locus := by
  classical
  obtain ⟨i₁, hi₁⟩ := hcover x
  by_cases heq : i₁ = i₀
  · simpa [heq] using hi₁
  obtain ⟨θ, hθ⟩ := refinementProduct_nonzero D hcover x
  have hpositive : 0 < x (refinementProduct D φ) :=
    (lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm _) hθ.symm).trans_le (hx θ)
  let s : Finset I := (Finset.univ.erase i₀).erase i₁
  let r : ℝ := ∏ i ∈ s, x (extendedEntry (D i) (φ.val i))
  have hr_nonneg : 0 ≤ r :=
    Finset.prod_nonneg fun i _ => apply_nonneg x.toMulRingSeminorm _
  have hφ : x (refinementProduct D φ) =
      x (D i₀).denominator * x (extendedEntry (D i₁) (φ.val i₁)) * r := by
    rw [eval_refinementProduct, prod_two _ i₀ i₁ heq]
    simp only [hi₀, extendedEntry]
    rfl
  have hr : 0 < r := by
    apply lt_of_le_of_ne hr_nonneg
    intro hz
    rw [← hz, mul_zero] at hφ
    exact (ne_of_gt hpositive) hφ
  intro j
  let ψval := Function.update (Function.update φ.val i₀ (some j)) i₁ none
  let ψ : RefinementChoice D := ⟨ψval, i₁, by simp [ψval]⟩
  have hrest :
      (∏ i ∈ s, x (extendedEntry (D i) (ψ.val i))) = r := by
    apply Finset.prod_congr rfl
    intro i hi
    have hi₁' : i ≠ i₁ := (Finset.mem_erase.mp hi).1
    have hi₀' : i ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [ψ, ψval, hi₁', hi₀']
  have hψ : x (refinementProduct D ψ) =
      x ((D i₀).numerator j) * x (D i₁).denominator * r := by
    rw [eval_refinementProduct, prod_two _ i₀ i₁ heq]
    change x (extendedEntry (D i₀) (ψ.val i₀)) *
      x (extendedEntry (D i₁) (ψ.val i₁)) *
        (∏ i ∈ s, x (extendedEntry (D i) (ψ.val i))) = _
    rw [hrest]
    simp [ψ, ψval, Ne.symm heq, extendedEntry]
  have hbound :
      x (extendedEntry (D i₁) (φ.val i₁)) ≤ x (D i₁).denominator := by
    cases hentry : φ.val i₁ with
    | none => simp [extendedEntry]
    | some k => exact hi₁ k
  have hcompare := hx ψ
  rw [hψ, hφ] at hcompare
  have hcancel := (mul_le_mul_iff_left₀ hr).mp hcompare
  have hfinal := hcancel.trans
    (mul_le_mul_of_nonneg_left hbound (apply_nonneg x.toMulRingSeminorm _))
  exact (mul_le_mul_iff_left₀ (denominator_pos (D i₁) x hi₁)).mp hfinal

/-- Every finite rational point cover has a finite standard rational refinement. -/
theorem finiteRationalRefinement : FiniteRationalRefinementStatement.{u} := by
  classical
  intro K _ _ _ P I _ D hcover
  let : Fintype I := Fintype.ofFinite I
  let C := RefinementChoice D
  let : Fintype C := Fintype.ofFinite C
  let e : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  let f : Fin (Fintype.card C) → P := fun j => refinementProduct D (e j)
  have hf : ∀ x : BanachSpectrum P, ∃ k, x (f k) ≠ 0 := by
    intro x
    obtain ⟨φ, hφ⟩ := refinementProduct_nonzero D hcover x
    refine ⟨e.symm φ, ?_⟩
    simpa [f] using hφ
  refine ⟨Fintype.card C, f, hf, ?_⟩
  intro j
  obtain ⟨i, hi⟩ := (e j).property
  refine ⟨i, ?_⟩
  intro x hx
  apply refinementProduct_refines D hcover (e j) i hi x
  intro ψ
  have h := hx (e.symm ψ)
  simpa [f] using h

end Langlands.Analytic.StrictTestDomain
