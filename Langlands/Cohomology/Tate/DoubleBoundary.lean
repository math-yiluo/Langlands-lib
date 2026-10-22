import Langlands.Cohomology.Tate.BoundaryDiagrams

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

lemma complexExact_preimage {S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)}
    (hS : S.ShortExact) (n : ℤ) (x : S.X₂.X n) (hx : S.g.f n x = 0) :
    ∃ y : S.X₁.X n, S.f.f n y = x :=
  (ShortComplex.moduleCat_exact_iff _).mp
    (hS.map_of_exact (HomologicalComplex.eval (ModuleCat R) (.up ℤ) n)).exact x hx

lemma complexExact_surjective {S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)}
    (hS : S.ShortExact) (n : ℤ) : Function.Surjective (S.g.f n) :=
  (hS.map_of_exact (HomologicalComplex.eval (ModuleCat R) (.up ℤ) n)).moduleCat_surjective_g

lemma complexExact_injective {S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)}
    (hS : S.ShortExact) (n : ℤ) : Function.Injective (S.f.f n) :=
  (hS.map_of_exact (HomologicalComplex.eval (ModuleCat R) (.up ℤ) n)).moduleCat_injective_f

lemma complexRow_zero_apply (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (n : ℤ) (x : S.X₁.X n) : S.g.f n (S.f.f n x) = 0 :=
  ConcreteCategory.congr_hom (congrArg (fun f => f.f n) S.zero) x

lemma complex_d_d_apply (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k : ℤ) (x : K.X i) : K.d j k (K.d i j x) = 0 :=
  ConcreteCategory.congr_hom (K.d_comp_d i j k) x

/-- In a commuting exact three-by-three diagram, the two successive boundaries anticommute. -/
lemma doubleBoundary_anticommutes
    (D : ShortComplex (ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)))
    (hrow₁ : D.X₁.ShortExact) (hrow₃ : D.X₃.ShortExact)
    (hcol₁ : (D.map ShortComplex.π₁).ShortExact)
    (hcol₂ : (D.map ShortComplex.π₂).ShortExact)
    (hcol₃ : (D.map ShortComplex.π₃).ShortExact) (n : ℤ) :
    hrow₃.δ n (n + 1) rfl ≫ hcol₁.δ (n + 1) (n + 1 + 1) rfl =
      -(hcol₃.δ n (n + 1) rfl ≫ hrow₁.δ (n + 1) (n + 1 + 1) rfl) := by
  ext c
  obtain ⟨z, hz, rfl⟩ := cycleClass_surjective D.X₃.X₃ n c
  obtain ⟨y₃₂, hy₃₂⟩ := complexExact_surjective hrow₃ n z
  obtain ⟨y₂₂, hy₂₂⟩ :
      ∃ y₂₂ : D.X₂.X₂.X n, D.g.τ₂.f n y₂₂ = y₃₂ :=
    complexExact_surjective hcol₂ n y₃₂
  have hz₃₂ : D.X₃.g.f (n + 1) (D.X₃.X₂.d n (n + 1) y₃₂) = 0 := by
    rw [complexMap_d_apply, hy₃₂, hz]
  obtain ⟨x₃₁, hx₃₁⟩ := complexExact_preimage hrow₃ (n + 1) _ hz₃₂
  have hcycle₃₁ : D.X₃.X₁.d (n + 1) (n + 1 + 1) x₃₁ = 0 :=
    hrow₃.d_eq_zero_of_f_eq_d_apply n (n + 1) y₃₂ x₃₁ hx₃₁ (n + 1 + 1)
  obtain ⟨x₂₁, hx₂₁⟩ :
      ∃ x₂₁ : D.X₂.X₁.X (n + 1), D.g.τ₁.f (n + 1) x₂₁ = x₃₁ :=
    complexExact_surjective hcol₁ (n + 1) x₃₁
  have hz₂₁ : D.g.τ₁.f (n + 1 + 1) (D.X₂.X₁.d (n + 1) (n + 1 + 1) x₂₁) = 0 := by
    rw [complexMap_d_apply, hx₂₁, hcycle₃₁]
  obtain ⟨x₁₁, hx₁₁⟩ :
      ∃ x₁₁ : D.X₁.X₁.X (n + 1 + 1),
        D.f.τ₁.f (n + 1 + 1) x₁₁ = D.X₂.X₁.d (n + 1) (n + 1 + 1) x₂₁ :=
    complexExact_preimage hcol₁ (n + 1 + 1) _ hz₂₁
  have hz₂₂ :
      D.g.τ₂.f (n + 1) (D.X₂.X₂.d n (n + 1) y₂₂ - D.X₂.f.f (n + 1) x₂₁) = 0 := by
    rw [map_sub, complexMap_d_apply, hy₂₂, complexSquare_left_apply, hx₂₁, hx₃₁, sub_self]
  obtain ⟨y₁₂, hy₁₂⟩ :
      ∃ y₁₂ : D.X₁.X₂.X (n + 1),
        D.f.τ₂.f (n + 1) y₁₂ = D.X₂.X₂.d n (n + 1) y₂₂ - D.X₂.f.f (n + 1) x₂₁ :=
    complexExact_preimage hcol₂ (n + 1) _ hz₂₂
  have hy₂₃ : D.g.τ₃.f n (D.X₂.g.f n y₂₂) = z := by
    rw [complexSquare_right_apply, hy₂₂, hy₃₂]
  have hx₁₃ :
      D.f.τ₃.f (n + 1) (D.X₁.g.f (n + 1) y₁₂) =
        D.X₂.X₃.d n (n + 1) (D.X₂.g.f n y₂₂) := by
    rw [complexSquare_right_apply, hy₁₂, map_sub, complexRow_zero_apply, sub_zero,
      complexMap_d_apply]
  have hcycle₁₃ :
      D.X₁.X₃.d (n + 1) (n + 1 + 1) (D.X₁.g.f (n + 1) y₁₂) = 0 :=
    hcol₃.d_eq_zero_of_f_eq_d_apply n (n + 1)
      (D.X₂.g.f n y₂₂) (D.X₁.g.f (n + 1) y₁₂) hx₁₃ (n + 1 + 1)
  have hd₁₂ :
      D.X₁.f.f (n + 1 + 1) (-x₁₁) = D.X₁.X₂.d (n + 1) (n + 1 + 1) y₁₂ := by
    apply complexExact_injective hcol₂ (n + 1 + 1)
    change D.f.τ₂.f (n + 1 + 1) (D.X₁.f.f (n + 1 + 1) (-x₁₁)) =
      D.f.τ₂.f (n + 1 + 1) (D.X₁.X₂.d (n + 1) (n + 1 + 1) y₁₂)
    rw [complexSquare_left_apply, complexMap_d_apply, hy₁₂, map_sub,
      complex_d_d_apply, ← complexMap_d_apply D.X₂.f, ← hx₁₁, zero_sub, map_neg, map_neg]
  change hcol₁.δ (n + 1) (n + 1 + 1) rfl
      (hrow₃.δ n (n + 1) rfl (cycleClass D.X₃.X₃ n z hz)) =
    -(hrow₁.δ (n + 1) (n + 1 + 1) rfl
      (hcol₃.δ n (n + 1) rfl (cycleClass D.X₃.X₃ n z hz)))
  have hcycle₁₁ : D.X₁.X₁.d (n + 1 + 1) (n + 1 + 1 + 1) x₁₁ = 0 :=
    hcol₁.d_eq_zero_of_f_eq_d_apply (n + 1) (n + 1 + 1)
      x₂₁ x₁₁ hx₁₁ (n + 1 + 1 + 1)
  have hl :
      hcol₁.δ (n + 1) (n + 1 + 1) rfl
        (hrow₃.δ n (n + 1) rfl (cycleClass D.X₃.X₃ n z hz)) =
      cycleClass D.X₁.X₁ (n + 1 + 1) x₁₁ hcycle₁₁ :=
    (congrArg
      (fun a : D.X₃.X₁.homology (n + 1) => (hcol₁.δ (n + 1) (n + 1 + 1) rfl).hom a)
      (delta_cycleClass hrow₃ n z hz y₃₂ hy₃₂ x₃₁ hx₃₁)).trans
        (delta_cycleClass hcol₁ (n + 1) x₃₁ hcycle₃₁ x₂₁ hx₂₁ x₁₁ hx₁₁)
  have hr :
      hrow₁.δ (n + 1) (n + 1 + 1) rfl
        (hcol₃.δ n (n + 1) rfl (cycleClass D.X₃.X₃ n z hz)) =
      -cycleClass D.X₁.X₁ (n + 1 + 1) x₁₁ hcycle₁₁ :=
    ((congrArg
      (fun a : D.X₁.X₃.homology (n + 1) => (hrow₁.δ (n + 1) (n + 1 + 1) rfl).hom a)
      (delta_cycleClass hcol₃ n z hz (D.X₂.g.f n y₂₂) hy₂₃
        (D.X₁.g.f (n + 1) y₁₂) hx₁₃)).trans
      (delta_cycleClass hrow₁ (n + 1) (D.X₁.g.f (n + 1) y₁₂)
        hcycle₁₃ y₁₂ rfl (-x₁₁) hd₁₂)).trans
      (cycleClass_neg D.X₁.X₁ (n + 1 + 1) x₁₁ hcycle₁₁)
  exact hl.trans ((neg_neg _).symm.trans (congrArg Neg.neg hr.symm))

end Langlands.Tate
