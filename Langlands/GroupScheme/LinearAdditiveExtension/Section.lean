import Langlands.GroupScheme.LinearAdditiveExtension.Correction

/-! # The homomorphic section determined by a corrected crossed homomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LinearAdditiveExtension

variable {k : Type u} [Field k] {Λ : Type u} [AddCommGroup Λ]

local notation "𝔾ₐ" => VectorGroup.groupScheme (CommRingCat.of k) 1
local notation "𝔻" => Diagonalizable.groupScheme (CommRingCat.of k) Λ

variable {E : GroupScheme (Spec (CommRingCat.of k))}
  (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
  (a : kernel q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
  (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))
  (b : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp (kernel q))
  (hlin : ∀ (T : Over (Spec (CommRingCat.of k)))
    (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) (x : T ⟶ (kernel q).X),
    b.act d x ≫ a.hom.hom = (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom))
  (c : E.X ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X)
  (hc₁ : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ E.X),
    cd ((g * h) ≫ c) = cd (g ≫ c) + chi q χ g * cd (h ≫ c))
  (hc₂ : ∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ (kernel q).X),
    cd ((u ≫ (kernelι q).hom.hom) ≫ c) = cd (u ≫ a.hom.hom))

include hc₁ in
theorem cd_one_comp {T : Over (Spec (CommRingCat.of k))} : cd ((1 : T ⟶ E.X) ≫ c) = 0 := by
  have h := hc₁ T 1 1
  rw [mul_one, chi_one, one_mul] at h
  linear_combination -h

include hc₁ hc₂ in
/-- Two points with the same image in `D` on which `c` vanishes are equal. -/
theorem eq_of_cd_eq_zero (ha : IsClosedSubgroup a) {T : Over (Spec (CommRingCat.of k))}
    {g g' : T ⟶ E.X} (hq : g ≫ q.hom.hom = g' ≫ q.hom.hom) (hg : cd (g ≫ c) = 0)
    (hg' : cd (g' ≫ c) = 0) : g = g' := by
  have : IsClosedImmersion a.hom.hom.left := ha
  have : Mono a.hom.hom := Over.mono_of_mono_left _
  set u := kpt q g g' hq
  have hgu := eq_mul_kpt q hq
  have h1 : chi q χ g * cd (u ≫ a.hom.hom) = 0 := by
    have := hc₁ T g (u ≫ (kernelι q).hom.hom)
    rw [← hgu, hg', hc₂, hg, zero_add] at this
    exact this.symm
  have h2 : cd (u ≫ a.hom.hom) = 0 := by
    have e := chi_mul_inv q χ g
    linear_combination chi q χ g⁻¹ * h1 - cd (u ≫ a.hom.hom) * e
  have h3 : u = 1 := by
    apply (cancel_mono a.hom.hom).mp
    rw [MonObj.one_comp]
    exact cd_injective (by rw [h2, cd_one])
  rw [hgu, show kpt q g g' hq = 1 from h3, MonObj.one_comp, mul_one]

variable [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

include hlin hc₁ hc₂ in
/-- A crossed homomorphism `c` extending `a` with all values in the closed subgroup gives a
homomorphic section of `q`. -/
theorem exists_section (ha : IsClosedSubgroup a)
    (hc₃ : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      g ≫ c ∈ (SubgroupFunctor.range a).carrier T) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E, s ≫ q = 𝟙 _ := by
  obtain ⟨c₀, hc₀⟩ := SubgroupFunctor.mem_range.mp (hc₃ E.X (𝟙 _))
  rw [Category.id_comp] at hc₀
  -- The correction `w(g) = (b(q(g)⁻¹, c₀(g)))⁻¹` and `σ(g) = g · w(g)`.
  set w : E.X ⟶ (kernel q).X := (b.act (q.hom.hom⁻¹) c₀)⁻¹ with hw
  set σ : E.X ⟶ E.X := 𝟙 E.X * (w ≫ (kernelι q).hom.hom) with hσ
  have hgσ : ∀ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ E.X),
      g ≫ σ = g * ((g ≫ w) ≫ (kernelι q).hom.hom) := by
    intro T g
    rw [hσ, MonObj.comp_mul, Category.comp_id, Category.assoc]
  have hσq : σ ≫ q.hom.hom = q.hom.hom := by
    rw [hσ, MonObj.mul_comp, kernel_comp_q, Category.id_comp, mul_one]
  have hσc : ∀ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ E.X), cd ((g ≫ σ) ≫ c) = 0 := by
    intro T g
    rw [hgσ, hc₁, hc₂, hw, GrpObj.comp_inv, GrpObj.inv_comp, cd_inv,
      AutomorphicAction.naturality, hlin, cd_act, GrpObj.comp_inv, Category.assoc, hc₀]
    have e := charValue_mul_inv χ (g ≫ q.hom.hom)
    linear_combination -(cd (g ≫ c)) * e
  have hσinv : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (u : T ⟶ (kernel q).X),
      (g * (u ≫ (kernelι q).hom.hom)) ≫ σ = g ≫ σ := by
    intro T g u
    apply eq_of_cd_eq_zero q a χ c hc₁ hc₂ ha _ (hσc _) (hσc _)
    rw [Category.assoc, Category.assoc, hσq, mul_kernel_comp_q]
  obtain ⟨s, hs⟩ : ∃ s : (𝔻).X ⟶ E.X, q.hom.hom ≫ s = σ :=
    ⟨descend q σ hσinv, fac_descend q σ hσinv⟩
  have hsq : s ≫ q.hom.hom = 𝟙 _ := by
    apply (cancel_epi q.hom.hom).mp
    rw [← Category.assoc, hs, hσq, Category.comp_id]
  have hone : η[(𝔻).X] ≫ s = η[E.X] := by
    rw [← IsMonHom.one_hom q.hom.hom, Category.assoc, hs]
    have h1 : (η[E.X] : 𝟙_ _ ⟶ E.X) = (1 : 𝟙_ _ ⟶ E.X) := by
      rw [CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [h1]
    exact eq_of_cd_eq_zero q a χ c hc₁ hc₂ ha (by rw [Category.assoc, hσq]) (hσc _)
      (cd_one_comp q χ c hc₁)
  have hmul : μ[(𝔻).X] ≫ s = (s ⊗ₘ s) ≫ μ[E.X] := by
    have := FpqcHomDescent.epi_tensorHom q
    apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).mp
    rw [← IsMonHom.mul_hom_assoc, hs, tensorHom_comp_tensorHom_assoc, hs]
    apply hom_ext_lift
    intro T g h
    rw [lift_map_assoc, ← CategoryTheory.Hom.mul_def, ← Category.assoc, ← CategoryTheory.Hom.mul_def]
    apply eq_of_cd_eq_zero q a χ c hc₁ hc₂ ha
    · simp only [Category.assoc, hσq, MonObj.mul_comp]
    · exact hσc _
    · rw [hc₁, hσc, hσc, mul_zero, add_zero]
  exact ⟨Grp.homMk'' s hone hmul, Grp.hom_ext _ _ (by
    change s ≫ q.hom.hom = 𝟙 _
    exact hsq)⟩

end Langlands.GroupScheme.LinearAdditiveExtension
