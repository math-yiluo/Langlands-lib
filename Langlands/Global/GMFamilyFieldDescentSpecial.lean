import Langlands.Global.GMFamilyFieldDescentGroupData
import Langlands.GroupScheme.Lie.LeviWeightFibreDeterminantStatement

/-! # Weighted fibre sums of fine roots vanish on the common kernel of the coarse characters -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Classical

namespace Langlands.GMFamily.FieldDescentTori

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {M : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom M.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {A₁ : CommGroupScheme (Spec (CommRingCat.of K))}
  {M₁ : GroupScheme (Spec (CommRingCat.of K))}

local instance fieldDescentSpecialAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local instance fieldDescentSpecialFiniteType :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- **Weighted fibre sums vanish.** If the weighted sum of the fine roots over a nonzero coarse
character is the restriction of a rational character, as provided by
`LeviWeightFibreDeterminantStatement`, then its functional vanishes on the common kernel of the
fine restrictions of the rational characters. -/
theorem fibre_sum_eq_zero (h2 : LeviWeightFibreDeterminantStatement.{u}) (l : M ⟶ G)
    (a : A.toGrp ⟶ M) (hAs : IsSplitTorus A.toGrp) (hAc : IsCentral a)
    (hA₁ : IsSplitTorus A₁.toGrp) (a₁ : A₁.toGrp ⟶ M₁)
    (m : M₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj M)
    (j : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj A ⟶ A₁)
    (hj : CommGroupScheme.groupHom j ≫ a₁ ≫ m = (GroupScheme.baseChange (algebraBaseMap k K)).map a)
    {β : characterLattice A} (hβ : β ≠ 0) {y : V A₁} (hy : y ∈ fineKernel a₁ m) :
    ∑ α ∈ (hA₁.finite_relativeRoots ((a₁ ≫ m) ≫
        (GroupScheme.baseChange (algebraBaseMap k K)).map l)).toFinset.filter
        (fun α => j ≫ α = characterLattice.baseChange (algebraBaseMap k K) A β),
      (Module.finrank K (weightSpace ((a₁ ≫ m) ≫
        (GroupScheme.baseChange (algebraBaseMap k K)).map l) α) : ℝ) * eval A₁ α y = 0 := by
  set i₁ := (a₁ ≫ m) ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map l with hi₁
  obtain ⟨χ, hχ⟩ := h2 k K G M l A a hAs hAc β
  have h := hχ A₁ (a₁ ≫ m) j hA₁ hj
  have hbc : characterLattice.baseChange (algebraBaseMap k K) A β ≠ 0 := by
    intro h0
    apply hβ
    apply (hAs.characterLattice_baseChange_bijective (algebraBaseMap k K) A).injective
    rw [h0, map_zero]
  set S := (hA₁.finite_relativeRoots i₁).toFinset.filter
    (fun α => j ≫ α = characterLattice.baseChange (algebraBaseMap k K) A β) with hS
  have hsum : (∑ᶠ (α : characterLattice A₁)
      (_ : j ≫ α = characterLattice.baseChange (algebraBaseMap k K) A β),
        (Module.finrank K (weightSpace i₁ α) : ℤ) • α) =
      ∑ α ∈ S, (Module.finrank K (weightSpace i₁ α) : ℤ) • α := by
    apply finsum_cond_eq_sum_of_cond_iff
    intro α hα
    rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset, relativeRoots_eq_roots, mem_roots]
    constructor
    · intro he
      refine ⟨⟨?_, ?_⟩, he⟩
      · rintro rfl
        apply hbc
        rw [← he]
        simp
      · intro hbot
        apply hα
        rw [hbot, finrank_bot, Nat.cast_zero, zero_smul]
    · exact fun h => h.2
  have h' : fineCharacter a₁ m χ = ∑ α ∈ S, (Module.finrank K (weightSpace i₁ α) : ℤ) • α := by
    rw [← hsum]
    convert h using 1
    rw [characterRestrict_comp]
    rfl
  have hval := congrArg (fun c => eval A₁ c y) h'
  simp only at hval
  rw [mem_fineKernel.mp hy χ] at hval
  rw [hval, ← evalHom_apply, map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro α _
  rw [evalHom_apply, eval_zsmul, LinearMap.smul_apply, smul_eq_mul, Int.cast_natCast]

/-- Two fine characters agree on the coarse cocharacters exactly when their pullbacks to the
scalar extension of the coarse split component agree. -/
theorem domRestrict_eval_eq_iff (hAs : IsSplitTorus A.toGrp)
    (j : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj A ⟶ A₁)
    {α α' : characterLattice A₁} :
    (eval A₁ α).domRestrict (LinearMap.range (fieldCocharacterInclusion j)) =
        (eval A₁ α').domRestrict (LinearMap.range (fieldCocharacterInclusion j)) ↔
      j ≫ α = j ≫ α' := by
  constructor
  · intro h
    obtain ⟨β, hβ⟩ := (hAs.characterLattice_baseChange_bijective (algebraBaseMap k K) A).surjective
      (j ≫ α)
    obtain ⟨β', hβ'⟩ :=
      (hAs.characterLattice_baseChange_bijective (algebraBaseMap k K) A).surjective (j ≫ α')
    have hev : eval A β = eval A β' := by
      apply LinearMap.ext
      intro x
      have hx := LinearMap.congr_fun h ⟨fieldCocharacterInclusion j x, x, rfl⟩
      simp only [LinearMap.domRestrict_apply] at hx
      rwa [eval_fieldCocharacterInclusion_of_eq j hβ.symm,
        eval_fieldCocharacterInclusion_of_eq j hβ'.symm] at hx
    rw [← hβ, ← hβ', eval_injective hAs hev]
  · intro h
    ext ⟨_, x, rfl⟩
    simp only [LinearMap.domRestrict_apply]
    rw [eval_fieldCocharacterInclusion, eval_fieldCocharacterInclusion, h]

/-- **The fibre-sum condition for the roots of a split torus.** -/
theorem torus_special (h2 : LeviWeightFibreDeterminantStatement.{u}) (l : M ⟶ G)
    (a : A.toGrp ⟶ M) (hAs : IsSplitTorus A.toGrp) (hAc : IsCentral a)
    (hA₁ : IsSplitTorus A₁.toGrp) (a₁ : A₁.toGrp ⟶ M₁)
    (m : M₁ ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj M)
    (j : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj A ⟶ A₁)
    (hj : CommGroupScheme.groupHom j ≫ a₁ ≫ m = (GroupScheme.baseChange (algebraBaseMap k K)).map a)
    {T : CommGroupScheme (Spec (CommRingCat.of K))} (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G) (g : A₁ ⟶ T)
    (hgt : (a₁ ≫ m) ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map l =
      CommGroupScheme.groupHom g ≫ t)
    (γ : characterLattice T)
    (hβ : ((eval T γ).comp (cocharacterMapReal g)).domRestrict
      (LinearMap.range (fieldCocharacterInclusion j)) ≠ 0)
    (y : V A₁) (hy : y ∈ fineKernel a₁ m) :
    ∑ δ ∈ (hT.finite_relativeRoots t).toFinset.filter (fun δ =>
        ((eval T δ).comp (cocharacterMapReal g)).domRestrict
            (LinearMap.range (fieldCocharacterInclusion j)) =
          ((eval T γ).comp (cocharacterMapReal g)).domRestrict
            (LinearMap.range (fieldCocharacterInclusion j))),
      (Module.finrank K (weightSpace t δ) : ℝ) * eval T δ (cocharacterMapReal g y) = 0 := by
  obtain ⟨β₀, hβ₀⟩ := (hAs.characterLattice_baseChange_bijective (algebraBaseMap k K) A).surjective
    (j ≫ g ≫ γ)
  have hβ₀ne : β₀ ≠ 0 := by
    rintro rfl
    apply hβ
    rw [eval_comp_cocharacterMapReal]
    have h0 : (eval A₁ (g ≫ γ)).domRestrict (LinearMap.range (fieldCocharacterInclusion j)) =
        (eval A₁ (0 : characterLattice A₁)).domRestrict
          (LinearMap.range (fieldCocharacterInclusion j)) := by
      rw [domRestrict_eval_eq_iff hAs, ← hβ₀, map_zero]
      simp
    rw [h0, eval_zero]
    rfl
  have hbc : characterLattice.baseChange (algebraBaseMap k K) A β₀ ≠ 0 := by
    intro h0
    apply hβ₀ne
    apply (hAs.characterLattice_baseChange_bijective (algebraBaseMap k K) A).injective
    rw [h0, map_zero]
  have hfilter : (hT.finite_relativeRoots t).toFinset.filter (fun δ =>
        ((eval T δ).comp (cocharacterMapReal g)).domRestrict
            (LinearMap.range (fieldCocharacterInclusion j)) =
          ((eval T γ).comp (cocharacterMapReal g)).domRestrict
            (LinearMap.range (fieldCocharacterInclusion j))) =
      (hT.finite_relativeRoots t).toFinset.filter (fun δ =>
        j ≫ g ≫ δ = characterLattice.baseChange (algebraBaseMap k K) A β₀) := by
    apply Finset.filter_congr
    intro δ _
    rw [eval_comp_cocharacterMapReal, eval_comp_cocharacterMapReal, domRestrict_eval_eq_iff hAs,
      hβ₀]
  rw [hfilter]
  have hfib := fibre_sum_eq_zero h2 l a hAs hAc hA₁ a₁ m j hj hβ₀ne hy
  rw [hgt] at hfib
  set s := (hT.finite_relativeRoots t).toFinset.filter
    (fun δ => j ≫ g ≫ δ = characterLattice.baseChange (algebraBaseMap k K) A β₀) with hs
  set u := (hA₁.finite_relativeRoots (CommGroupScheme.groupHom g ≫ t)).toFinset.filter
    (fun α => j ≫ α = characterLattice.baseChange (algebraBaseMap k K) A β₀) with hu
  have hmaps : ∀ δ ∈ s, g ≫ δ ∈ u := by
    intro δ hδ
    obtain ⟨hδR, hδβ⟩ := Finset.mem_filter.mp hδ
    rw [Set.Finite.mem_toFinset] at hδR
    refine Finset.mem_filter.mpr ⟨?_, hδβ⟩
    rw [Set.Finite.mem_toFinset, relativeRoots_eq_roots]
    have hne : g ≫ δ ≠ 0 := by
      intro h0
      apply hbc
      rw [← hδβ, h0]
      simp
    rw [relativeRoots_eq_roots] at hδR
    exact (mem_roots_comp_iff hT hA₁ g t _).mpr ⟨hne, δ, hδR, rfl⟩
  rw [← hfib, ← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro α hα
  have hαne : α ≠ 0 := by
    rintro rfl
    apply hbc
    rw [← (Finset.mem_filter.mp hα).2]
    simp
  rw [finrank_weightSpace_comp hT hA₁ g t hαne, Nat.cast_sum, Finset.sum_mul]
  have hst : s.filter (fun δ => g ≫ δ = α) =
      (hT.finite_relativeRoots t).toFinset.filter (fun δ => g ≫ δ = α) := by
    ext δ
    simp only [Finset.mem_filter, hs]
    constructor
    · rintro ⟨⟨h, -⟩, he⟩
      exact ⟨h, he⟩
    · rintro ⟨h, he⟩
      exact ⟨⟨h, by rw [he]; exact (Finset.mem_filter.mp hα).2⟩, he⟩
  rw [hst]
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [eval_cocharacterMapReal, (Finset.mem_filter.mp hδ).2]

end Langlands.GMFamily.FieldDescentTori
