import Langlands.AlgebraicGeometry.Modules.QuasiAffineLineBundleSectionBasis
import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Modules.PrincipalGenerationOpenLiftProof
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # A global section generating a line bundle at finitely many points of an affine scheme -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.FinitePointsGeneratingSection

open Langlands.SchemeModule Langlands.SchemeModule.LineBundleDescent

variable {Y : Scheme.{u}}

/-- On an affine scheme, a point which is not a specialization of another one is separated
from it by a global function. -/
lemma exists_basicOpen_separating [IsAffine Y] {y y' : Y} (h : ¬ y' ⤳ y) :
    ∃ a : Γ(Y, ⊤), y ∈ Y.basicOpen a ∧ y' ∉ Y.basicOpen a := by
  have hy : y ∈ (closure ({y'} : Set Y))ᶜ := by
    rwa [Set.mem_compl_iff, ← specializes_iff_mem_closure]
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hya, hsub⟩ := (isBasis_basicOpen Y).exists_subset_of_mem_open hy
    isClosed_closure.isOpen_compl
  exact ⟨a, hya, fun h' ↦ hsub h' (subset_closure rfl)⟩

/-- The germ of a sum of a unit and non-units in a local ring is a unit. -/
lemma isUnit_add_of_nonunits {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : ¬ IsUnit b) : IsUnit (a + b) := by
  by_contra hab
  have h1 : a + b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hab
  have h2 : b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hb
  have h3 : a ∈ IsLocalRing.maximalIdeal R := by
    simpa using Ideal.sub_mem _ h1 h2
  exact (IsLocalRing.mem_maximalIdeal _).mp h3 ha

/-- On an affine scheme, a line bundle has a global section generating it at every point of a
finite set of points no two of which specialize to each other. -/
theorem exists_section_mem_trivializationOpen [IsAffine Y] (N : LineBundle Y) (F : Finset Y)
    (hF : ∀ x ∈ F, ∀ y ∈ F, x ⤳ y → x = y) :
    ∃ σ : GlobalSections N.obj, ∀ y ∈ F, y ∈ trivializationOpen N.obj σ := by
  classical
  have hs : ∀ y : Y, ∃ s : GlobalSections N.obj, y ∈ trivializationOpen N.obj s := by
    intro y
    obtain ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hy, -⟩ := (QuasiAffineSectionBasis.isBasis N).exists_subset_of_mem_open
      (Set.mem_univ y) isOpen_univ
    exact ⟨s, hy⟩
  choose s hs using hs
  have hsep : ∀ y y' : Y, ∃ a : Γ(Y, ⊤), ¬ y' ⤳ y →
      y ∈ Y.basicOpen a ∧ y' ∉ Y.basicOpen a := by
    intro y y'
    by_cases h : y' ⤳ y
    · exact ⟨1, fun h' ↦ (h' h).elim⟩
    · obtain ⟨a, ha⟩ := exists_basicOpen_separating h
      exact ⟨a, fun _ ↦ ha⟩
  choose sep hsep using hsep
  let e : Y → Γ(Y, ⊤) := fun y ↦ ∏ y' ∈ F.erase y, sep y y'
  have he_mem : ∀ y ∈ F, y ∈ Y.basicOpen (e y) := by
    intro y hy
    rw [Scheme.mem_basicOpen_top, map_prod]
    refine Finset.prod_induction _ IsUnit (fun _ _ ha hb ↦ ha.mul hb) isUnit_one ?_
    intro y' hy'
    have hne : y' ≠ y := Finset.ne_of_mem_erase hy'
    have hns : ¬ y' ⤳ y := fun h ↦ hne (hF y' (Finset.mem_of_mem_erase hy') y hy h)
    exact (Scheme.mem_basicOpen_top _ _ _).mp (hsep y y' hns).1
  have he_not : ∀ y ∈ F, ∀ y₀ ∈ F, y₀ ≠ y → y₀ ∉ Y.basicOpen (e y) := by
    intro y hy y₀ hy₀ hne hmem
    rw [Scheme.mem_basicOpen_top] at hmem
    have hns : ¬ y₀ ⤳ y := fun h ↦ hne (hF y₀ hy₀ y hy h)
    have hmem' : y₀ ∈ F.erase y := Finset.mem_erase.mpr ⟨hne, hy₀⟩
    change IsUnit ((Y.presheaf.germ ⊤ y₀ trivial).hom (∏ y' ∈ F.erase y, sep y y')) at hmem
    rw [← Finset.mul_prod_erase _ _ hmem', map_mul] at hmem
    exact (hsep y y₀ hns).2 ((Scheme.mem_basicOpen_top _ _ _).mpr (isUnit_of_mul_isUnit_left hmem))
  refine ⟨∑ y ∈ F, e y • s y, fun y₀ hy₀ ↦ ?_⟩
  let U := trivializationOpen N.obj (s y₀)
  have hq : TrivializesOn N.obj (s y₀) U := trivializesOn_trivializationOpen N.obj (s y₀)
  have hbij := (trivializesOn_iff_bijective N.obj (s y₀) U).mp hq U le_rfl
  let res : GlobalSections N.obj → Γ(N.obj, U) :=
    fun t ↦ N.obj.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op t
  have hc : ∀ y, ∃ c : Γ(Y, U), res (s y) = c • res (s y₀) := by
    intro y
    obtain ⟨c, hc⟩ := hbij.2 (res (s y))
    exact ⟨c, hc.symm.trans (sectionHom_app N.obj (s y₀) U c)⟩
  choose c hc using hc
  have hc₀ : c y₀ = 1 := by
    apply hbij.1
    exact (sectionHom_app N.obj (s y₀) U (c y₀)).trans
      ((hc y₀).symm.trans (((one_smul _ _).symm).trans
        (sectionHom_app N.obj (s y₀) U 1).symm))
  let resY : Γ(Y, ⊤) → Γ(Y, U) := fun a ↦ Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a
  let r : Γ(Y, U) := ∑ y ∈ F, resY (e y) * c y
  have hres : res (∑ y ∈ F, e y • s y) = r • res (s y₀) := by
    simp only [res, r, map_sum, Scheme.Modules.map_smul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    change resY (e y) • res (s y) = (resY (e y) * c y) • res (s y₀)
    rw [hc y, smul_smul]
  have heq := inf_trivializationOpen_eq_basicOpen_of_res_eq_smul N.obj (s y₀)
    (∑ y ∈ F, e y • s y) U hq r hres
  have hy₀U : y₀ ∈ U := hs y₀
  suffices hr : y₀ ∈ Y.basicOpen r by
    have : y₀ ∈ U ⊓ trivializationOpen N.obj (∑ y ∈ F, e y • s y) := heq ▸ hr
    exact this.2
  rw [Scheme.mem_basicOpen _ _ _ hy₀U]
  have hgerm : ∀ a : Γ(Y, ⊤), (Y.presheaf.germ U y₀ hy₀U).hom (resY a) =
      (Y.presheaf.germ ⊤ y₀ trivial).hom a := by
    intro a
    exact Y.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top)) y₀ hy₀U a
  change IsUnit ((Y.presheaf.germ U y₀ hy₀U).hom (∑ y ∈ F, resY (e y) * c y))
  rw [← Finset.add_sum_erase _ _ hy₀, map_add, map_mul, hc₀, map_one, mul_one, hgerm]
  apply isUnit_add_of_nonunits ((Scheme.mem_basicOpen_top _ _ _).mp (he_mem y₀ hy₀))
  rw [map_sum, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  refine Submodule.sum_mem _ fun y hy ↦ ?_
  rw [map_mul, hgerm]
  apply Ideal.mul_mem_right
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen_top]
  exact he_not y (Finset.mem_of_mem_erase hy) y₀ hy₀ (Finset.ne_of_mem_erase hy).symm

/-- For a finite morphism from an affine scheme, a line bundle has a global section generating
it on the inverse image of an open neighbourhood of any given point of the target. -/
theorem exists_nbhd_le_trivializationOpen [IsAffine Y] {T₀ : Scheme.{u}} (p : Y ⟶ T₀)
    [IsFinite p] (N : LineBundle Y) (t : T₀) :
    ∃ (W : T₀.Opens) (σ : GlobalSections N.obj),
      t ∈ W ∧ p ⁻¹ᵁ W ≤ trivializationOpen N.obj σ := by
  have hfin := p.finite_preimage_singleton t
  have hdisc := (p.isDiscrete_preimage_singleton t).to_subtype
  obtain ⟨σ, hσ⟩ := exists_section_mem_trivializationOpen N hfin.toFinset (by
    intro x hx y hy hxy
    rw [Set.Finite.mem_toFinset] at hx hy
    have h' : (⟨x, hx⟩ : ↥(p ⁻¹' {t})) ⤳ ⟨y, hy⟩ :=
      (Topology.IsInducing.subtypeVal.specializes_iff).mp hxy
    exact congrArg Subtype.val h'.eq)
  have hclosed : IsClosed (p '' (trivializationOpen N.obj σ : Set Y)ᶜ) :=
    p.isClosedMap _ (trivializationOpen N.obj σ).isOpen.isClosed_compl
  refine ⟨⟨(p '' (trivializationOpen N.obj σ : Set Y)ᶜ)ᶜ, hclosed.isOpen_compl⟩, σ, ?_, ?_⟩
  · rintro ⟨y, hyC, hyt⟩
    exact hyC (hσ y ((Set.Finite.mem_toFinset hfin).mpr hyt))
  · intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩

/-- A line bundle becomes trivial after pullback along any morphism landing in the
trivialization open of a global section. -/
theorem nonempty_pullback_iso_of_le_trivializationOpen {V : Scheme.{u}} (N : LineBundle Y)
    (σ : GlobalSections N.obj) (q : V ⟶ Y)
    (hq : Set.range q ⊆ (trivializationOpen N.obj σ : Set Y)) :
    Nonempty ((Scheme.Modules.pullback q).obj N.obj ≅
      SheafOfModules.unit V.ringCatSheaf) := by
  let U := trivializationOpen N.obj σ
  have hr : Set.range q ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact hq
  let q' : V ⟶ U.toScheme := IsOpenImmersion.lift U.ι q hr
  have hq' : q' ≫ U.ι = q := IsOpenImmersion.lift_fac U.ι q hr
  exact ⟨(Scheme.Modules.pullbackCongr hq').symm.app N.obj ≪≫
    ((Scheme.Modules.pullbackComp q' U.ι).app N.obj).symm ≪≫
    (Scheme.Modules.pullback q').mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N.obj).symm ≪≫
    (Scheme.Modules.pullback q').mapIso (trivializationOpenIso N.obj σ).symm ≪≫
    Langlands.Scheme.Modules.pullbackUnitIso q'⟩

end Langlands.AlgebraicGeometry.Picard.FinitePointsGeneratingSection
