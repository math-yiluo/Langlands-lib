import Langlands.Geometry.Building.MaximalUnramifiedApartmentInjective
import Langlands.Geometry.Building.RootCharacterValuationKernel
import Langlands.Geometry.Building.BoundedRootFixerFiltration

/-! # Actual root groups intersected with full building fixers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- A root point fixing an apartment point in the reduced building has
nonnegative valuation. No additional apartment axiom is required. -/
theorem mem_filtration_of_mem_rootGroup_of_fixing_apartmentMap
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a)
    (hfix : g • D.apartmentMap x = D.apartmentMap x) :
    g ∈ D.filtration x a 0 := by
  have : Smooth G.X.hom := hG.smooth
  have hS := hi.isSplitSubtorus.1
  have hrank := rootRankOneFactorization k G hG S i hi
  by_cases hg1 : g = 1
  · simpa only [hg1] using (D.filtration x a 0).one_mem
  obtain ⟨t, ht⟩ := exists_val_eq_coe x ha hg hg1
  have ht0 : 0 ≤ t := by
    by_contra hnegative
    have htneg : t < 0 := lt_of_not_ge hnegative
    obtain ⟨p, hp⟩ := ((hrank a ha g hg hg1).1).exists
    have hflip := hp.weylAction_eq_neg i hS ha.1 hg hg1
    have hnega : -a ∈ relativeRoots i := by
      rw [← hflip]
      exact weylAction_mapsTo_relativeRoots i _ ha
    have hp1val := x.isValuation.opposite a ha g hg hg1
      p.1 hp.1 p.2 hp.2.1 hp.2.2
    rw [ht] at hp1val
    have hp1t := withTop_eq_neg_of_add_eq_zero hp1val
    have hp2val := x.isValuation.opposite_snd ha hg hg1 hp.1 hp.2.1 hp.2.2
    rw [ht] at hp2val
    have hp2t := withTop_eq_neg_of_add_eq_zero hp2val
    have hp1F : p.1 ∈ D.filtration x (-a) 0 :=
      ⟨hp.1, by rw [hp1t]; exact WithTop.coe_le_coe.mpr (by linarith)⟩
    have hp2F : p.2 ∈ D.filtration x (-a) 0 :=
      ⟨hp.2.1, by rw [hp2t]; exact WithTop.coe_le_coe.mpr (by linarith)⟩
    have hFF : D.filtration x (-a) 0 ≤ D.reducedFixer (D.apartmentMap x) :=
      (D.filtration_le_sharpFixer x hnega).trans (D.sharpFixer_le_reducedFixer x)
    let m : normalizerPoints i := ⟨p.1 * g * p.2, hp.2.2⟩
    have hmF : (m : rationalPoints G) ∈ D.reducedFixer (D.apartmentMap x) :=
      (D.reducedFixer (D.apartmentMap x)).mul_mem
        ((D.reducedFixer (D.apartmentMap x)).mul_mem (hFF hp1F)
          (D.mem_reducedFixer.mpr hfix)) (hFF hp2F)
    have hmx : m • x = x := by
      apply D.apartmentMap_injective hG hi
      rw [D.apartmentMap_smul]
      exact D.mem_reducedFixer.mp hmF
    have hw : m • x.val = (0 : V S) +ᵥ x.val := by
      simpa only [val_smul, zero_vadd] using
        congrArg (fun y : D.Apartment => y.val) hmx
    have heval := eval_translation_eq_of_factor
      x ha hnega hg hg1 hp.1 hp.2.1 hp.2.2 hflip ht hw
    rw [map_zero] at heval
    linarith
  exact ⟨hg, by rw [ht]; exact WithTop.coe_le_coe.mpr ht0⟩

/-- The actual root group meets the full apartment-point stabilizer in its
depth-zero filtration, over any field and without extra apartment axioms. -/
theorem rootGroupPoints_inf_reducedFixer_eq_filtration
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    rootGroupPoints i a ⊓ D.reducedFixer (D.apartmentMap x) = D.filtration x a 0 := by
  apply le_antisymm
  · intro g hg
    exact D.mem_filtration_of_mem_rootGroup_of_fixing_apartmentMap hG hi x ha hg.1
      (D.mem_reducedFixer.mp hg.2)
  · exact le_inf (D.filtration_le_rootGroupPoints x a 0)
      ((D.filtration_le_sharpFixer x ha).trans (D.sharpFixer_le_reducedFixer x))

/-- For every apartment subset, including the empty subset, the actual
root-group intersection with its full pointwise fixer is its root fixer. -/
theorem rootGroupPoints_inf_pointwiseFixer_eq_rootFixer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (a : relativeRoots i) (Ω : Set D.Apartment) :
    rootGroupPoints i a ⊓ D.pointwiseFixer (D.apartmentMap '' Ω) =
      D.rootFixer a Ω := by
  apply le_antisymm
  · intro g hg
    refine D.mem_rootFixer.mpr ⟨hg.1, fun x hx => ?_⟩
    exact D.mem_filtration_of_mem_rootGroup_of_fixing_apartmentMap hG hi x a.2 hg.1
      (D.mem_pointwiseFixer.mp hg.2 _ ⟨x, hx, rfl⟩)
  · intro g hg
    obtain ⟨hgRoot, hgΩ⟩ := D.mem_rootFixer.mp hg
    refine ⟨hgRoot, D.mem_pointwiseFixer.mpr ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact D.mem_reducedFixer.mp ((D.sharpFixer_le_reducedFixer x)
      ((D.filtration_le_sharpFixer x a.2) (hgΩ x hx)))

/-- The character-valuation condition of a one-fixer is automatic on root
points. Thus its root-group intersection is the same actual root fixer. -/
theorem rootGroupPoints_inf_oneFixer_eq_rootFixer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation k Γ₀)
    (a : relativeRoots i) (Ω : Set D.Apartment) :
    rootGroupPoints i a ⊓
        (characterValuationKernel v G ⊓ D.pointwiseFixer (D.apartmentMap '' Ω)) =
      D.rootFixer a Ω := by
  rw [rootGroupPoints_inf_characterValuationKernel_inf hi.isSplitSubtorus.1 i a a.2.1 v]
  exact D.rootGroupPoints_inf_pointwiseFixer_eq_rootFixer hG hi a Ω

/-- On a nonempty affinely bounded apartment subset, the root-group
intersection with its one-fixer is exactly one specified filtration level. -/
theorem rootGroupPoints_inf_oneFixer_eq_filtration_of_bounded
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation k Γ₀)
    (a : relativeRoots i) (x : D.Apartment) {Ω : Set D.Apartment}
    (hne : Ω.Nonempty) (hb : ∀ f : D.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    rootGroupPoints i a ⊓
        (characterValuationKernel v G ⊓ D.pointwiseFixer (D.apartmentMap '' Ω)) =
      D.filtration x a (D.rootFixerDepth a x Ω) := by
  rw [D.rootGroupPoints_inf_oneFixer_eq_rootFixer hG hi v a Ω]
  exact D.rootFixer_eq_filtration_of_bounded a x hne hb

end Langlands.Geometry.Building.KPApartmentData
