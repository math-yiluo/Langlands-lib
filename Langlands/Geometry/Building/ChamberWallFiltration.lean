import Langlands.Geometry.Building.AffineChamberWallComparisonProof
import Langlands.Geometry.Building.ChamberFiltration

/-! # Root filtrations away from a chamber wall -/

noncomputable section

universe u uV uA

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V : Type uV} {A : Type uA}
    [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- A chamber-simple reflection preserves the sign of a root whose
derivative is not proportional to its own derivative. -/
theorem sign_eq_simpleReflection_of_linear_not_proportional
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {C : Set A} (hC : IsChamber Ψ C)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ simpleAffineRoots Ψ C)
    {v : V} (hv : IsCoroot Ψ ψ v)
    {x : A} (hx : x ∈ C)
    {eta : A →ᵃ[ℝ] ℝ} (hη : eta ∈ Ψ)
    (hnot : ¬∃ c : ℝ, eta.linear = c • ψ.linear) :
    SignType.sign (eta x) =
      SignType.sign (eta (affineReflection ψ hv.1 x)) := by
  obtain ⟨z, hz, hzC⟩ := hC
  have hzx : x ∈ facet Ψ z := hzC.symm ▸ hx
  have hxC : facet Ψ x = C := (facet_eq_of_mem hzx).trans hzC
  have hxreg : ∀ ξ ∈ Ψ, ξ x ≠ 0 := by
    intro ξ hξ hzero
    have hs := hzx ξ hξ
    rw [hzero, sign_zero, sign_eq_zero_iff] at hs
    exact hz ξ hξ hs
  let s : affineWeylGroup Ψ :=
    ⟨affineReflection ψ hv.1, affineReflection_mem_affineWeylGroup hψ.1.1 hv⟩
  have hs : (s : A ≃ᵃ[ℝ] A) ∈ wallReflections Ψ x :=
    chamberSimple_mem_wallReflections hΨ ⟨ψ, hxC.symm ▸ hψ, v, hv, rfl⟩
  have hηrx : eta (affineReflection ψ hv.1 x) ≠ 0 := by
    have hcomp : eta.comp (affineReflection ψ hv.1 : A →ᵃ[ℝ] A) ∈ Ψ := by
      rw [comp_affineReflection]
      exact hv.2 eta hη
    exact hxreg _ hcomp
  have hnsep : ¬eta x * eta (affineReflection ψ hv.1 x) < 0 := by
    intro hsep
    obtain ⟨w, hw⟩ := hΨ.exists_isCoroot eta hη
    have heq : affineReflection eta hw.1 = affineReflection ψ hv.1 :=
      hs.2 _ ⟨eta, hη, w, hw, rfl, hsep⟩
    have heta := eq_smul_of_hyperplane_le hv.1
      (hyperplane_le_of_affineReflection_eq hv.1 hw.1 heq)
    exact hnot ⟨eta.linear v / 2, by
      simpa only [AffineMap.smul_linear] using congrArg AffineMap.linear heta⟩
  exact sign_eq_of_mul_pos (lt_of_le_of_ne (le_of_not_gt hnsep)
    (mul_ne_zero (hxreg eta hη) hηrx).symm)

end AffineRootSystem

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

variable
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
      eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)
    {C : Set D.Apartment} (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots ψ v)
    {a : relativeRoots i}
    (hnot : ¬∃ c : ℝ, rootForm i a = c • ψ.linear)

include hsys hAS4 hC hψ hnot

/-- AS4 extends the off-wall sign comparison to every valuation jump. -/
theorem sign_eq_extendedAffineRoot_simpleReflection_of_not_proportional
    {x : D.Apartment} (hx : x ∈ C)
    {eta : D.Apartment →ᵃ[ℝ] ℝ} (hη : eta ∈ D.extendedAffineRoots)
    (hlin : eta.linear = rootForm i a) :
    SignType.sign (eta x) =
      SignType.sign (eta (AffineRootSystem.affineReflection ψ hv.1 x)) := by
  obtain ⟨ξ, hξ, c, hc, hξeq⟩ :
      ∃ ξ ∈ D.affineRoots, ∃ c : ℝ, 0 < c ∧ ξ = c • eta := by
    rcases hAS4 eta hη with h | h
    · exact ⟨eta, h, 1, by norm_num, (one_smul ℝ eta).symm⟩
    · exact ⟨(2 : ℝ) • eta, h, 2, by norm_num, rfl⟩
  have hξlin : ξ.linear = c • rootForm i a := by
    rw [hξeq, AffineMap.smul_linear, hlin]
  have hξnot : ¬∃ d : ℝ, ξ.linear = d • ψ.linear := by
    rintro ⟨d, hd⟩
    apply hnot
    refine ⟨c⁻¹ * d, ?_⟩
    calc
      rootForm i a = c⁻¹ • (c • rootForm i a) := by
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
      _ = (c⁻¹ * d) • ψ.linear := by rw [← hξlin, hd, smul_smul]
  have hs := AffineRootSystem.sign_eq_simpleReflection_of_linear_not_proportional
    hsys hC hψ hv hx hξ hξnot
  simpa only [hξeq, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul,
    sign_mul, sign_pos hc, one_mul] using hs

/-- Both depth-zero filtrations are unchanged across a chamber-simple
reflection away from the proportional root direction. -/
theorem filtration_eq_simpleReflection_of_not_proportional
    {x : D.Apartment} (hx : x ∈ C) :
    D.filtration x a 0 =
        D.filtration (AffineRootSystem.affineReflection ψ hv.1 x) a 0 ∧
      D.filtrationPlus x a 0 =
        D.filtrationPlus (AffineRootSystem.affineReflection ψ hv.1 x) a 0 := by
  have hmem (g : rationalPoints G) (hg : g ∈ rootGroupPoints i a) :
      ((0 : WithTop ℝ) ≤ x.val a g ↔
        0 ≤ (AffineRootSystem.affineReflection ψ hv.1 x).val a g) ∧
      ((0 : WithTop ℝ) < x.val a g ↔
        0 < (AffineRootSystem.affineReflection ψ hv.1 x).val a g) := by
    by_cases hg1 : g = 1
    · subst g
      rw [(x.isValuation.eq_top_iff a a.property 1 hg).2 rfl,
        ((AffineRootSystem.affineReflection ψ hv.1 x).isValuation.eq_top_iff
          a a.property 1 hg).2 rfl]
      exact ⟨Iff.rfl, Iff.rfl⟩
    · obtain ⟨eta, hη, hlin, hval⟩ :=
        D.exists_extendedAffineRoot_of_ne_one x a.property hg hg1
      have hs := D.sign_eq_extendedAffineRoot_simpleReflection_of_not_proportional
        hsys hAS4 hC hψ hv hnot hx hη hlin
      rw [hval x, hval (AffineRootSystem.affineReflection ψ hv.1 x)]
      constructor
      · rw [← WithTop.coe_zero, WithTop.coe_le_coe, WithTop.coe_le_coe]
        simpa only [sign_nonneg_iff] using
          (congrArg (fun s : SignType => 0 ≤ s) hs).to_iff
      · rw [← WithTop.coe_zero, WithTop.coe_lt_coe, WithTop.coe_lt_coe]
        simpa only [sign_eq_one_iff] using
          (congrArg (fun s : SignType => s = 1) hs).to_iff
  constructor
  · ext g
    simp only [mem_filtration]
    exact and_congr_right fun hg => (hmem g hg).1
  · ext g
    simp only [mem_filtrationPlus]
    exact and_congr_right fun hg => (hmem g hg).2

/-- The actual root fixers at both zero depths agree on adjacent chambers
for every direction not proportional to the reflected wall. -/
theorem rootFixer_eq_simpleReflection_of_not_proportional :
    D.rootFixer a C =
        D.rootFixer a (AffineRootSystem.affineReflection ψ hv.1 '' C) ∧
      D.rootFixerPlus a C =
        D.rootFixerPlus a (AffineRootSystem.affineReflection ψ hv.1 '' C) := by
  have hmem (g : rationalPoints G) :
      (∀ x ∈ C, g ∈ D.filtration x a 0) ↔
        ∀ y ∈ AffineRootSystem.affineReflection ψ hv.1 '' C,
          g ∈ D.filtration y a 0 := by
    constructor
    · rintro hg y ⟨x, hx, rfl⟩
      rw [← (D.filtration_eq_simpleReflection_of_not_proportional
        hsys hAS4 hC hψ hv hnot hx).1]
      exact hg x hx
    · intro hg x hx
      rw [(D.filtration_eq_simpleReflection_of_not_proportional
        hsys hAS4 hC hψ hv hnot hx).1]
      exact hg _ ⟨x, hx, rfl⟩
  have hmemPlus (g : rationalPoints G) :
      (∀ x ∈ C, g ∈ D.filtrationPlus x a 0) ↔
        ∀ y ∈ AffineRootSystem.affineReflection ψ hv.1 '' C,
          g ∈ D.filtrationPlus y a 0 := by
    constructor
    · rintro hg y ⟨x, hx, rfl⟩
      rw [← (D.filtration_eq_simpleReflection_of_not_proportional
        hsys hAS4 hC hψ hv hnot hx).2]
      exact hg x hx
    · intro hg x hx
      rw [(D.filtration_eq_simpleReflection_of_not_proportional
        hsys hAS4 hC hψ hv hnot hx).2]
      exact hg _ ⟨x, hx, rfl⟩
  constructor
  · ext g
    simp only [mem_rootFixer]
    exact and_congr_right fun _ => hmem g
  · ext g
    simp only [mem_rootFixerPlus_iff_forall_mem]
    exact and_congr_right fun _ => hmemPlus g

/-- The off-wall root-fixer comparison preserves the ambient rational point. -/
def rootFixerEquivSimpleReflection_of_not_proportional :
    D.rootFixer a C ≃*
      D.rootFixer a (AffineRootSystem.affineReflection ψ hv.1 '' C) :=
  MulEquiv.subgroupCongr
    (D.rootFixer_eq_simpleReflection_of_not_proportional
      hsys hAS4 hC hψ hv hnot).1

/-- The positive-depth-zero comparison also preserves the ambient point. -/
def rootFixerPlusEquivSimpleReflection_of_not_proportional :
    D.rootFixerPlus a C ≃*
      D.rootFixerPlus a (AffineRootSystem.affineReflection ψ hv.1 '' C) :=
  MulEquiv.subgroupCongr
    (D.rootFixer_eq_simpleReflection_of_not_proportional
      hsys hAS4 hC hψ hv hnot).2

@[simp]
theorem coe_rootFixerEquivSimpleReflection_of_not_proportional
    (g : D.rootFixer a C) :
    ((D.rootFixerEquivSimpleReflection_of_not_proportional
      hsys hAS4 hC hψ hv hnot g) : rationalPoints G) = g :=
  MulEquiv.subgroupCongr_apply _ _

@[simp]
theorem coe_rootFixerPlusEquivSimpleReflection_of_not_proportional
    (g : D.rootFixerPlus a C) :
    ((D.rootFixerPlusEquivSimpleReflection_of_not_proportional
      hsys hAS4 hC hψ hv hnot g) : rationalPoints G) = g :=
  MulEquiv.subgroupCongr_apply _ _

end KPApartmentData

end Langlands.Geometry.Building
