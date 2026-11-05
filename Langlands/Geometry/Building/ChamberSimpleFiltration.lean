import Langlands.Geometry.Building.SimpleReflectionPositivity
import Langlands.Geometry.Building.ChamberFiltration
import Langlands.Geometry.Building.AffineChamberFreeness

/-! # Root filtrations across a chamber-simple wall -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)
  (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
    eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)
  {C : Set D.Apartment} {ψ : D.Apartment →ᵃ[ℝ] ℝ}
  {v : TranslationSpace i}

include hAS4

/-- AS 4 extends the wall sign comparison to the extended affine roots. -/
theorem sign_reflection_eq_of_extendedAffineRoot
    (hψ : ψ ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    (hv : AffineRootSystem.IsCoroot D.affineRoots ψ v)
    {eta : D.Apartment →ᵃ[ℝ] ℝ} (heta : eta ∈ D.extendedAffineRoots)
    (hetaψ : ¬ ∃ c : ℝ, eta = c • ψ) {x : D.Apartment} (hx : x ∈ C) :
    SignType.sign (eta (AffineRootSystem.affineReflection ψ hv.1 x)) =
      SignType.sign (eta x) := by
  rcases hAS4 eta heta with h | h
  · exact AffineRootSystem.sign_reflection_eq_of_mem_simpleAffineRoots hψ hv h hetaψ hx
  · have hnot : ¬ ∃ c : ℝ, (2 : ℝ) • eta = c • ψ := by
      rintro ⟨c, hc⟩
      apply hetaψ
      refine ⟨c / 2, ?_⟩
      ext z
      have hz := congrArg (fun f : D.Apartment →ᵃ[ℝ] ℝ => f z) hc
      change (2 : ℝ) * eta z = c * ψ z at hz
      change eta z = (c / 2) * ψ z
      linarith
    have hs :=
      AffineRootSystem.sign_reflection_eq_of_mem_simpleAffineRoots hψ hv h hnot hx
    change SignType.sign ((2 : ℝ) * eta (AffineRootSystem.affineReflection ψ hv.1 x)) =
      SignType.sign ((2 : ℝ) * eta x) at hs
    simpa only [sign_mul, sign_pos (by norm_num : (0 : ℝ) < 2), one_mul] using hs

/-- A root fixer outside the positive derivative ray of the wall root
is contained in the root fixer of the reflected chamber. -/
theorem rootFixer_le_reflected_of_not_pos_multiple
    (hC : AffineRootSystem.IsChamber D.affineRoots C)
    (hψ : ψ ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    (hv : AffineRootSystem.IsCoroot D.affineRoots ψ v)
    {a : relativeRoots i}
    (haψ : ¬ ∃ c : ℝ, 0 < c ∧ rootForm i a = c • ψ.linear) :
    D.rootFixer a C ≤
      D.rootFixer a (AffineRootSystem.affineReflection ψ hv.1 '' C) := by
  intro u hu
  by_cases hu1 : u = 1
  · subst u
    exact Subgroup.one_mem _
  · obtain ⟨x₀, hx₀⟩ : C.Nonempty := hC.nonempty
    have huRoot := (D.mem_rootFixer.1 hu).1
    obtain ⟨eta, heta, hlin, hval⟩ :=
      D.exists_extendedAffineRoot_of_ne_one x₀ a.property huRoot hu1
    have hpos (x : D.Apartment) (hx : x ∈ C) : 0 < eta x := by
      have hge : 0 ≤ eta x := by
        simpa only [hval x, WithTop.coe_le_coe] using ((D.mem_rootFixer.1 hu).2 x hx).2
      exact lt_of_le_of_ne hge
        (D.extendedAffineRoot_ne_zero_of_mem_chamber hAS4 hC hx heta).symm
    have hnot : ¬ ∃ c : ℝ, eta = c • ψ := by
      rintro ⟨c, hc⟩
      have heval := congrArg (fun f : D.Apartment →ᵃ[ℝ] ℝ => f x₀) hc
      change eta x₀ = c * ψ x₀ at heval
      have hcpos : 0 < c := by
        have := hpos x₀ hx₀
        have := hψ.1.2 x₀ hx₀
        nlinarith
      apply haψ
      refine ⟨c, hcpos, ?_⟩
      simpa only [AffineMap.smul_linear, hlin] using congrArg AffineMap.linear hc
    refine D.mem_rootFixer.2 ⟨huRoot, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hetapos : 0 < eta (AffineRootSystem.affineReflection ψ hv.1 x) := by
      rw [← sign_eq_one_iff,
        D.sign_reflection_eq_of_extendedAffineRoot hAS4 hψ hv heta hnot hx]
      exact sign_pos (hpos x hx)
    exact mem_filtration.2
      ⟨huRoot, by simpa only [hval _, WithTop.coe_le_coe] using hetapos.le⟩

/-- The root fixer on a simple wall ray is precisely the filtration at
the corresponding scalar multiple of the wall root. -/
theorem rootFixer_eq_affineRootGroup_of_pos_multiple
    (hC : AffineRootSystem.IsChamber D.affineRoots C)
    (hψ : ψ ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    (hv : AffineRootSystem.IsCoroot D.affineRoots ψ v)
    {a : relativeRoots i} {c : ℝ} (hc : 0 < c)
    (hlin : (c • ψ).linear = rootForm i a) :
    D.rootFixer a C = D.affineRootGroup a (c • ψ) := by
  obtain ⟨y, hy, hcl, _⟩ :=
    AffineRootSystem.exists_wall_point_of_mem_simpleAffineRoots hψ hv
  obtain ⟨x, hx⟩ : C.Nonempty := hC.nonempty
  apply le_antisymm
  · intro u hu
    have hyu := (D.filtration_comparison_of_mem_facetClosure hAS4 (hcl x hx) a.property).2
      ((D.mem_rootFixer.1 hu).2 x hx)
    apply (mem_affineRootGroup_iff hlin y).2
    simpa only [mem_filtration, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul, hy, mul_zero, WithTop.coe_zero]
      using hyu
  · intro u hu
    have huRoot := D.affineRootGroup_le_rootGroupPoints a (c • ψ) hu
    refine D.mem_rootFixer.2 ⟨huRoot, fun z hz => mem_filtration.2 ⟨huRoot, ?_⟩⟩
    have hge := ((mem_affineRootGroup_iff hlin z).1 hu).2
    have hpos : 0 ≤ (c • ψ) z := mul_nonneg hc.le (hψ.1.2 z hz).le
    exact (WithTop.coe_le_coe.2 hpos).trans hge

/-- Positive depth above a multiple of a simple wall already fixes the
reflected chamber. This includes the half-wall filtration in the doubled-root case. -/
theorem affineRootGroupPlus_le_reflected_rootFixer_of_pos_multiple
    (hC : AffineRootSystem.IsChamber D.affineRoots C)
    (hψ : ψ ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    (hv : AffineRootSystem.IsCoroot D.affineRoots ψ v)
    {a : relativeRoots i} {c : ℝ} (hc : 0 < c)
    (hlin : (c • ψ).linear = rootForm i a) :
    D.affineRootGroupPlus a (c • ψ) ≤
      D.rootFixer a (AffineRootSystem.affineReflection ψ hv.1 '' C) := by
  obtain ⟨y, hy, _, _⟩ :=
    AffineRootSystem.exists_wall_point_of_mem_simpleAffineRoots hψ hv
  intro u hu
  by_cases hu1 : u = 1
  · subst u
    exact Subgroup.one_mem _
  · obtain ⟨x₀, hx₀⟩ : C.Nonempty := hC.nonempty
    have huRoot := ((mem_affineRootGroupPlus_iff hlin x₀).1 hu).1
    obtain ⟨eta, heta, _, hval⟩ :=
      D.exists_extendedAffineRoot_of_ne_one x₀ a.property huRoot hu1
    have hnot : ¬ ∃ d : ℝ, eta = d • ψ := by
      rintro ⟨d, hd⟩
      have hgt := ((mem_affineRootGroupPlus_iff hlin y).1 hu).2
      have hetay : eta y = 0 := by simp [hd, hy]
      exact (lt_irrefl ((0 : ℝ) : WithTop ℝ))
        (by simpa only [hval y, hetay, AffineMap.coe_smul, Pi.smul_apply,
          smul_eq_mul, hy, mul_zero] using hgt)
    refine D.mem_rootFixer.2 ⟨huRoot, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hpos : 0 < eta x := by
      have hgt := ((mem_affineRootGroupPlus_iff hlin x).1 hu).2
      have hgt' : (c • ψ) x < eta x := by
        simpa only [hval x, WithTop.coe_lt_coe] using hgt
      exact (mul_pos hc (hψ.1.2 x hx)).trans hgt'
    have hetapos : 0 < eta (AffineRootSystem.affineReflection ψ hv.1 x) := by
      rw [← sign_eq_one_iff,
        D.sign_reflection_eq_of_extendedAffineRoot hAS4 hψ hv heta hnot hx]
      exact sign_pos hpos
    exact mem_filtration.2
      ⟨huRoot, by simpa only [hval _, WithTop.coe_le_coe] using hetapos.le⟩

/-- The three root-filtration comparisons used at a chamber-simple wall. -/
def ChamberSimpleFiltrationStatement : Prop :=
  (∀ eta ∈ D.extendedAffineRoots,
    eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots) →
  ∀ (C : Set D.Apartment), AffineRootSystem.IsChamber D.affineRoots C →
    ∀ ψ ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C,
      ∀ (v : TranslationSpace i) (hv : AffineRootSystem.IsCoroot D.affineRoots ψ v),
        (∀ a : relativeRoots i,
          (¬ ∃ c : ℝ, 0 < c ∧ rootForm i a = c • ψ.linear) →
          D.rootFixer a C ≤
            D.rootFixer a (AffineRootSystem.affineReflection ψ hv.1 '' C)) ∧
        (∀ (a : relativeRoots i) (c : ℝ), 0 < c →
          (c • ψ).linear = rootForm i a →
          D.rootFixer a C = D.affineRootGroup a (c • ψ) ∧
            D.affineRootGroupPlus a (c • ψ) ≤
              D.rootFixer a (AffineRootSystem.affineReflection ψ hv.1 '' C))

omit hAS4 in
/-- AS 4 and the simple-wall geometry imply the three comparisons. -/
theorem chamberSimpleFiltration : D.ChamberSimpleFiltrationStatement := by
  intro hAS4 C hC ψ hψ v hv
  exact ⟨fun _ haψ =>
    D.rootFixer_le_reflected_of_not_pos_multiple hAS4 hC hψ hv haψ,
    fun _ _ hc hlin =>
      ⟨D.rootFixer_eq_affineRootGroup_of_pos_multiple hAS4 hC hψ hv hc hlin,
        D.affineRootGroupPlus_le_reflected_rootFixer_of_pos_multiple
          hAS4 hC hψ hv hc hlin⟩⟩

end Langlands.Geometry.Building.KPApartmentData
