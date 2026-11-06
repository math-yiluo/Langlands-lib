import Langlands.Cohomology.SupercuspidalExtCharZero.CoefficientMap
import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Category.Abelian

/-!
# Projective lifting with compact smooth-dual coefficients

The coefficient-map construction gives projectivity for irreducible smooth
complex representations, with independent group and carrier universes.
-/

noncomputable section

namespace Langlands.CompactCoefficient

open CategoryTheory
open Langlands.Compact.CharZero
open Langlands.Cohomology.SupercuspidalExtCharZero

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- An irreducible smooth complex representation with compact smooth-dual
coefficients is projective, with no relation between the group and carrier
universes. -/
theorem projective_of_hasCompactSmoothDualCoefficients
    (ρ : SmoothRep.{0, uG, uV} ℂ G)
    (hirr : ρ.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients ρ.representation) : Projective ρ := by
  have := hirr
  obtain ⟨U, hUc, ξ, hξ, w, hw, hbij⟩ :=
    exists_coefficientMap_bijective ρ.representation ρ.isSmooth hc
  have hξ' := mem_fixedVectors_dual_iff.1 hξ
  have hc' : ∀ v, HasCompactSupport fun g => ξ (ρ.representation g v) :=
    fun v => hc v ξ ⟨U, hξ⟩
  set Ψ := Representation.IntertwiningMap.ofBijective _ hbij
  refine ⟨fun {E X} f e he => ?_⟩
  obtain ⟨y₀, hy₀⟩ := (SmoothRep.epi_iff_surjective e).1 he (SmoothRep.hom f w)
  set y := averageMap E.representation E.isSmooth U hUc y₀ with hydef
  have hy : ∀ u ∈ U.toSubgroup, E.representation u y = y :=
    Cohomology.SupercuspidalExtCharZero.mem_fixedVectors_iff.1
      (averageMap_mem_fixedVectors _ _ U hUc y₀)
  have hey : SmoothRep.hom e y = SmoothRep.hom f w := by
    have h1 := LinearMap.congr_fun (averageMap_commute E.representation X.representation
      E.isSmooth X.isSmooth U hUc (SmoothRep.hom e)) y₀
    simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply] at h1
    rw [hydef, h1, hy₀]
    refine averageMap_id _ _ U hUc _
      (Cohomology.SupercuspidalExtCharZero.mem_fixedVectors_iff.2 fun u hu => ?_)
    rw [← Representation.IntertwiningMap.isIntertwining,
      Cohomology.SupercuspidalExtCharZero.mem_fixedVectors_iff.1 hw u hu]
  refine ⟨SmoothRep.ofHom ((coefficientIntertwiningMap (σ := E.representation) U.isOpen hξ'
    hc' hy).comp Ψ.symm.toIntertwiningMap), ?_⟩
  rw [← SmoothRep.ofHom_hom (_ ≫ e), ← SmoothRep.ofHom_hom f]
  congr 1
  ext v
  have hv : coefficientMap ρ.representation ρ.representation U ξ w (Ψ.symm v) = v :=
    Ψ.toLinearEquiv.apply_symm_apply v
  simp only [SmoothRep.hom_comp, SmoothRep.hom_ofHom, Representation.IntertwiningMap.comp_apply,
    Representation.Equiv.coe_toIntertwiningMap, Representation.IntertwiningMap.toLinearMap_apply,
    coefficientIntertwiningMap_apply]
  rw [map_coefficientMap_intertwining _ U.isOpen hc', hey,
    ← map_coefficientMap_intertwining _ U.isOpen hc', hv]

/-- A chosen lift of a morphism out of an irreducible compact-coefficient
representation along an epimorphism of smooth representations. -/
def projectiveLift (ρ : SmoothRep.{0, uG, uV} ℂ G)
    (hirr : ρ.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients ρ.representation)
    {E X : SmoothRep.{0, uG, uV} ℂ G} (f : ρ ⟶ X) (e : E ⟶ X) [Epi e] : ρ ⟶ E :=
  letI := projective_of_hasCompactSmoothDualCoefficients ρ hirr hc
  Projective.factorThru f e

/-- The chosen lift has the required composite. -/
@[simp]
theorem projectiveLift_comp (ρ : SmoothRep.{0, uG, uV} ℂ G)
    (hirr : ρ.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients ρ.representation)
    {E X : SmoothRep.{0, uG, uV} ℂ G} (f : ρ ⟶ X) (e : E ⟶ X) [Epi e] :
    projectiveLift ρ hirr hc f e ≫ e = f := by
  have := projective_of_hasCompactSmoothDualCoefficients ρ hirr hc
  exact Projective.factorThru_comp f e

end Langlands.CompactCoefficient
