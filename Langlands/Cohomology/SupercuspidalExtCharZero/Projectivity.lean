import Langlands.Cohomology.SupercuspidalExtCharZero.CoefficientMap
import Langlands.Cohomology.SupercuspidalExtCharZero.Statement
import Langlands.Representation.Category.Abelian

/-!
# Projectivity of irreducible representations with compact coefficients

Over a field of characteristic zero, an irreducible smooth representation `ρ` with
compactly supported matrix coefficients is a projective object of the category of
smooth representations. A bijective coefficient map `Ψ : V → V` at a compact open `U`
and a `U`-fixed `w` exists. To lift `f : ρ → X` along an epimorphism `e : E → X`, choose
a preimage of `f w`, average it over `U` to a `U`-fixed `y` with `e y = f w`, and take
the coefficient map of `(E, y)` composed with `Ψ⁻¹`.
-/

noncomputable section

namespace Langlands.Cohomology.SupercuspidalExtCharZero

open CategoryTheory Function
open Langlands.Compact.CharZero

universe u

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- An irreducible smooth representation with compactly supported matrix coefficients over
a field of characteristic zero is projective. -/
theorem projective_of_hasCompactCoefficients (ρ : SmoothRep.{u, u, u} k G)
    (hirr : ρ.IsIrreducible) (hc : HasCompactCoefficients ρ) : Projective ρ := by
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
    mem_fixedVectors_iff.1 (averageMap_mem_fixedVectors _ _ U hUc y₀)
  have hey : SmoothRep.hom e y = SmoothRep.hom f w := by
    have h1 := LinearMap.congr_fun (averageMap_commute E.representation X.representation
      E.isSmooth X.isSmooth U hUc (SmoothRep.hom e)) y₀
    simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply] at h1
    rw [hydef, h1, hy₀]
    refine averageMap_id _ _ U hUc _ (mem_fixedVectors_iff.2 fun u hu => ?_)
    rw [← Representation.IntertwiningMap.isIntertwining, mem_fixedVectors_iff.1 hw u hu]
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

end Langlands.Cohomology.SupercuspidalExtCharZero
