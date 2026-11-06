import Langlands.Cohomology.SupercuspidalExtCharZero.Retraction
import Langlands.Cohomology.SupercuspidalExtCharZero.Statement
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Category.SmoothPartAdjunction

/-!
# Injectivity of irreducible representations with compact coefficients

Over a field of characteristic zero, an irreducible smooth representation `ρ` with
compactly supported matrix coefficients and finite-dimensional compact open fixed vectors
is an injective object of the category of smooth representations. Embed `ρ` into an
injective object `I`. With a bijective coefficient map `Ψ : V → V` at a compact open `U`,
the retraction lemma gives an intertwiner `r : I → V` restricting to `Ψ` on `V`; then
`Ψ⁻¹ ∘ r` exhibits `ρ` as a retract of `I`.
-/

noncomputable section

namespace Langlands.Cohomology.SupercuspidalExtCharZero

open CategoryTheory Function

universe u

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- An irreducible smooth representation with compactly supported matrix coefficients and
finite-dimensional fixed vectors under compact open subgroups is injective, over a field of
characteristic zero. -/
theorem injective_of_hasCompactCoefficients (ρ : SmoothRep.{u, u, u} k G)
    (hirr : ρ.IsIrreducible) (hc : HasCompactCoefficients ρ)
    (hadm : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      FiniteDimensional k (fixedVectors ρ.representation K.toSubgroup)) : Injective ρ := by
  have := hirr
  obtain ⟨U, hUc, ξ, hξ, w, hw, hbij⟩ :=
    exists_coefficientMap_bijective ρ.representation ρ.isSmooth hc
  set Ψ := Representation.IntertwiningMap.ofBijective _ hbij
  have hi : Injective (SmoothRep.hom (Injective.ι ρ)) :=
    (SmoothRep.mono_iff_injective _).1 inferInstance
  obtain ⟨r, hr⟩ := exists_intertwining_comp_eq_coefficientMap ρ.representation ρ.isSmooth
    hadm hc (Injective.under ρ).representation (Injective.under ρ).isSmooth
    (SmoothRep.hom (Injective.ι ρ)) hi U hUc ξ (mem_fixedVectors_dual_iff.1 hξ) w
    (mem_fixedVectors_iff.1 hw)
  refine Retract.injective (Y := Injective.under ρ)
    ⟨Injective.ι ρ, SmoothRep.ofHom (Ψ.symm.toIntertwiningMap.comp r), ?_⟩
  rw [← SmoothRep.ofHom_hom (_ ≫ _), ← SmoothRep.ofHom_hom (𝟙 ρ)]
  congr 1
  ext v
  simp only [SmoothRep.hom_comp, SmoothRep.hom_ofHom, SmoothRep.hom_id,
    Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.comp_apply,
    Representation.IntertwiningMap.id_apply, Representation.Equiv.coe_toIntertwiningMap, hr]
  exact Ψ.toLinearEquiv.symm_apply_apply v

end Langlands.Cohomology.SupercuspidalExtCharZero
