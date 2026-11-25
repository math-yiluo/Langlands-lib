import Langlands.Cohomology.Profinite.Cochains

/-!
# Cohomology in low degree

`zeroIso A : cohomology A 0 ≅ A^G`: a locally constant `0`-cochain is a vector of `A`, and it is
a cocycle exactly when it is fixed by `G`. The identification goes through the exact sequence
`0 → A^G → C⁰ → C¹` (`shortComplexH0`).
-/

namespace Langlands.ProfiniteCohomology

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section H0


variable (A : Rep.{u} k G) [IsSmoothRep A]

noncomputable def invariantsToCochains₀ :
    A.ρ.invariants →ₗ[k] locallyConstantCochains A 0 where
  toFun v := ⟨fun _ => v.1, IsLocallyConstant.const _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def shortComplexH0 : ShortComplex (ModuleCat k) :=
  ShortComplex.mk (ModuleCat.ofHom (invariantsToCochains₀ A)) (dLocallyConstant A 0) (by
    ext v : 2
    apply Subtype.ext
    funext g
    change (inhomogeneousCochains.d A 0).hom (fun _ => v.1) g = 0
    simp [inhomogeneousCochains.d_hom_apply, v.2 (g 0)])

instance : Mono (shortComplexH0 A).f := by
  rw [ModuleCat.mono_iff_injective]
  intro v w h
  apply Subtype.ext
  exact congrFun (congrArg Subtype.val h) Fin.elim0

theorem shortComplexH0_exact : (shortComplexH0 A).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro c₀ hc
  let c : locallyConstantCochains A 0 := c₀
  have hc' : ∀ g : Fin 1 → G, (inhomogeneousCochains.d A 0).hom c.1 g = 0 := fun g =>
    congrArg (fun x : locallyConstantCochains A (0 + 1) => x.1 g) hc
  refine ⟨⟨c.1 Fin.elim0, fun g => ?_⟩, Subtype.ext ?_⟩
  · have h := hc' fun _ => g
    have hfe : ∀ x : Fin 0 → G, c.1 x = c.1 Fin.elim0 := fun x => by
      rw [Subsingleton.elim x Fin.elim0]
    simp only [inhomogeneousCochains.d_hom_apply, hfe] at h
    exact add_neg_eq_zero.1 (by simpa using h)
  · funext x
    change c.1 Fin.elim0 = c.1 x
    rw [Subsingleton.elim x Fin.elim0]

theorem cochains_d_zero_one :
    (cochains A).d 0 1 = dLocallyConstant A 0 :=
  cochains_d A 0

noncomputable def cocyclesIso₀ : cocycles A 0 ≅ ModuleCat.of k A.ρ.invariants :=
  Limits.KernelFork.mapIsoOfIsLimit ((cochains A).cyclesIsKernel 0 1 (by simp))
    (shortComplexH0_exact A).fIsKernel
    (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
      simp only [Arrow.mk_hom, Iso.refl_hom, cochains_d_zero_one]
      exact (Category.id_comp _).trans (Category.comp_id _).symm))

noncomputable def zeroIso : cohomology A 0 ≅ ModuleCat.of k A.ρ.invariants :=
  (CochainComplex.isoHomologyπ₀ _).symm ≪≫ cocyclesIso₀ A

end H0

end Langlands.ProfiniteCohomology
