import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.Closure

/-!
# Vanishing of a module on an open subset

`VanishesOn M O` says that every section of `M` over an open contained in `O` is zero, that is,
the restriction of `M` to `O` is zero. The property is local, passes to kernels of maps out of
`M` and to cokernels of maps into `M`, and is compatible with the unit
`M ⟶ j_* (M|_Y)` of an open immersion `j : Y ⟶ X`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

namespace QuasicoherentLocal

open Langlands.Cohomology

variable {X : Scheme.{u}}

/-- Every section of `M` over an open contained in `O` is zero. -/
def VanishesOn (M : X.Modules) (O : X.Opens) : Prop :=
  ∀ W ≤ O, ∀ s : Γ(M, W), s = 0

namespace VanishesOn

variable {M N : X.Modules} {O O' : X.Opens}

lemma mono (h : VanishesOn M O) (hO : O' ≤ O) : VanishesOn M O' :=
  fun W hW => h W (hW.trans hO)

lemma sup (h₁ : VanishesOn M O) (h₂ : VanishesOn M O') : VanishesOn M (O ⊔ O') := by
  intro W hW s
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  refine TopCat.Sheaf.eq_of_locally_eq₂ (F := F) (homOfLE (inf_le_left : W ⊓ O ≤ W))
    (homOfLE (inf_le_left : W ⊓ O' ≤ W)) ?_ s 0 ?_ ?_
  · rw [← inf_sup_left]
    exact le_inf le_rfl hW
  · rw [map_zero]
    exact h₁ _ inf_le_right _
  · rw [map_zero]
    exact h₂ _ inf_le_right _

lemma of_iso (e : M ≅ N) (h : VanishesOn M O) : VanishesOn N O := by
  intro W hW s
  have hs : e.hom.app W (e.inv.app W s) = s :=
    congrArg (fun g : N ⟶ N => g.app W s) e.inv_hom_id
  rw [← hs, h W hW (e.inv.app W s), map_zero]

lemma kernel (φ : M ⟶ N) (h : VanishesOn M O) : VanishesOn (kernel φ) O :=
  fun W hW s => kernel_ι_app_injective φ W (by rw [h W hW ((kernel.ι φ).app W s), map_zero])

lemma isZero_restrict (h : VanishesOn M O) : IsZero (M.restrict O.ι) := by
  rw [IsZero.iff_id_eq_zero]
  apply Scheme.Modules.hom_ext
  intro W
  have h0 : ∀ x : Γ(M.restrict O.ι, W), x = 0 := fun x =>
    h _ ((Scheme.Hom.image_le_opensRange _ W).trans (Scheme.Opens.opensRange_ι O).le) x
  ext s
  exact (h0 _).trans (h0 _).symm

lemma of_isZero_restrict (h : IsZero (M.restrict O.ι)) : VanishesOn M O := by
  intro W hW s
  have e : O.ι ''ᵁ (O.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hW
  have h0 : ∀ x : Γ(M.restrict O.ι, O.ι ⁻¹ᵁ W), x = 0 := fun x =>
    congrArg (fun g : M.restrict O.ι ⟶ M.restrict O.ι => g.app (O.ι ⁻¹ᵁ W) x)
      (h.eq_of_src (𝟙 _) 0)
  have h1 : Cech.res (P := M.presheaf) e.le s = 0 := h0 _
  calc s = Cech.res (P := M.presheaf) e.ge (Cech.res e.le s) := by
        rw [Cech.res_res, Cech.res_self]
    _ = 0 := by rw [h1, map_zero]

lemma cokernel_of_right (φ : M ⟶ N) (h : VanishesOn N O) : VanishesOn (cokernel φ) O := by
  apply of_isZero_restrict
  have : Epi ((Scheme.Modules.restrictFunctor O.ι).map φ) := h.isZero_restrict.epi _
  exact (isZero_cokernel_of_epi _).of_iso
    (PreservesCokernel.iso (Scheme.Modules.restrictFunctor O.ι) φ)

lemma cokernel_of_isIso (φ : M ⟶ N) (h : IsIso ((Scheme.Modules.restrictFunctor O.ι).map φ)) :
    VanishesOn (cokernel φ) O := by
  apply of_isZero_restrict
  exact (isZero_cokernel_of_epi _).of_iso
    (PreservesCokernel.iso (Scheme.Modules.restrictFunctor O.ι) φ)

end VanishesOn

section Unit

variable {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules)

/-- The unit `M ⟶ j_* (M|_Y)` of restriction along an open immersion. -/
noncomputable abbrev unitMap : M ⟶ (Scheme.Modules.pushforward j).obj (M.restrict j) :=
  (Scheme.Modules.restrictAdjunction j).unit.app M

lemma isIso_unitMap_app {W : X.Opens} (hW : W ≤ j.opensRange) :
    IsIso ((unitMap j M).app W) := by
  have e : j ''ᵁ j ⁻¹ᵁ W = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.2 hW
  change IsIso (M.presheaf.map (homOfLE (j.image_preimage_le W)).op)
  rw [show homOfLE (j.image_preimage_le W) = eqToHom e from Subsingleton.elim _ _]
  infer_instance

lemma isIso_restrict_unitMap {O : X.Opens} (hO : O ≤ j.opensRange) :
    IsIso ((Scheme.Modules.restrictFunctor O.ι).map (unitMap j M)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  exact isIso_unitMap_app j M
    (((Scheme.Hom.image_le_opensRange _ W).trans (Scheme.Opens.opensRange_ι O).le).trans hO)

lemma vanishesOn_kernel_unitMap : VanishesOn (kernel (unitMap j M)) j.opensRange := by
  intro W hW s
  have := isIso_unitMap_app j M hW
  apply kernel_ι_app_injective (unitMap j M) W
  apply (ConcreteCategory.bijective_of_isIso ((unitMap j M).app W)).1
  rw [app_kernel_ι_app, map_zero, map_zero]

lemma vanishesOn_cokernel_unitMap : VanishesOn (cokernel (unitMap j M)) j.opensRange :=
  VanishesOn.cokernel_of_isIso _ (isIso_restrict_unitMap j M le_rfl)

lemma vanishesOn_pushforward_restrict {O O' : X.Opens} (h : VanishesOn M O')
    (hO : ∀ W ≤ O, j ''ᵁ j ⁻¹ᵁ W ≤ O') :
    VanishesOn ((Scheme.Modules.pushforward j).obj (M.restrict j)) O :=
  fun W hW s => h _ (hO W hW) s

end Unit

end QuasicoherentLocal

end Langlands.AlgebraicGeometry.Modules
