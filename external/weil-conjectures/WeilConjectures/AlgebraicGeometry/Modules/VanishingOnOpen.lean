/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-!
# Modules vanishing on an open subset

An `𝒪_X`-module `M` *vanishes on* an open `U` if its restriction `M|_U` is zero, i.e. if all its
sections over opens contained in `U` vanish. We show that this is a local condition, so that a
module vanishing on two opens vanishes on their union, and record how it interacts with kernels,
cokernels and tensor products. For a global section `s` of an invertible module `ℒ`, the
morphism `F ⟶ F ⊗ ℒ` given by `s` is an isomorphism away from the zero scheme of `s`, so its
kernel and cokernel vanish there.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isZero_restrict_sup`: a module vanishing on `U` and on `W`
  vanishes on `U ⊔ W`.
- `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_le`: a section `s` of an
  invertible module is an isomorphism `𝒪_U ≅ ℒ|_U` on every open `U` not meeting its zero scheme.
- `AlgebraicGeometry.Scheme.Modules.isZero_restrict_kernel_of_isIso` and
  `AlgebraicGeometry.Scheme.Modules.isZero_restrict_cokernel_of_isIso`: kernels and cokernels
  vanish where the morphism is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A module is zero if and only if all its sections vanish. -/
lemma isZero_iff_forall_subsingleton (M : X.Modules) :
    IsZero M ↔ ∀ U : X.Opens, Subsingleton Γ(M, U) := by
  refine ⟨fun h U ↦ ?_, fun h ↦ ?_⟩
  · have h0 (a : Γ(M, U)) : a = 0 := by
      have := congrArg (fun f : M ⟶ M ↦ Hom.app f U a) (h.eq_of_src (𝟙 M) 0)
      simpa using this
    exact ⟨fun a b ↦ (h0 a).trans (h0 b).symm⟩
  · refine (IsZero.iff_id_eq_zero M).mpr (hom_ext _ _ fun U ↦ ?_)
    ext x
    exact Subsingleton.elim _ _

/-- The restriction of `M` to `U` is zero if and only if all sections of `M` over opens contained
in `U` vanish. -/
lemma isZero_restrict_iff (M : X.Modules) (U : X.Opens) :
    IsZero (M.restrict U.ι) ↔ ∀ V : X.Opens, V ≤ U → Subsingleton Γ(M, V) := by
  rw [isZero_iff_forall_subsingleton]
  refine ⟨fun h V hV ↦ ?_, fun h V ↦ h _ (U.ι.image_le_opensRange _ |>.trans (by simp))⟩
  obtain ⟨V', rfl⟩ : ∃ V' : U.toScheme.Opens, U.ι ''ᵁ V' = V :=
    ⟨U.ι ⁻¹ᵁ V, by rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.2 hV]⟩
  exact h V'

/-- Vanishing on an open is inherited by smaller opens. -/
lemma isZero_restrict_of_le {M : X.Modules} {U W : X.Opens} (hWU : W ≤ U)
    (h : IsZero (M.restrict U.ι)) : IsZero (M.restrict W.ι) :=
  (isZero_restrict_iff M W).mpr fun V hV ↦ (isZero_restrict_iff M U).mp h V (hV.trans hWU)

/-- **Vanishing on an open is local.** A module vanishing on `U` and on `W` vanishes on
`U ⊔ W`: a section over `V ≤ U ⊔ W` vanishes on the cover `V ⊓ U, V ⊓ W` of `V`. -/
lemma isZero_restrict_sup {M : X.Modules} {U W : X.Opens} (hU : IsZero (M.restrict U.ι))
    (hW : IsZero (M.restrict W.ι)) : IsZero (M.restrict (U ⊔ W).ι) := by
  rw [isZero_restrict_iff] at hU hW ⊢
  intro V hV
  refine ⟨fun a b ↦ ?_⟩
  let S : Sieve V := Sieve.generate (Presieve.ofArrows (fun i : Bool ↦ V ⊓ cond i U W)
    (fun i ↦ homOfLE inf_le_left))
  have hS : S ∈ Opens.grothendieckTopology X V := by
    intro x hx
    obtain hxU | hxW := (hV hx : x ∈ U ⊔ W)
    · exact ⟨V ⊓ U, homOfLE inf_le_left,
        ⟨_, 𝟙 _, _, Presieve.ofArrows.mk true, Category.id_comp _⟩, ⟨hx, hxU⟩⟩
    · exact ⟨V ⊓ W, homOfLE inf_le_left,
        ⟨_, 𝟙 _, _, Presieve.ofArrows.mk false, Category.id_comp _⟩, ⟨hx, hxW⟩⟩
  refine ((M.isSheaf_presheaf_comp_forget) _ hS).isSeparatedFor.ext fun Z l hl ↦ ?_
  have hZ : Z ≤ U ∨ Z ≤ W := by
    obtain ⟨Y, g, f, hf, rfl⟩ := hl
    obtain ⟨i⟩ := hf
    cases i
    · exact Or.inr ((leOfHom g).trans inf_le_right)
    · exact Or.inl ((leOfHom g).trans inf_le_right)
  obtain hZ | hZ := hZ
  · exact (hU Z hZ).elim _ _
  · exact (hW Z hZ).elim _ _

/-- A module whose restriction to `⊤` vanishes is zero. -/
lemma isZero_of_isZero_restrict_top {M : X.Modules} (h : IsZero (M.restrict (⊤ : X.Opens).ι)) :
    IsZero M :=
  (isZero_iff_forall_subsingleton M).mpr fun V ↦ (isZero_restrict_iff M ⊤).mp h V le_top

/-- The restriction of a zero module vanishes. -/
lemma isZero_restrict_of_isZero {M : X.Modules} (h : IsZero M) (U : X.Opens) :
    IsZero (M.restrict U.ι) :=
  (isZero_restrict_iff M U).mpr fun V _ ↦ (isZero_iff_forall_subsingleton M).mp h V

section Restrict

variable {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)

/-- The kernel of `φ` vanishes on any open on which `φ` is an isomorphism. -/
lemma isZero_restrict_kernel_of_isIso [IsIso ((restrictFunctor U.ι).map φ)] :
    IsZero ((kernel φ).restrict U.ι) :=
  (isZero_kernel_of_mono ((restrictFunctor U.ι).map φ)).of_iso
    (PreservesKernel.iso (restrictFunctor U.ι) φ)

/-- The cokernel of `φ` vanishes on any open on which `φ` is an isomorphism. -/
lemma isZero_restrict_cokernel_of_isIso [IsIso ((restrictFunctor U.ι).map φ)] :
    IsZero ((cokernel φ).restrict U.ι) :=
  (isZero_cokernel_of_epi ((restrictFunctor U.ι).map φ)).of_iso
    (PreservesCokernel.iso (restrictFunctor U.ι) φ)

/-- The kernel of `φ` vanishes on any open on which the source of `φ` vanishes. -/
lemma isZero_restrict_kernel_of_isZero (h : IsZero (M.restrict U.ι)) :
    IsZero ((kernel φ).restrict U.ι) :=
  (isZero_restrict_iff _ U).mpr fun V hV ↦ ⟨fun _ _ ↦ injective_map_kernelι V φ
    (((isZero_restrict_iff M U).mp h V hV).elim _ _)⟩

/-- The cokernel of `φ` vanishes on any open on which the target of `φ` vanishes. -/
lemma isZero_restrict_cokernel_of_isZero (h : IsZero (N.restrict U.ι)) :
    IsZero ((cokernel φ).restrict U.ι) := by
  have : IsZero (cokernel ((restrictFunctor U.ι).map φ)) := by
    refine (IsZero.iff_id_eq_zero _).mpr (coequalizer.hom_ext ?_)
    exact h.eq_of_src _ _
  exact this.of_iso (PreservesCokernel.iso (restrictFunctor U.ι) φ)

end Restrict

section Section

variable {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L)

/-- **A section is an isomorphism away from its zero scheme.** If the open `U` does not meet the
zero scheme of `s : 𝒪_X ⟶ ℒ`, then `s|_U : 𝒪_U ⟶ ℒ|_U` is an isomorphism. -/
lemma isIso_restrictFunctor_map_of_le [SheafOfModules.IsInvertible.{u, u, u} L] {U : X.Opens}
    (hU : U ≤ (Hom.zeroLocus s).support.compl) :
    IsIso ((restrictFunctor U.ι).map s) := by
  have he := isFreeGenerator_app_one_of_le s (U := U.ι ''ᵁ ⊤)
    ((U.ι.image_le_opensRange _).trans (by simpa using hU))
  have : IsIso ((restrictUnitIso U.ι).inv ≫ (restrictFunctor U.ι).map s) :=
    (isFreeGenerator_iff_isIso U.ι _).mp (by
      convert he using 1
      rw [Hom.comp_app, ConcreteCategory.comp_apply]
      exact congrArg (Hom.app s (U.ι ''ᵁ ⊤)) (map_one (U.ι.appIso ⊤).inv.hom))
  exact IsIso.of_isIso_comp_left (restrictUnitIso U.ι).inv _

/-- If `s` is an isomorphism on `U`, so is `F ⊗ s : F ⊗ 𝒪_X ⟶ F ⊗ ℒ`, since restriction is
monoidal. -/
lemma isIso_restrictFunctor_map_whiskerLeft (F : X.Modules) {U : X.Opens}
    [IsIso ((restrictFunctor U.ι).map s)] :
    IsIso ((restrictFunctor U.ι).map (F ◁ s)) := by
  rw [NatIso.isIso_map_iff (restrictFunctorIsoPullback U.ι)] at *
  have h := Functor.LaxMonoidal.μ_natural_right (pullback U.ι) F s
  rw [(IsIso.eq_inv_comp _).mpr h.symm]
  infer_instance

end Section

end AlgebraicGeometry.Scheme.Modules
