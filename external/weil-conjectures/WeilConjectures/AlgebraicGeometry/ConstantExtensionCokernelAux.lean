/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.ConstantExtensionPresentationLift
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

private theorem extension_presentation
    {C : Type*} [Category C] [Abelian C]
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (e : T.X₃ ≅ S.X₃) (r : T.X₂ ⟶ S.X₂)
    (hr : r ≫ S.g = T.g ≫ e.hom) :
    ∃ d : T.X₁ ⟶ S.X₁ ⊞ T.X₂, Nonempty (cokernel d ≅ S.X₂) := by
  have := hS.mono_f
  have := hS.epi_g
  have := hT.mono_f
  have := hT.epi_g
  have hz : (T.f ≫ r) ≫ S.g = 0 := by
    simp only [Category.assoc, hr, T.zero_assoc, zero_comp]
  let g := hS.exact.lift (T.f ≫ r) hz
  have hg : g ≫ S.f = T.f ≫ r := hS.exact.lift_f _ _
  let d := biprod.lift (-g) T.f
  let q := biprod.desc S.f r
  have hdq : d ≫ q = 0 := by simp [d, q, hg]
  have hd : d ≫ biprod.snd = T.f := by simp [d]
  have : Mono d := mono_of_mono_fac hd
  have hq : Epi q := by
    rw [Preadditive.epi_iff_cancel_zero]
    intro Z k hk
    have ha : S.f ≫ k = 0 := by
      simpa [q] using congrArg (fun t ↦ biprod.inl ≫ t) hk
    have hb : r ≫ k = 0 := by
      simpa [q] using congrArg (fun t ↦ biprod.inr ≫ t) hk
    obtain ⟨l, hl⟩ := hS.exact.desc' k ha
    have he : e.hom ≫ l = 0 := by
      apply (cancel_epi T.g).mp
      rw [← Category.assoc, ← hr, Category.assoc, hl, hb, comp_zero]
    have hlz : l = 0 := by simpa using congrArg (fun t ↦ e.inv ≫ t) he
    rw [← hl, hlz, comp_zero]
  have hkern : IsLimit (KernelFork.ofι d hdq) := by
    apply KernelFork.IsLimit.ofι'
    intro Z k hk
    have hb : (k ≫ biprod.snd) ≫ T.g = 0 := by
      apply (cancel_mono e.hom).mp
      have he := congrArg (fun t ↦ t ≫ S.g) hk
      simpa [q, biprod.desc_eq, Preadditive.comp_add, Preadditive.add_comp,
        Category.assoc, S.zero, ← hr] using he
    let l := hT.exact.lift (k ≫ biprod.snd) hb
    have hl : l ≫ T.f = k ≫ biprod.snd := hT.exact.lift_f _ _
    refine ⟨l, ?_⟩
    apply biprod.hom_ext
    · have ha : (k ≫ biprod.fst) ≫ S.f + (k ≫ biprod.snd) ≫ r = 0 := by
        simpa [q, biprod.desc_eq, Preadditive.comp_add, Category.assoc] using hk
      apply (cancel_mono S.f).mp
      simp only [Category.assoc, d, biprod.lift_fst, Preadditive.comp_neg,
        Preadditive.neg_comp, hg]
      rw [← Category.assoc, hl]
      simpa only [Category.assoc] using (eq_neg_of_add_eq_zero_left ha).symm
    · simpa [d, Category.assoc] using hl
  let U := ShortComplex.mk d q hdq
  have hu : U.Exact := U.exact_of_f_is_kernel hkern
  refine ⟨d, ⟨?_⟩⟩
  exact (cokernelIsCokernel d).coconePointUniqueUpToIso hu.gIsCokernel

/-- An extension with constant outer terms admits a local cokernel presentation before
recording finite generation of the source module.
Source: Stacks Project, Tag 093U, extension argument.
(blueprint: lem-pc-constant-extension-cokernel-aux-cover)
-/
theorem exists_constantExtension_cokernelPresentation_aux_cover {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact)
    [S.X₁.IsConstant X.smallEtaleTopology] [S.X₃.IsConstant X.smallEtaleTopology]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ∃ K L : ModuleCat.{u + 1} Λ, ∃ φ :
        (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj K ⟶
          (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj L,
          Nonempty (cokernel φ ≅
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂) := by
  obtain ⟨𝒰, h𝒰⟩ := exists_constantExtension_presentation_lift hS
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨T, hT, _, e, r, hr⟩ := h𝒰 i
  let F := constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let P := Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)
  obtain ⟨d, ⟨ed⟩⟩ := extension_presentation (hS.map_of_exact P)
    (hT.map_of_exact F) e r hr
  obtain ⟨M, ⟨eM⟩⟩ := S.X₁.mem_essImage_of_isConstant
  let eA : F.obj M ≅ P.obj S.X₁ :=
    ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (𝒰.f i)).app M).symm ≪≫ P.mapIso eM
  let eB : F.obj (M ⊞ T.X₂) ≅ F.obj M ⊞ F.obj T.X₂ :=
    F.mapIso (biprod.isoCoprod M T.X₂) ≪≫ (PreservesColimitPair.iso F M T.X₂).symm ≪≫
      (biprod.isoCoprod _ _).symm
  let eL := eB ≪≫ biprod.mapIso eA (Iso.refl _)
  refine ⟨T.X₁, M ⊞ T.X₂, d ≫ eL.inv, ⟨?_⟩⟩
  exact cokernel.mapIso (d ≫ eL.inv) d (Iso.refl _) eL (by simp) ≪≫ ed

/-- A lifted short exact module presentation with finite kernel yields a finite-source
cokernel presentation of the middle term, when the first term is constant.
Source: Stacks Project, Tag 093U, finite free presentation step.
(blueprint: lem-pc-constant-extension-cokernel-aux-finite)

Proof: Restrict the extension and apply the exact constant-sheaf functor to the supplied
module presentation. Factor the lifted kernel map through the first term. The proved
helper shows that (-g,T.f) has the middle term as its cokernel. Identify the first term
with a constant model M and the biproduct with the constant sheaf of M plus T.X₂.
Transporting the cokernel along this isomorphism preserves the source T.X₁, whose finite
generation is part of the supplied presentation. -/
theorem finite_cokernelPresentation_of_local_presentation {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {𝒰 : Cover.{u} etalePrecoverage X} {i : 𝒰.I₀}
    (hS : S.ShortExact)
    [S.X₁.IsConstant X.smallEtaleTopology]
    (h : ∃ T : ShortComplex (ModuleCat.{u + 1} Λ), T.ShortExact ∧ Module.Finite Λ T.X₁ ∧
        ∃ e : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₃ ≅
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₃,
        ∃ r : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₂ ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂,
          r ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).map S.g =
            (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map T.g ≫
              e.hom) :
    ∃ K L : ModuleCat.{u + 1} Λ, Module.Finite Λ K ∧ ∃ φ :
      (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj K ⟶
        (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj L,
      Nonempty (cokernel φ ≅
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂) := by
  obtain ⟨T, hT, hfinite, e, r, hr⟩ := h
  let F := constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let P := Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)
  obtain ⟨d, ⟨ed⟩⟩ := extension_presentation (hS.map_of_exact P)
    (hT.map_of_exact F) e r hr
  obtain ⟨M, ⟨eM⟩⟩ := S.X₁.mem_essImage_of_isConstant
  let eA : F.obj M ≅ P.obj S.X₁ :=
    ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (𝒰.f i)).app M).symm ≪≫ P.mapIso eM
  let eB : F.obj (M ⊞ T.X₂) ≅ F.obj M ⊞ F.obj T.X₂ :=
    F.mapIso (biprod.isoCoprod M T.X₂) ≪≫ (PreservesColimitPair.iso F M T.X₂).symm ≪≫
      (biprod.isoCoprod _ _).symm
  let eL := eB ≪≫ biprod.mapIso eA (Iso.refl _)
  refine ⟨T.X₁, M ⊞ T.X₂, hfinite, d ≫ eL.inv, ⟨?_⟩⟩
  exact cokernel.mapIso (d ≫ eL.inv) d (Iso.refl _) eL (by simp) ≪≫ ed

end AlgebraicGeometry.Scheme
