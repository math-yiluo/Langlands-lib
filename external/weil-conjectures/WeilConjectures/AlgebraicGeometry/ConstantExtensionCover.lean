/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.ConstantExtensionCokernelPresentation
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import WeilConjectures.AlgebraicGeometry.EtaleShortExactLocalLift
import WeilConjectures.ConstructibleSheaf.Biproduct

/-!
# Local presentations of extensions with finite constant outer terms

Source: Stacks Project, Etale Cohomology Tag 03RX (3), via Modules on Sites Tag 093U.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- Choose an etale cover from a covering sieve of the final etale object. -/
private def presentationCover {Y : Scheme.{u}} (R : Sieve (Etale.mk (𝟙 Y)))
    (hR : R ∈ Y.smallEtaleTopology _) : Cover.{u} etalePrecoverage Y where
  I₀ := Y
  X y := ((mem_smallEtaleTopology_iff R).mp hR y).choose.left
  f y := ((mem_smallEtaleTopology_iff R).mp hR y).choose_spec.choose.left
  mem₀ := by
    refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun y ↦ ?_, fun y ↦ inferInstance⟩
    exact ⟨y, ((mem_smallEtaleTopology_iff R).mp hR y).choose_spec.choose_spec.2⟩

/-- Cokernels of maps out of finitely generated constant module sheaves are locally constant
when the target is constant. -/
private theorem exists_constantCokernel_cover {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]
    (K L : ModuleCat.{u + 1} Λ) [Module.Finite Λ K]
    (φ : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj K ⟶
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj L) :
    ∃ 𝒱 : Cover.{u} etalePrecoverage Y, ∀ j,
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒱.f j)).obj (cokernel φ)).IsConstant
        (𝒱.X j).smallEtaleTopology := by
  obtain ⟨R, hR, hmem⟩ := exists_mem_forall_exists_constantSheafOverHom_comp_map_eq
    Y.smallEtaleTopology (T := Etale.mk (𝟙 Y)) K L φ
  refine ⟨presentationCover R hR, fun y ↦ ?_⟩
  let V := ((mem_smallEtaleTopology_iff R).mp hR y).choose
  let a : V ⟶ Etale.mk (𝟙 Y) :=
    ((mem_smallEtaleTopology_iff R).mp hR y).choose_spec.choose
  have ha : R a := ((mem_smallEtaleTopology_iff R).mp hR y).choose_spec.choose_spec.1
  have hV : (⊥ : Sieve V) ∉ Y.smallEtaleTopology V := by
    intro h
    obtain ⟨W, b, hb, _⟩ := (mem_smallEtaleTopology_iff _).mp h
      ((mem_smallEtaleTopology_iff R).mp hR y).choose_spec.choose_spec.2.choose
    exact hb
  obtain ⟨f, hf⟩ := hmem a ha hV
  have hc := Sheaf.isConstant_cokernel_over Y.smallEtaleTopology _ V f φ hf
  rw [isConstant_over_iff_upperStar] at hc
  have hw : a.left = V.hom :=
    (Category.comp_id _).symm.trans (MorphismProperty.Over.w a)
  change ((Etale.upperStar (ModuleCat.{u + 1} Λ) a.left).obj (cokernel φ)).IsConstant
    V.left.smallEtaleTopology
  rwa [hw]

/-- An extension with constant outer terms of finite stalks has a cover on which its middle
term is constant. Source: Stacks Project, Tags 03RX (3) and 093U.
(blueprint: lem-constructible-constant-extension-cover)

Proof: Discard empty members of covers. Write the outer terms as constant sheaves M and N.
Their values are finitely generated, since they identify with geometric stalks on a nonempty
scheme. Choose a finite free presentation Λ^m → N, with kernel K. The finite ring hypothesis
makes K and Λ^m finite. The epimorphism from the middle term to N admits simultaneous local
lifts of the finitely many generators by local surjectivity and intersection of their covering
sieves. These lifts give a morphism r from the constant sheaf Λ^m to the middle term. Its
restriction to K factors through M, defining g. Exactness of the constant sheaf functor makes
the middle term the cokernel of (-g, inclusion): K → M ⊞ Λ^m: the quotient map sends (a,v)
to a+r(v); it is epi, and its kernel consists of pairs (-g(k),k). On a further cover, the
morphism g between finite constant sheaves is induced by a module homomorphism, by the
constant morphism lemma. The displayed cokernel is then the constant sheaf of its module
cokernel. The composite covers give the asserted cover. Empty schemes admit the empty cover;
no splitting of the original extension is asserted. -/
theorem exists_constantExtension_cover {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]
    [Finite Λ] {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hS : S.ShortExact)
    [S.X₁.IsConstant X.smallEtaleTopology] [S.X₃.IsConstant X.smallEtaleTopology]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂).IsConstant
        (𝒰.X i).smallEtaleTopology := by
  classical
  have : etalePrecoverage.{u}.IsStableUnderComposition :=
    inferInstanceAs (precoverage @Etale).IsStableUnderComposition
  obtain ⟨𝒰, h𝒰⟩ := exists_constantExtension_cokernelPresentation hS
  have key : ∀ i : 𝒰.I₀, ∃ 𝒱 : Cover.{u} etalePrecoverage (𝒰.X i), ∀ j,
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒱.f j ≫ 𝒰.f i)).obj S.X₂).IsConstant
        (𝒱.X j).smallEtaleTopology := by
    intro i
    obtain ⟨K, L, hK, φ, ⟨e⟩⟩ := h𝒰 i
    have : Module.Finite Λ K := hK
    obtain ⟨𝒱, h𝒱⟩ := exists_constantCokernel_cover K L φ
    refine ⟨𝒱, fun j ↦ ?_⟩
    have := h𝒱 j
    exact Sheaf.isConstant_congr _
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒱.f j)).mapIso e ≪≫
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (𝒱.f j) (𝒰.f i)).app S.X₂).symm)
  choose 𝒱 h𝒱 using key
  exact ⟨𝒰.bind 𝒱, fun ⟨i, j⟩ ↦ h𝒱 i j⟩

end

end AlgebraicGeometry.Scheme
