/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionGradedQuotientCore
public import Mathlib.CategoryTheory.Category.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionTensorCokernel

/-! The canonical comparison map for a convolution graded quotient. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.FilteredConvolutionCore
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

/-- A map into `T` whose composite with `T.arrow` factors through a smaller subobject `S`
is killed by the cokernel projection of `S ≤ T`. -/
theorem comp_cokernelπ_ofLE_eq_zero {D : Type*} [Category D] [Preadditive D] {Y X : D}
    {S T : Subobject Y} (h : S ≤ T) [HasCokernel (Subobject.ofLE S T h)] (f : X ⟶ (T : D))
    (g : X ⟶ (S : D)) (hfg : f ≫ T.arrow = g ≫ S.arrow) :
    f ≫ cokernel.π (Subobject.ofLE S T h) = 0 := by
  obtain rfl : f = g ≫ Subobject.ofLE S T h := by
    rw [← cancel_mono T.arrow, hfg, Category.assoc, Subobject.ofLE_arrow]
  rw [Category.assoc, cokernel.condition, comp_zero]

/-- The tensor of two filtration steps of total degree at least `s` lands in the `s`-th
convolution level. -/
theorem exists_lift_level {P Q : Complex R} (F : DecreasingFiltration P)
    (G : DecreasingFiltration Q) (p q s : ℤ) (hs : s ≤ p + q) :
    ∃ g : ((F.F p : Complex R) ⊗ (G.F q : Complex R)) ⟶ (level F G s : Complex R),
      g ≫ (level F G s).arrow = (F.F p).arrow ⊗ₘ (G.F q).arrow := by
  refine ⟨((F.F p : Complex R) ◁
        Subobject.ofLE _ _ (G.antitone (show s - p ≤ q by omega))) ≫
      Sigma.ι (fun p : ℤ ↦ (F.F p : Complex R) ⊗ (G.F (s - p) : Complex R)) p ≫
      factorThruImageSubobject _, ?_⟩
  simp only [level, Category.assoc, imageSubobject_arrow_comp, Sigma.ι_comp_desc]
  rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Subobject.ofLE_arrow]

/-- The quotient projections of the convolution summands induce a unique map to the
associated graded of the image filtration.  The proof is the two cokernel universal
properties, using preservation of coproducts and cokernels by the sheaf tensor product.
Source: the second step of the proof of `lem-trf-filtered-convolution-graded-quotient`.
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
theorem canonical_comparison_unique
    {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (H : DecreasingFiltration (P ⊗ Q)) (hH : ∀ r : ℤ, H.F r = level F G r) (r : ℤ) :
    ∃! α : gradedSource F G r ⟶ H.gradedPiece r, IsCanonical F G H r α := by
  have hlift (p q s : ℤ) (hs : s ≤ p + q) :
      ∃ g : ((F.F p : Complex R) ⊗ (G.F q : Complex R)) ⟶ (H.F s : Complex R),
        g ≫ (H.F s).arrow = (F.F p).arrow ⊗ₘ (G.F q).arrow := by
    rw [hH s]
    exact exists_lift_level F G p q s hs
  choose t ht using fun p : ℤ ↦ hlift p (r - p) r (by omega)
  have hψ (p : ℤ) := existsUnique_cokernelπ_tensorHom
    (Subobject.ofLE _ _ (F.F_succ_le p)) (Subobject.ofLE _ _ (G.F_succ_le (r - p)))
    (t p ≫ H.complexQuotientπ r (r + 1) (by omega)) (by
      obtain ⟨g, hg⟩ := hlift (p + 1) (r - p) (r + 1) (by omega)
      rw [← Category.assoc]
      refine comp_cokernelπ_ofLE_eq_zero _ _ g ?_
      rw [Category.assoc, ht, hg, ← tensorHom_id, tensorHom_comp_tensorHom,
        Subobject.ofLE_arrow, Category.id_comp]) (by
      obtain ⟨g, hg⟩ := hlift p (r - p + 1) (r + 1) (by omega)
      rw [← Category.assoc]
      refine comp_cokernelπ_ofLE_eq_zero _ _ g ?_
      rw [Category.assoc, ht, hg, ← id_tensorHom, tensorHom_comp_tensorHom,
        Subobject.ofLE_arrow, Category.id_comp])
  choose ψ hψ _ using hψ
  refine ⟨Sigma.desc (f := fun p ↦ F.gradedPiece p ⊗ G.gradedPiece (r - p))
      (P := H.gradedPiece r) ψ, fun p ↦ ⟨t p, ht p, ?_⟩,
    fun α hα ↦ Sigma.hom_ext _ _ fun p ↦ ?_⟩
  · erw [Sigma.ι_comp_desc]
    exact hψ p
  · obtain ⟨t', ht', h'⟩ := hα p
    obtain rfl : t' = t p := by rw [← cancel_mono (H.F r).arrow, ht', ht p]
    have : Epi (F.complexQuotientπ p (p + 1) (by omega) ⊗ₘ
        G.complexQuotientπ (r - p) (r - p + 1) (by omega)) :=
      epi_tensorHom (cokernel.π _) (cokernel.π _)
    erw [Sigma.ι_comp_desc]
    exact this.left_cancellation _ _ (h'.trans (hψ p).symm)

end SheafOfModules.FilteredConvolutionCore
