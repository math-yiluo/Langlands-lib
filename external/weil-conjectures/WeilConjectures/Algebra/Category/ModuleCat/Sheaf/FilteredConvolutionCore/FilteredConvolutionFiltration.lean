/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionGradedQuotientCore

/-! Construction of the convolution filtration. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.FilteredConvolutionCore

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

/-- The convolution levels decrease: every generator of level `r + 1` factors through the
generator of level `r` with the same first index, since `G^(r+1-p) ≤ G^(r-p)`. -/
theorem level_succ_le {P Q : Complex R} (F : DecreasingFiltration P)
    (G : DecreasingFiltration Q) (r : ℤ) : level F G (r + 1) ≤ level F G r := by
  refine imageSubobject_le _ (Sigma.desc fun p ↦ ((F.F p : Complex R) ◁
      Subobject.ofLE _ _ (G.antitone (show r - p ≤ r + 1 - p by omega))) ≫
      Sigma.ι (fun p : ℤ ↦ (F.F p : Complex R) ⊗ (G.F (r - p) : Complex R)) p ≫
      factorThruImageSubobject _) ?_
  refine Sigma.hom_ext _ _ fun p ↦ ?_
  simp only [level, Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
    imageSubobject_arrow_comp]
  rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Subobject.ofLE_arrow]

/-- The image-sum subobjects form a decreasing filtration of the total tensor.
The proof is the degreewise tensor coherence and the image-subobject universal property.
Source: the convolution filtration step in the blueprint proof.
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
theorem convolution_filtration_exists
    (P Q : Complex R) (F : DecreasingFiltration P) (G : DecreasingFiltration Q) :
    ∃ H : DecreasingFiltration (P ⊗ Q), ∀ r : ℤ, H.F r = level F G r :=
  ⟨⟨level F G, level_succ_le F G⟩, fun _ ↦ rfl⟩

end SheafOfModules.FilteredConvolutionCore
