/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Monoidal

/-!
# The tensor product of locally constant sheaves of modules is locally constant

Let `Λ` be a commutative ring. The tensor product of two constant sheaves of `Λ`-modules on the
small étale site of a scheme is constant, `M_X ⊗ N_X ≅ (M ⊗ N)_X`, sheafification being
monoidal. Since the pullback along an étale map is monoidal, the tensor product of two locally
constant sheaves is trivialised by a common trivialising étale cover, hence locally constant.

## Main results

- `AlgebraicGeometry.Scheme.isConstant_tensorObj`
- `AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.tensorObj`
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- The constant presheaf at `M ⊗ N` is the tensor product of the constant presheaves. -/
noncomputable def constTensorIso (M N : ModuleCat.{u + 1} Λ) :
    (Functor.const X.Etaleᵒᵖ).obj (M ⊗ N) ≅
      (Functor.const X.Etaleᵒᵖ).obj M ⊗ (Functor.const X.Etaleᵒᵖ).obj N :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp)

/-- The tensor product of two constant sheaves of `Λ`-modules on the small étale site is
constant: `M_X ⊗ N_X ≅ (M ⊗ N)_X`, sheafification being monoidal. -/
theorem isConstant_tensorObj (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [F.IsConstant X.smallEtaleTopology] [G.IsConstant X.smallEtaleTopology] :
    (F ⊗ G).IsConstant X.smallEtaleTopology := by
  obtain ⟨M, ⟨i⟩⟩ := F.mem_essImage_of_isConstant
  obtain ⟨N, ⟨j⟩⟩ := G.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _ (X := M ⊗ N) ((i.symm ⊗ᵢ j.symm) ≪≫
    (Functor.Monoidal.μIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      ((Functor.const X.Etaleᵒᵖ).obj M) ((Functor.const X.Etaleᵒᵖ).obj N)) ≪≫
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
      (constTensorIso M N).symm)

/-- **The tensor product of locally constant sheaves of modules is locally constant**: on a
common trivialising étale cover, the pullback of `F ⊗ G` is the tensor product of the pullbacks,
the pullback being monoidal, which is constant.
(blueprint: `lem-weil-pbc-flc-tensor-locally-constant-part`) -/
theorem IsLocallyConstantSheaf.tensorObj (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf F] [IsLocallyConstantSheaf G] :
    IsLocallyConstantSheaf (F ⊗ G) := by
  obtain ⟨𝒰, h𝒰⟩ := IsLocallyConstantSheaf.exists_cover₂ F G
  refine ⟨⟨⟨𝒰, fun i ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  change ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj (F ⊗ G)).IsConstant
    (𝒰.X i).smallEtaleTopology
  obtain ⟨hF, hG⟩ := h𝒰 i
  have := isConstant_tensorObj ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj G)
  exact Sheaf.isConstant_congr _
    (Functor.Monoidal.μIso (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)) F G)

end AlgebraicGeometry.Scheme
