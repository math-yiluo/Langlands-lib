import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame

/-! # Refining the open family of a glued line bundle -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.CocycleGluing

variable {X : Scheme.{u}} {ι κ : Type u} {T : ι → X.Opens} {S : κ → X.Opens}

/-- Restrict transition units along a refinement of open families. -/
def refineCocycle (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)
    (β : κ → ι) (hβ : ∀ j, S j ≤ T (β j)) (i j : κ) : (Γ(X, S i ⊓ S j))ˣ :=
  Units.map (X.presheaf.map (homOfLE (inf_le_inf (hβ i) (hβ j))).op).hom.toMonoidHom
    (g (β i) (β j))

lemma refineCocycle_val (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)
    (β : κ → ι) (hβ : ∀ j, S j ≤ T (β j)) (i j : κ) :
    (refineCocycle g β hβ i j : Γ(X, S i ⊓ S j)) =
      X.presheaf.map (homOfLE (inf_le_inf (hβ i) (hβ j))).op
        (g (β i) (β j) : Γ(X, T (β i) ⊓ T (β j))) := rfl

/-- The original glued generators, restricted to the refined opens. -/
noncomputable def refineFrame (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g)
    (β : κ → ι) (hβ : ∀ j, S j ≤ T (β j)) (j : κ) : Γ(glued g, S j) :=
  genSec g hg (β j) (hβ j)

lemma isFrameOn_refineFrame (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g)
    (β : κ → ι) (hβ : ∀ j, S j ≤ T (β j)) (j : κ) :
    Scheme.Modules.IsFrameOn (refineFrame g hg β hβ j) (S j) := by
  intro W hW _
  dsimp only [refineFrame]
  rw [map_genSec]
  exact smul_genSec_bijective g hg (β j) (hW.trans (hβ j))

lemma isTransition_refineFrame (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g)
    (β : κ → ι) (hβ : ∀ j, S j ≤ T (β j)) :
    IsTransition (refineFrame g hg β hβ) (refineCocycle g β hβ) := by
  intro i j
  dsimp only [refineFrame]
  rw [map_genSec, map_genSec, refineCocycle_val]
  exact genSec_eq_smul_genSec hg (inf_le_left.trans (hβ i)) (inf_le_right.trans (hβ j))

/-- Restricted transition units still satisfy the cocycle equation. -/
lemma isCocycle_refineCocycle (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g)
    (β : κ → ι) (hβ : ∀ j, S j ≤ T (β j)) :
    IsCocycle (refineCocycle g β hβ) :=
  isCocycle_of_isTransition (isFrameOn_refineFrame g hg β hβ)
    (isTransition_refineFrame g hg β hβ)

/-- Refining to a full open cover preserves the actual glued module sheaf. -/
noncomputable def refinementIso (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g)
    (β : κ → ι) (hβ : ∀ j, S j ≤ T (β j)) (hS : (⨆ j, S j) = ⊤) :
    glued g ≅ glued (refineCocycle g β hβ) :=
  frameIso (isFrameOn_refineFrame g hg β hβ) (isTransition_refineFrame g hg β hβ) hS

/-- The refinement isomorphism matches the corresponding restricted local generators. -/
lemma refinementIso_hom_app_genSec
    (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g)
    (β : κ → ι) (hβ : ∀ j, S j ≤ T (β j)) (hS : (⨆ j, S j) = ⊤)
    (j : κ) {V : X.Opens} (hV : V ≤ S j) :
    (refinementIso g hg β hβ hS).hom.app V
        (genSec g hg (β j) (hV.trans (hβ j))) =
      genSec (refineCocycle g β hβ) (isCocycle_refineCocycle g hg β hβ) j hV := by
  have h := frameIso_hom_app_frame (isFrameOn_refineFrame g hg β hβ)
    (isTransition_refineFrame g hg β hβ) hS (isCocycle_refineCocycle g hg β hβ) j hV
  simpa only [refinementIso, refineFrame, map_genSec] using h

/-- The inverse refinement isomorphism recovers the original restricted generator. -/
lemma refinementIso_inv_app_genSec
    (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (hg : IsCocycle g)
    (β : κ → ι) (hβ : ∀ j, S j ≤ T (β j)) (hS : (⨆ j, S j) = ⊤)
    (j : κ) {V : X.Opens} (hV : V ≤ S j) :
    (refinementIso g hg β hβ hS).inv.app V
        (genSec (refineCocycle g β hβ) (isCocycle_refineCocycle g hg β hβ) j hV) =
      genSec g hg (β j) (hV.trans (hβ j)) := by
  have h := frameIso_inv_app_genSec (isFrameOn_refineFrame g hg β hβ)
    (isTransition_refineFrame g hg β hβ) hS (isCocycle_refineCocycle g hg β hβ) j hV
  simpa only [refinementIso, refineFrame, map_genSec] using h

end Langlands.AlgebraicGeometry.Picard.CocycleGluing
