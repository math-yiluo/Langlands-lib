/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (𝓛 : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (j : ι) (hij : i ≤ j) (n : ℕ) (W : ULift.{u} (Fin n) → (Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))).Opens),
      (∀ k, IsAffineOpen (W k)) ∧
      ∀ (c : Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))) →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        (⨆ k, c ⁻¹ᵁ W k) = ⊤ ∧
        ∃ s : ∀ k, Γ(𝓛, c ⁻¹ᵁ W k), ∀ k, Scheme.Modules.IsFrameOn (s k) (c ⁻¹ᵁ W k) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit.solution ι _ _ _ G _ φ _ R _ g hR i X fX _ _ 𝓛 h𝓛
