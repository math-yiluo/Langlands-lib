/-
Ported from `P2M/Sol/S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisationRosati
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem solution
    {S S' : Type u} [CommRing S] [CommRing S'] {X Y : Scheme.{u}}
    {g : X ⟶ Spec (CommRingCat.of S)} (g' : Y ⟶ Spec (CommRingCat.of S')) (h : Y ⟶ X)
    (φ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (comm : h ≫ g = g' ≫ φ)
    {M M' : X.Modules} (hM : LocIsoOnBase g M M') :
    LocIsoOnBase g' ((Scheme.Modules.pullback h).obj M) ((Scheme.Modules.pullback h).obj M') := by
  intro s'
  obtain ⟨U, hs, ⟨e⟩⟩ := hM (φ.base s')
  refine ⟨φ ⁻¹ᵁ U, hs, ⟨?_⟩⟩

  have hle : g' ⁻¹ᵁ (φ ⁻¹ᵁ U) ≤ h ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, comm]
  let r : (g' ⁻¹ᵁ (φ ⁻¹ᵁ U)).toScheme ⟶ (g ⁻¹ᵁ U).toScheme := h.resLE (g ⁻¹ᵁ U) (g' ⁻¹ᵁ (φ ⁻¹ᵁ U)) hle
  have hr : r ≫ (g ⁻¹ᵁ U).ι = (g' ⁻¹ᵁ (φ ⁻¹ᵁ U)).ι ≫ h := Scheme.Hom.resLE_comp_ι _ _
  exact ((Scheme.Modules.pullbackComp (g' ⁻¹ᵁ (φ ⁻¹ᵁ U)).ι h).app M) ≪≫
    (Scheme.Modules.pullbackCongr hr.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp r (g ⁻¹ᵁ U).ι).app M).symm ≪≫
        (Scheme.Modules.pullback r).mapIso e ≪≫
          (Scheme.Modules.pullbackComp r (g ⁻¹ᵁ U).ι).app M' ≪≫
            (Scheme.Modules.pullbackCongr hr).app M' ≪≫
              ((Scheme.Modules.pullbackComp (g' ⁻¹ᵁ (φ ⁻¹ᵁ U)).ι h).app M').symm
