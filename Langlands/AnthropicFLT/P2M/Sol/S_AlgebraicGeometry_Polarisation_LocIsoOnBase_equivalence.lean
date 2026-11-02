/-
Ported from `P2M/Sol/S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped and its commands are replaced
by standard Lean commands. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisationRosati
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Polarisation

universe u

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.homOfLE Scheme.Modules Scheme.Modules.pullbackComp Polarisation.LocIsoOnBase)
namespace Polarisation
export _root_.AlgebraicGeometry.Polarisation (LocIsoOnBase)
namespace LocIsoOnBaseEquivSol
open _root_.AlgebraicGeometry.Polarisation _root_.AlgebraicGeometry

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S))

private theorem _root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.refl (M : X.Modules) : LocIsoOnBase g M M :=
  fun _ => ⟨⊤, trivial, ⟨Iso.refl _⟩⟩

variable {g} in
private theorem _root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.symm {M M' : X.Modules} (h : LocIsoOnBase g M M') : LocIsoOnBase g M' M := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := h s
  exact ⟨U, hs, ⟨e.symm⟩⟩


def restrictIso {M M' : X.Modules} {U V : (Spec (CommRingCat.of S)).Opens} (hVU : V ≤ U)
    (e : (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M') :
    (Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj M' :=
  have hle : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U := fun _ hx => hVU hx
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE hle) (g ⁻¹ᵁ U).ι).app M).symm ≪≫
      (Scheme.Modules.pullback (X.homOfLE hle)).mapIso e ≪≫
        (Scheme.Modules.pullbackComp (X.homOfLE hle) (g ⁻¹ᵁ U).ι).app M' ≪≫
          (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle)).app M'

variable {g} in
theorem trans {M M' M'' : X.Modules} (h : LocIsoOnBase g M M') (h' : LocIsoOnBase g M' M'') :
    LocIsoOnBase g M M'' := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := h s
  obtain ⟨U', hs', ⟨e'⟩⟩ := h' s
  exact ⟨U ⊓ U', ⟨hs, hs'⟩, ⟨restrictIso g inf_le_left e ≪≫ restrictIso g inf_le_right e'⟩⟩

end AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol

open AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol in
theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S)) :
    Equivalence (LocIsoOnBase g) :=
  ⟨_root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.refl g, _root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.symm, trans⟩

end
