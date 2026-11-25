/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-! # The generator of a principal Cartier ideal
Source: Stacks Project, Tags 01WQ and 0A45; principal-chart step of
lem-pur-finite-cartier-pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Multiplication by the equation identifies the structure sheaf with the principal
Cartier ideal, compatibly with its inclusion into the structure sheaf.
Source: Stacks Tags 01WQ and 0A45, principal ideal trivialization.
(blueprint: lem-pur-principal-cartier-ideal-frame).
Proof: the equation vanishes on its zero subscheme, so it lifts to a global section
of the ideal, which is the kernel of restriction. On every affine open its image
generates the ideal. Invertibility therefore makes this section a free generator.
The morphism from the unit associated to this generator is an isomorphism; composing
it with the ideal inclusion is multiplication by the equation on every open. -/
theorem principalCartierIdealFrame (T : Scheme.{u}) (f : Γ(T, ⊤))
    (hI : (T.zeroLocusSubschemeι {f}).ker.IsInvertible) :
    ∃ φ : Modules.unit T ≅ (T.zeroLocusSubschemeι {f}).ker.toModules,
      ∀ (V : T.Opens) (r : Γ(T, V)),
        ((φ.hom ≫ (T.zeroLocusSubschemeι {f}).ker.toModulesι).app V) r =
          r * T.presheaf.map (homOfLE le_top).op f := by
  let k := T.zeroLocusSubschemeι {f}
  have hk : k.ker = IdealSheafData.ofIdealTop (Ideal.span {f}) :=
    IdealSheafData.ker_subschemeι _
  have hf : k.ker.subschemeι.app ⊤ f = 0 := by
    rw [hk]
    exact T.zeroLocusSubschemeι_appTop (Set.mem_singleton f)
  have hfmem : f ∈ Set.range (k.ker.toModulesι.app ⊤) := by
    rw [k.ker.range_toModulesι_app_eq ⊤]
    exact hf
  obtain ⟨s, hs⟩ := hfmem
  have hgen : Modules.IsFreeGenerator s := hI.isFreeGenerator s (fun V hV => by
    rw [hs, hk, IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton])
  let := Modules.isIso_homOfGlobalSection hgen
  refine ⟨asIso (Modules.homOfGlobalSection k.ker.toModules s), ?_⟩
  intro V r
  change k.ker.toModulesι.app V ((Modules.homOfGlobalSection k.ker.toModules s).app V r) = _
  rw [Modules.homOfGlobalSection_app, Modules.Hom.app_smul,
    Modules.Hom.app_presheaf_map, hs]
  rfl

end AlgebraicGeometry.Scheme
