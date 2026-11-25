/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Constant pullback identity coherence

Source: Stacks Project, sites.tex, Tag 03CB; cohomology.tex, Tag 01F8.
(blueprint: lem-weil-pbc-constant-pullback-identity-coherence)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Constant-sheaf comparison for identity inverse image is the inverse of upperStarId.
Source: Stacks Project, sites.tex, Tag 03CB, and cohomology.tex, Tag 01F8.

Proof: constantSheaf followed by inverse image of the identity is left adjoint to
sections composed with identity direct image. Transport along lowerStarId identifies
this adjunction with constantSheaf adjoint to sections. The definition of upperStarId
is the conjugate of the inverse of lowerStarId, while upperStarConstantSheafIso is
uniqueness of the same left adjoint. Hence their composite is the identity comparison,
by uniqueness of left-adjoint isomorphisms compatible with the adjunction units.
Taking its component at M gives the displayed equality of sheaf morphisms.
(blueprint: lem-weil-pbc-constant-pullback-identity-coherence)
-/
theorem constantPullbackIdentityCoherence (Z : Scheme.{u}) (M : AddCommGrpCat.{u + 1}) :
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (𝟙 Z)).inv.app M ≫
        (upperStarId AddCommGrpCat.{u + 1} Z).hom.app
          ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) = 𝟙 _ := by
  let adj := constantSheafAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal
  let adjId := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (𝟙 Z)
  let e := lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} (𝟙 Z)
  have h : (upperStarId AddCommGrpCat.{u + 1} Z).hom.app
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (𝟙 Z)).hom.app M := by
    apply (((adj.comp adjId).ofNatIsoRight e).homEquiv M _).injective
    change _ = (((adj.comp adjId).ofNatIsoRight e).homEquiv M _)
      ((((adj.comp adjId).ofNatIsoRight e).leftAdjointUniq adj).hom.app M)
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change adj.homEquiv M _ (adjId.homEquiv _ _
      ((upperStarId AddCommGrpCat.{u + 1} Z).hom.app
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M))) ≫
      e.hom.app _ = _
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    dsimp only [adjId]
    rw [upperStarId_hom_app_unit_app]
    have ht : PreservesTerminal.iso (Scheme.Hom.Etale (𝟙 Z)) =
        (MorphismProperty.Over.pullbackId @Etale ⊤ Z).app (⊤_ Z.Etale) := by
      apply Iso.ext
      exact terminalIsTerminal.hom_ext _ _
    simp [e, lowerStarCompSheafSectionsTerminalIso, lowerStarId,
      GrothendieckTopology.lowerStarId, ht, ← Functor.map_comp, ← op_comp]
  rw [h]
  exact (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (𝟙 Z)).inv_hom_id_app M

end AlgebraicGeometry.Etale
