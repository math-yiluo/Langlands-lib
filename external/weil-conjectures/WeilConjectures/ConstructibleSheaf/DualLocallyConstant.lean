/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.ConstructibleSheaf.FiniteConstantModel
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
import WeilConjectures.ConstructibleSheaf.ConstantFiniteDual

/-! # Local constancy of coefficient duals -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
variable {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

/-- The coefficient dual of a finite locally constant sheaf is locally constant.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`, the docstring of
`IsFiniteLocallyConstantSheaf.ihom_unit`, local trivialization argument.

Proof: Choose an étale cover trivializing F. Discard empty members. On a nonempty member
F is the constant sheaf associated to a module M. A geometric stalk identifies M with a
stalk of F, so M is finitely generated. Since Λ is noetherian, choose a finite presentation
Λᵐ → Λⁿ → M → 0. Constant sheafification is exact and monoidal, so this presents the
restriction of F by finite free constant sheaves. Internal Hom into the unit is left exact:
its restriction is the kernel of the transposed map Λⁿ → Λᵐ. That map is constant and its
kernel is the constant sheaf associated to Hom_Λ(M, Λ), since constant sheafification
preserves finite limits. Restriction to a slice commutes with internal Hom, by the local
characterization of internal Hom through maps from restricted sheaves. Hence the same
cover trivializes the coefficient dual. Empty members impose no condition.

(blueprint: lem-weil-pbc-flc-dual-locally-constant) -/
theorem IsFiniteLocallyConstantSheaf.ihom_unit_locallyConstant
    (hF : IsFiniteLocallyConstantSheaf F) :
    IsLocallyConstantSheaf ((ihom F).obj (𝟙_ _)) := by
  obtain ⟨d⟩ := hF.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
  let A := ModuleCat.{u + 1} Λ
  refine ⟨⟨⟨d.cover, fun i ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  let f := d.cover.f i
  have : Etale f := d.cover.map_prop i
  have hc : ((Etale.upperStar A f).obj F).IsConstant (d.cover.X i).smallEtaleTopology :=
    (isConstant_over_iff_upperStar A (d.cover.etalePrecoverageToEtale i) F).mp
      (d.isConstant i)
  let := hF.toIsFiniteSheaf
  have hf := IsFiniteSheaf.upperStar f F
  obtain ⟨M, hM, ⟨eM⟩⟩ := exists_finite_constant_model _ hc hf
  let := hM
  have := Etale.isIso_ihomComparison_upperStar A f F
  let eH := asIso ((Functor.LaxMonoidal.ihomComparison
    (Etale.upperStar A f) F).app (𝟙_ _))
  obtain ⟨eD⟩ := nonempty_constant_finite_dual_iso (d.cover.X i) M
  exact Sheaf.isConstant_of_iso _
    (eH ≪≫ (ihom ((Etale.upperStar A f).obj F)).mapIso
        (Functor.Monoidal.εIso (Etale.upperStar A f)).symm ≪≫
      (MonoidalClosed.internalHom.mapIso eM.symm.op).app (𝟙_ _) ≪≫ eD)

end AlgebraicGeometry.Scheme
