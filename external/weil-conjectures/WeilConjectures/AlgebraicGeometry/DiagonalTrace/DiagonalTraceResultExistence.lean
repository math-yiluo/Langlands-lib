/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTracePresentationExistence
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Assembling a completed trace from its presentation
Source: diagonal trace proof paragraph (1), steps 3--8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- Construct the completed trace, its strict splitting and its finite projection
identities from the normalized presentation.
Source: diagonal trace proof paragraph (1), steps 3--8
(blueprint: lem-sfb-diagonal-trace-result-existence).
Proof: exact scalar restriction preserves the biproduct, so the restricted splitting
is the image of the varying splitting composed with the inverse biproduct comparison
and the varying direct-image comparison. It is therefore invertible. Surjectivity of
completed restriction on the specified Hom set lifts sourceMap followed by Rlim of the
system trace and the inverse unitMap. Cancel unitMap to obtain IsTrace. Naturality of
each derived-limit projection gives the finite reduction equations. The finite unit
and Chern equations were supplied by the normalized presentation. -/
theorem exists_diagonalTraceResult
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (e : X ≅ ProjectiveLine S)
    (he : e.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (l : Γ(S, ⊤))) :
    ∃ t : Result l (ULift.{u} (Padic l)) f, t.model.model = e := by
  obtain ⟨p, hp, hs, hu, hc, hfull⟩ := exists_diagonalTracePresentation l f e he hS
  have := hs
  have := p.unit_limit
  let E := ULift.{u} (Padic l)
  let F := p.restrictionS.F.mapDerivedCategory
  have : F.Additive := inferInstance
  have : F.PreservesZeroMorphisms := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hsplit : IsIso (p.splitting l E) := by
    have heq : p.splitting l E =
        (F.mapBiprod
          (SpTowerClasses.unit S (SpTowerClasses.Arings l E S))
          ((SpTowerClasses.inverseLine l E p.chernS)⟦(-2 : ℤ)⟧)).inv ≫
          F.map (p.model.bq l E) ≫ p.varying.hom.app _ := by
      dsimp only [Presentation.splitting, Model.bq, F]
      rw [← Category.assoc]
      congr 1
      exact (biprod.mapBiprod_inv_map_desc F _ _
        (SpTowerClasses.unitArrow l E p.model.coefficientPullback)
        (p.model.second l E)).symm
    rw [heq]
    infer_instance
  obtain ⟨t, ht⟩ := hfull.2
    (p.sourceMap l E ≫ p.LS.R.map (p.systemTrace l E) ≫
      inv (p.coefficientsS.unitMap l E p.LS))
  dsimp only at ht
  have htrace' : (diagonalCompletedUnderlying l S).map t ≫
      p.coefficientsS.unitMap l E p.LS =
        p.sourceMap l E ≫ p.LS.R.map (p.systemTrace l E) := by
    rw [ht]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have htrace : p.IsTrace l E t := by
    simpa only [Presentation.IsTrace, Presentation.sourceMap, Category.assoc] using htrace'
  refine ⟨{ toPresentation := p
            split := hs
            strict_split := hsplit
            trace := t
            construction := htrace
            reductions := ?_
            torsion_unit := hu
            torsion_chern := hc }, hp⟩
  intro n
  change (diagonalCompletedUnderlying l S).map t ≫
      p.coefficientsS.unitMap l E p.LS ≫ _ = _
  rw [← Category.assoc, htrace']
  simpa only [Category.assoc] using congrArg
    (fun k ↦ p.sourceMap l E ≫ k)
    ((p.LS.projection n).naturality (p.systemTrace l E))

end AlgebraicGeometry.ProEtale.DiagonalTrace
