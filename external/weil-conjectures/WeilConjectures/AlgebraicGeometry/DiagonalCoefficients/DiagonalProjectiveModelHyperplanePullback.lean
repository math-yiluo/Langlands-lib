/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import all WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line.ProjectiveLineAutomorphismHyperplane

/-! # Hyperplane pullback for independently chosen projective-line models -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- A Cartesian inverse image of one relative hyperplane class is the other
relative hyperplane class times a line from the base.

Source: diagonal coefficients (3), the change of projective-line model; EGA II,
Remark 4.2.7 (blueprint: lem-diagonal-projective-model-hyperplane-pullback).

Proof: the Cartesian square and the old projective model identify the new total
space with the canonical projective line over the new base. Compare this model
with the independently chosen new model. Their difference is an automorphism over
the new base. Such an automorphism preserves O(1) modulo a base line. The canonical
projective-space base-change map preserves the tautological O(1), so pulling the
automorphism formula back through the new model gives the claimed factorization.
The argument also applies to disconnected, nonreduced and empty schemes. -/
theorem diagonalProjectiveModel_hyperplanePullback
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (square : IsPullback hX f' f hS)
    (m : X ≅ ProjectiveLine S) (hm : m.hom ≫ (ProjectiveLine S ↘ S) = f)
    (m' : X' ≅ ProjectiveLine S') (hm' : m'.hom ≫ (ProjectiveLine S' ↘ S') = f') :
    ∃ B : S'.Pic,
      Scheme.Pic.map hX (Scheme.Pic.map m.hom (SpTowerClasses.hyperplanePic S)) =
        Scheme.Pic.map f' B * Scheme.Pic.map m'.hom (SpTowerClasses.hyperplanePic S') := by
  let j := ProjectiveSpace.map (ULift.{u} (Fin 2)) hS
  have hp : IsPullback (hX ≫ m.hom) f' (ProjectiveLine S ↘ S) hS :=
    square.of_iso (Iso.refl X') m (Iso.refl S') (Iso.refl S)
      (by simp) (by simp) (by simpa using hm.symm) (by simp)
  let n := hp.isoIsPullback _ _ (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) hS)
  have hn : n.hom ≫ j = hX ≫ m.hom := hp.isoIsPullback_hom_fst _ _ _
  have hnp : n.hom ≫ (ProjectiveLine S' ↘ S') = f' :=
    hp.isoIsPullback_hom_snd _ _ _
  let a := m'.symm ≪≫ n
  have ha : a.hom ≫ (ProjectiveLine S' ↘ S') = (ProjectiveLine S' ↘ S') := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, hnp, ← hm', Iso.inv_hom_id_assoc]
  obtain ⟨B, hB⟩ := ProjectiveLine.automorphism_hyperplane S' a ha
  have hj : Scheme.Pic.map j (SpTowerClasses.hyperplanePic S) =
      SpTowerClasses.hyperplanePic S' := by
    change Scheme.Pic.map j (Scheme.Pic.ofIsInvertible _) = Scheme.Pic.ofIsInvertible _
    rw [ProjectiveLine.pic_map_ofIsInvertible]
    exact Scheme.Pic.ofIsInvertible_eq_of_iso
      (ProjectiveSpace.pullbackMapTwistIso (ULift.{u} (Fin 2)) hS 1)
  have hma : m'.hom ≫ a.hom = n.hom := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom]
    rw [Iso.hom_inv_id_assoc]
  refine ⟨B, ?_⟩
  rw [← Scheme.Pic.map_comp, ← hn, Scheme.Pic.map_comp, hj,
    ← hma, Scheme.Pic.map_comp]
  change Scheme.Pic.map a.hom (SpTowerClasses.hyperplanePic S') = _ at hB
  rw [hB, Scheme.Pic.map_mul, ← Scheme.Pic.map_comp, hm']
  rfl

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
