/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import WeilConjectures.AlgebraicGeometry.Modules.ConstantRankMapKernelImage
import WeilConjectures.AlgebraicGeometry.Modules.LocallySplitShortComplexHomology

/-! # Homology of a complex with constant differential ranks over a reduced scheme
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- Constant ranks of the two adjacent differentials over a reduced scheme imply finite
local freeness of the homology on an open subscheme. It suffices to test each point over
one field extension of its residue field. -/
theorem isFiniteLocallyFreeOfRank_homology_pullback_of_constantRank
    {Y Z : Scheme.{u}} [IsReduced Y] {P : CochainComplex Y.Modules ℤ} {r : ℤ → ℕ}
    (e : ∀ n, P.X n ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r n))))
    (q : ℤ) (j : Z ⟶ Y) [IsOpenImmersion j] (a b : ℕ)
    (hrank : ∀ z : Z, ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y),
      Set.range g.base = {j.base z} ∧
      ((freeMatrix ((e q).inv ≫ P.d q (q + 1) ≫ (e (q + 1)).hom)).map g.appTop).rank = a ∧
      ((freeMatrix ((e (q - 1)).inv ≫ P.d (q - 1) q ≫ (e q).hom)).map g.appTop).rank = b) :
    ((((Modules.pullback j).mapHomologicalComplex _).obj P).homology q).IsFiniteLocallyFreeOfRank
       (r q - a - b) := by
  let Q := ((Modules.pullback j).mapHomologicalComplex _).obj P
  let S := Q.sc' (q - 1) q (q + 1)
  obtain ⟨hkernel, _, _⟩ :=
    kernel_image_pullback_of_constantRank (e q) (e (q + 1)) (P.d q (q + 1)) j a (by
      intro z
      obtain ⟨R, hR, g, hg, ha, _⟩ := hrank z
      exact ⟨R, hR, g, hg, ha⟩)
  obtain ⟨_, himage, hsplit⟩ :=
    kernel_image_pullback_of_constantRank (e (q - 1)) (e q) (P.d (q - 1) q) j b (by
      intro z
      obtain ⟨R, hR, g, hg, _, hb⟩ := hrank z
      exact ⟨R, hR, g, hg, hb⟩)
  have : S.homology.IsFiniteLocallyFreeOfRank (r q - a - b) :=
    isFiniteLocallyFreeOfRank_homology_of_locally_split_image S (r q - a) b
      hkernel himage hsplit
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (Q.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).symm

end AlgebraicGeometry.Scheme.Modules
