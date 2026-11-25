/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.LinearAlgebra.MatrixRankFieldExtension
import WeilConjectures.AlgebraicGeometry.Modules.ConstantRankMapNormalFormNonempty

/-! # Local block normal form of a constant rank sheaf map
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- A constant rank map on an open part of a reduced scheme is locally a projection
followed by an inclusion, in finite free bases. -/
theorem exists_local_normal_form_of_constantRank
    {Y Z : Scheme.{u}} [IsReduced Y] {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ)
    (hrank : ∀ z : Z, ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y),
      Set.range g.base = {j.base z} ∧
      ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).map g.appTop).rank = a) :
    ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      ∃ (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
          free (ULift.{u} (Fin (m - a))) ⊞ free (ULift.{u} (Fin a)))
        (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
          free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a)))),
        (restrictFunctor U.ι).map ((Modules.pullback j).map φ) =
          eS.hom ≫ biprod.snd ≫ biprod.inl ≫ eT.inv := by
  classical
  by_cases hZ : Nonempty Z
  · exact @exists_local_normal_form_of_constantRank_nonempty Y Z inferInstance hZ M N m n
      eM eN φ j inferInstance a hrank
  · have h : IsEmpty Z := ⟨fun z => hZ ⟨z⟩⟩
    intro z
    exact h.elim z

end AlgebraicGeometry.Scheme.Modules
