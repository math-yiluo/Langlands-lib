/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.Triangulated.BoundedPostnikovTower

/-! # Vanishing of bounded tensor products detected on homology factors

Source: Stacks Project, derived.tex, Tag 08J5, and sites-cohomology.tex, Tags 06YM and 06YU.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory

/-- Tensor with a flat-term K-flat complex vanishes on a bounded complex if it vanishes
on each of its homology sheaves placed in degree zero.

Source: Stacks Project, derived.tex, Tag 08J5, finite truncation triangles;
sites-cohomology.tex, Tags 06YM and 06YU, exactness and definition of derived tensor.
(auxiliary; not a blueprint node).

Proof: descend the fixed K-flat tensor to an exact functor on the derived category.
The finite ordered Postnikov tower of the bounded input has shifted homology sheaves
as factors. The computation comparison and the assumed single-module vanishing kill
those factors. Exactness kills each successive vertex, starting at zero. The final
vertex is the input, and the computation comparison returns acyclicity of the total. -/
theorem tensor_acyclic_of_bounded_homology
    {C : Type u} [SmallCategory C] {T : GrothendieckTopology C}
    (R : Sheaf T CommRingCat.{u}) (P K : ringedSiteComplex R)
    (hP : P.IsKFlatTensor)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i))
    (hbounded : ∃ a z : ℤ, ∀ i : ℤ, i < a ∨ z < i → IsZero (K.X i))
    (hH : ∀ i : ℤ, (((ringedKoszulTensor R).obj P).obj
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (K.homology i))).Acyclic) :
    (((ringedKoszulTensor R).obj P).obj K).Acyclic := by
  let A := SheafOfModules.{u}
    ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)
  let := HasDerivedCategory.standard A
  have hPf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := T) (R := R) (P.X i) := by
    intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X i)).symm (hflat i)
  have hPi := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP
  obtain ⟨s, hs⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  let := s
  obtain ⟨_, _, htri, ⟨c, _, _⟩, _⟩ := hs P hPi hPf
  let F := (SheafOfModules.KFlatFixedTensor.derivedTensor R).obj (DerivedCategory.Q.obj P)
  let : F.CommShift ℤ := s.commShiftObj _
  have : F.IsTriangulated := htri.1
  let D := DerivedCategory.Q.obj K
  obtain ⟨a, z, hb⟩ := hbounded
  let N := (z - a).toNat + 1
  have : K.IsStrictlyGE a := (K.isStrictlyGE_iff a).2
    (fun i hi ↦ hb i (Or.inl hi))
  have : K.IsStrictlyLE (a + (N : ℤ) - 1) :=
    (K.isStrictlyLE_iff _).2 (fun i hi ↦ hb i (Or.inr (by
      have hh := Int.self_le_toNat (z - a)
      dsimp [N] at hi
      omega)))
  obtain ⟨_, L, ⟨e₀⟩, ⟨eN⟩, _, f, g, δ, hdist⟩ :=
    Triangulated.TStructure.exists_bounded_postnikov_tower
      (DerivedCategory.TStructure.t (C := A)) a N D
  have hsingle (i : ℤ) : IsZero (F.obj ((DerivedCategory.singleFunctor A 0).obj
      ((DerivedCategory.homologyFunctor A i).obj D))) := by
    let e := (DerivedCategory.homologyFunctorFactors A i).app K
    have hz := (DerivedCategory.isZero_Q_obj_iff _).2 (hH i)
    have hz' : IsZero (F.obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single A (.up ℤ) 0).obj (K.homology i)))) :=
      hz.of_iso (c.app _).symm
    exact hz'.of_iso (F.mapIso ((DerivedCategory.singleFunctor A 0).mapIso e))
  have hL (j : Fin (N + 1)) : IsZero (F.obj (L j)) := by
    induction j using Fin.induction with
    | zero => exact (F.map_isZero (isZero_zero _)).of_iso (F.mapIso e₀)
    | succ j ih =>
      let i := a + (j : ℤ)
      let B := ((DerivedCategory.TStructure.t (C := A)).truncGELE i i).obj D
      obtain ⟨e⟩ := DerivedCategory.bounded_postnikov_cohomology_iso D i
      have hz : IsZero (F.obj (B⟦i⟧)) := (hsingle i).of_iso (F.mapIso e)
      have hz' : IsZero (F.obj ((B⟦i⟧)⟦-i⟧)) :=
        ((shiftFunctor _ (-i)).map_isZero hz).of_iso ((F.commShiftIso (-i)).app _)
      exact (F.mapTriangle.obj (Triangle.mk (f j) (g j) (δ j))).isZero₂_of_isZero₁₃
        (F.map_distinguished _ (hdist j)) ih hz'
  have hz : IsZero (F.obj D) := (hL (Fin.last N)).of_iso (F.mapIso eN).symm
  exact (DerivedCategory.isZero_Q_obj_iff _).1 (hz.of_iso (c.app K))

end CategoryTheory
