/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A bounded-above complex representative can be replaced by a termwise flat one.
Source: Stacks Project, Tag 077J.
(blueprint: new-pc-bounded-above-model-flat-replacement).
Apply the functorial bounded-above flat replacement to a good truncation of the
representative; its augmentation is a quasi-isomorphism, hence induces the
required isomorphism in the derived category. -/
theorem exists_flat_model_of_boundedAbove_model
    {B : Scheme.{u}}
    [hB : HasDerivedCategory (SheafOfModules.{u} (moduleRings B.toRingedSpace))]
    [hBM : HasDerivedCategory B.Modules]
    (E : schemeDerivedCategory B)
    (h : ∃ K : CochainComplex (SheafOfModules.{u} (moduleRings B.toRingedSpace)) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) ∧
      Nonempty (E ≅
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) :
    ∃ K : CochainComplex (SheafOfModules.{u} (moduleRings B.toRingedSpace)) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) ∧
      Nonempty (E ≅
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) := by
  obtain ⟨K, ⟨b, hb⟩, ⟨e⟩⟩ := h
  let _ := hBM
  let J := Opens.grothendieckTopology
    (B.toRingedSpace.toPresheafedSpace.carrier)
  let A := SheafOfModules.{u} (moduleRings B.toRingedSpace)
  let P : ObjectProperty (CochainComplex A ℤ) :=
    fun F => ∀ i : ℤ, b < i → IsZero (F.X i)
  let R0 : CategoryTheory.Sheaf J CommRingCat :=
    ⟨B.toRingedSpace.presheaf, B.toRingedSpace.IsSheaf⟩
  obtain ⟨Q, ε, hQ⟩ := CochainComplex.exists_functorial_boundedAbove_flat_replacement
    J R0 b
  let F : P.FullSubcategory := ⟨K, hb⟩
  let L := Q.obj F
  let q := (HomotopyCategory.quotient A (.up ℤ)).map (ε.app F)
  have hq : IsIso (DerivedCategory.Qh.map q) := by
    apply (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) (ε.app F)).2
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso A (ε.app F)).2 (hQ F).2.2.2
  refine ⟨L, ⟨b, ?_⟩, (hQ F).1, ?_⟩
  · intro i hi
    exact (hQ F).2.1 i hi
  · refine ⟨e.trans (asIso (DerivedCategory.Qh.map q)).symm⟩

end AlgebraicGeometry
