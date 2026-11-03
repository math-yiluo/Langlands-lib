import Langlands.Cohomology.EquivariantGodementCohomology

/-! # Augmentation-compatible maps under the degree-zero Godement identification -/

noncomputable section

namespace Langlands.Cohomology.EquivariantGodementCohomology

open CategoryTheory CategoryTheory.Limits

universe uA vA uA' vA' uB vB

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A']
  {B : Type uB} [Category.{vB} B] [Abelian B]
  (T : A ⥤ A) (η : 𝟭 A ⟶ T) [∀ M : A, Mono (η.app M)]
  (T' : A' ⥤ A') (η' : 𝟭 A' ⟶ T') [∀ M : A', Mono (η'.app M)]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ]
  (Ψ : A' ⥤ B) [Ψ.Additive] [PreservesFiniteLimits Ψ]
  {M : A} {N : A'}
  (a : Φ.obj M ⟶ Ψ.obj N)
  (t : (mappedComplex T η Φ).obj M ⟶ (mappedComplex T' η' Ψ).obj N)
  (h : Φ.map (CokernelComplex.augmentation T η M) ≫ t.f 0 =
    a ≫ Ψ.map (CokernelComplex.augmentation T' η' N))

include h

/-- A chain map compatible with the actual augmentations induces the given
map of degree-zero sections, under the canonical cycles identifications. -/
@[reassoc]
theorem cyclesIso_map :
    (cyclesIso T η Φ M).hom ≫ HomologicalComplex.cyclesMap t 0 =
      a ≫ (cyclesIso T' η' Ψ N).hom := by
  rw [← cancel_mono (((mappedComplex T' η' Ψ).obj N).iCycles 0),
    Category.assoc, Category.assoc, HomologicalComplex.cyclesMap_i,
    cyclesIso_hom_iCycles, ← Category.assoc (cyclesIso T η Φ M).hom,
    cyclesIso_hom_iCycles]
  exact h

/-- Degree-zero homology of an augmentation-compatible chain map is the
original section map, using the existing canonical identification. -/
@[reassoc]
theorem homologyZeroIso_inv_map :
    (homologyZeroIso T η Φ).inv.app M ≫
        (HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) 0).map t =
      a ≫ (homologyZeroIso T' η' Ψ).inv.app N := by
  change ((cyclesIso T η Φ M).hom ≫
      ((mappedComplex T η Φ).obj M).homologyπ 0) ≫
        HomologicalComplex.homologyMap t 0 =
    a ≫ (cyclesIso T' η' Ψ N).hom ≫
      ((mappedComplex T' η' Ψ).obj N).homologyπ 0
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, cyclesIso_map T η T' η' Φ Ψ a t h, Category.assoc]

/-- The forward degree-zero identifications commute with every chain map
whose actual augmentations give the stated section map. -/
@[reassoc]
theorem homologyZeroIso_map :
    (HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) 0).map t ≫
        (homologyZeroIso T' η' Ψ).hom.app N =
      (homologyZeroIso T η Φ).hom.app M ≫ a := by
  rw [← cancel_epi ((homologyZeroIso T η Φ).inv.app M)]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [homologyZeroIso_inv_map T η T' η' Φ Ψ a t h]
  simp

end Langlands.Cohomology.EquivariantGodementCohomology
