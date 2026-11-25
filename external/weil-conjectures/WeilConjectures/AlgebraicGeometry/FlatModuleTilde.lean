/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Tensor flatness of the associated sheaf of a flat module

Source: Stacks Project, Tags 01HV and 05NE.
(blueprint: lem-pc-flat-module-tilde).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Flat stalks imply exactness of right tensoring.
Source: Stacks Project, Tag 05NE, implication from stalk flatness to sheaf flatness.
Use the natural stalk-tensor isomorphism to identify the stalks of a tensored short
complex. Flat stalks preserve its exactness, and stalkwise detection gives exactness
of the sheaf complex. Additivity then upgrades this to finite limits and colimits. -/
private theorem isFlat_of_flat_stalk (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X))
    (hflat : ∀ x : X, Module.Flat (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X x).obj F)) : SheafOfModules.IsFlat F := by
  let := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨⟨hpreadd⟩, _, _⟩ := SheafOfModules.tensorClosed X.sheaf
  let := hpreadd
  let T := tensorRight F
  have hT : T.PreservesHomology := Functor.preservesHomology_of_map_exact T (by
    intro C hC
    apply ((RingedSpace.module_stalk_exact X (C.map T).f).2.2.2.2
      (C.map T).X₃ (C.map T).f (C.map T).g (C.map T).zero).mpr
    intro x
    let S := RingedSpace.moduleStalkFunctor X x
    have := hflat x
    obtain ⟨Φ, _, hΦ⟩ := SheafOfModules.stalkTensorIso X x
    let e : (C.map T).map S ≅ (C.map S).map (tensorRight (S.obj F)) :=
      ShortComplex.isoMk (Φ C.X₁ F) (Φ C.X₂ F) (Φ C.X₃ F)
        (by simpa [S, T] using (hΦ C.X₁ F C.X₂ F C.f (𝟙 F)).symm)
        (by simpa [S, T] using (hΦ C.X₂ F C.X₃ F C.g (𝟙 F)).symm)
    have hCS := ((RingedSpace.module_stalk_exact X C.f).2.2.2.2
      C.X₃ C.f C.g C.zero).mp hC x
    exact ShortComplex.exact_of_iso e.symm
      (Module.Flat.rTensor_shortComplex_exact (S.obj F) _ hCS))
  exact ⟨T.preservesFiniteLimits_of_preservesHomology,
    T.preservesFiniteColimits_of_preservesHomology⟩

/-- The associated sheaf of a flat module on an affine scheme is tensor-flat.
Source: Stacks Project, Tags 01HV (stalks of associated sheaves) and 05NE
(flat stalks imply flatness of a sheaf of modules).
(blueprint: lem-pc-flat-module-tilde).

Proof: At every prime p of A, the stalk of the associated sheaf of M is M_p,
by the stalk-localization description of associated sheaves. Localization of
an A-flat module is flat over A_p. Tensor products of sheaves commute with
stalks, naturally in each input. Consequently an exact short complex stays
exact after tensoring on every stalk, and detection of exactness on stalks
makes the tensored sheaf complex exact. The tensor functor is additive;
Mathlib's homology-preservation criterion therefore gives preservation of
finite limits and finite colimits. The zero module and zero ring are included;
on the empty spectrum the stalkwise exactness test is vacuous. -/
theorem isFlat_tilde (A : CommRingCat.{u}) (M : ModuleCat.{u} A)
    (hflat : Module.Flat A M) : SheafOfModules.IsFlat ((tilde.functor A).obj M) := by
  apply isFlat_of_flat_stalk (Spec A).toRingedSpace
  intro x
  let : Algebra A ((Spec A).presheaf.stalk x) :=
    (StructureSheaf.toStalk A x).hom.toAlgebra
  have : IsLocalization x.asIdeal.primeCompl ((Spec A).presheaf.stalk x) :=
    inferInstanceAs (IsLocalization x.asIdeal.primeCompl
      ((structurePresheafInCommRingCat A).stalk x))
  have : IsScalarTower A ((Spec A).presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := PrimeSpectrum.Top A)
        (moduleStructurePresheaf A M).presheaf x) :=
    .of_algebraMap_smul (fun _ _ ↦ rfl)
  have := hflat
  change Module.Flat ((Spec A).presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := PrimeSpectrum.Top A)
      (moduleStructurePresheaf A M).presheaf x)
  exact Module.Flat.of_isLocalizedModule ((Spec A).presheaf.stalk x)
    x.asIdeal.primeCompl (StructureSheaf.toStalkₗ A M x)

end AlgebraicGeometry
