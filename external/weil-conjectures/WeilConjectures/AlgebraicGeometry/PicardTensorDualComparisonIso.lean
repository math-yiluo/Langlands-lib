/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCanonicalBaseChange

import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree
import WeilConjectures.AlgebraicGeometry.DualTensorHomComparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Invertibility of the canonical tensor-pullback dual comparison
Source: Stacks Project, Tags 0FNV and 01C8.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- The comparison defined by transposing pulled evaluation is invertible for a
finite locally free module.

Source: Stacks Project, Tag 0FNV, finite free dual bases; Tag 01C8,
base change of locally free sheaves.
(blueprint: lem-sc-picard-tensor-dual-comparison-iso)

Proof: The finite-locally-free dual-tensor-Hom isomorphism agrees with the
closed-category comparison. Thus the comparison at M is invertible, and
MonoidalClosed.exactPairingOfIsIso gives the canonical exact pairing of dual M
with M, whose evaluation is the internal-Hom evaluation. Transport the monoidal
structure of ordinary pullback along picardTensorComparison, and apply
ExactPairing.map. The resulting evaluation is the tensor comparison followed by
the pulled internal-Hom evaluation and the transported monoidal unit comparison.
Its transpose is an isomorphism by MonoidalClosed.curry_evaluation. The explicit
picardTensorUnitIso might use a different unit comparison; compose with the
unit automorphism obtained as the inverse transported unit map followed by this
explicit map. Its image under internal Hom is invertible. Naturality of currying
in the target identifies the resulting composite with the defined canonical
comparison. Hence that comparison is invertible as well. This argument covers
rank zero, empty schemes and arbitrary base morphisms without flatness. -/
theorem picardTensorDualComparison_isIso {W T : Scheme.{u}} (h : T ⟶ W)
    (M : W.Modules) [M.IsFiniteLocallyFree] :
    IsIso (Modules.picardTensorDualComparison h M) := by
  have : IsIso (MonoidalClosed.ihomUnitTensorToIhom M M) := by
    rw [← Modules.dualTensorHom_eq_ihomUnitTensorToIhom]
    infer_instance
  let : ExactPairing (Modules.dual M) M := MonoidalClosed.exactPairingOfIsIso M
  let : (Modules.tensorPullback h).Monoidal :=
    Functor.Monoidal.transport (Modules.picardTensorComparison h).symm
  let : ExactPairing ((Modules.tensorPullback h).obj (Modules.dual M))
      ((Modules.tensorPullback h).obj M) :=
    ExactPairing.map (Modules.tensorPullback h) (Modules.dual M) M
  let k := inv (Functor.OplaxMonoidal.η (Modules.tensorPullback h)) ≫
    (Modules.picardTensorUnitIso h).hom
  have : IsIso k := by dsimp [k]; infer_instance
  have hi : IsIso (MonoidalClosed.curry
      (ε_ ((Modules.tensorPullback h).obj (Modules.dual M))
        ((Modules.tensorPullback h).obj M)) ≫
      (ihom ((Modules.tensorPullback h).obj M)).map k) := by
    infer_instance
  rw [← MonoidalClosed.curry_natural_right] at hi
  convert hi using 1
  · rfl
  · unfold Modules.picardTensorDualComparison
    congr 1
    change _ =
      (Functor.LaxMonoidal.μ (Modules.tensorPullback h) M (Modules.dual M) ≫
        (Modules.tensorPullback h).map ((ihom.ev M).app (SheafOfModules.unit W.ringCatSheaf)) ≫
        Functor.OplaxMonoidal.η (Modules.tensorPullback h)) ≫
      (inv (Functor.OplaxMonoidal.η (Modules.tensorPullback h)) ≫
        (Modules.picardTensorUnitIso h).hom)
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [Functor.Monoidal.transport_μ]
    simp only [Modules.picardTensorObjIso, Iso.trans_inv, tensorIso_inv, Iso.symm_inv,
      Iso.app_hom, Iso.symm_hom, Functor.Monoidal.μIso_hom, Category.assoc]
    rfl

end AlgebraicGeometry.Scheme
