/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import WeilConjectures.AlgebraicGeometry.TensorUnitOpenLocalization
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Units on finite locally free modules

Source: Stacks Project, Tags 0BDP and 01E8.
(blueprint: lem-sc-finite-locally-free-tensor-unit)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem isIso_app_coproduct {C : Type*} [Category C] {I : Type*}
    [HasCoproductsOfShape I C] (H : C ⥤ C)
    [PreservesColimitsOfShape (Discrete I) H] (α : 𝟭 C ⟶ H)
    (O : C) [IsIso (α.app O)] : IsIso (α.app (∐ fun _ : I ↦ O)) := by
  have h : α.app (∐ fun _ : I ↦ O) =
      CategoryTheory.Limits.Sigma.map (fun _ : I ↦ α.app O) ≫
        (PreservesCoproduct.iso H (fun _ : I ↦ O)).inv := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_map_assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
    exact α.naturality (Sigma.ι (fun _ : I ↦ O) i)
  rw [h]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The tensor-pullback adjunction unit is invertible on finite locally free modules
when it is invertible on the structure module.
Source: Stacks Project, Tag 01E8, degree-zero projection formula and its local proof;
Tag 0BDP, projection-formula paragraph.
(blueprint: lem-sc-finite-locally-free-tensor-unit)

Proof: Cover Y by opens U on which N is free with a finite basis of size r. Direct
image restricts to the full inverse image of U, and tensor pullback along U's inclusion
is restriction. The defining section formula for the chosen adjunction unit is
m ↦ 1 ⊗ m. Both tensor pullback and direct image preserve finite direct sums, so in
these coordinates the unit at N is the direct sum of r copies of the restricted
unit at O_Y. The latter is an isomorphism by hypothesis. Hence the unit at N is
invertible on each U, and inverses glue by uniqueness. For r = 0 the unit is the
identity of the zero object. If Y is empty, the assertion is vacuous locally. -/
theorem isIso_tensorPullback_unit_of_finiteLocallyFree {X Y : Scheme.{u}}
    (p : X ⟶ Y)
    (hO : IsIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction p)).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)))
    (N : Y.Modules) [N.IsFiniteLocallyFree] :
    IsIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction p)).unit.app N) := by
  classical
  obtain ⟨q, hfree, hfinite⟩ :=
    SheafOfModules.IsFiniteLocallyFree.exists_localGeneratorsData (M := N)
  let := hfree
  let := hfinite
  let η := (Classical.choose (Modules.exists_tensorPullbackAdjunction p)).unit
  let := hO
  have hlocal (i : q.I) : IsIso ((η.app N).over (q.X i)) := by
    have := hfinite.isFiniteType i
    let := Fintype.ofFinite (q.generators i).I
    let e := asIso (q.generators i).π
    obtain ⟨H, α, θ, hH, hθ⟩ := tensorPullback_unit_open_localization p (q.X i)
    let := hH
    let O := SheafOfModules.unit Y.ringCatSheaf
    have hunit : IsIso ((η.app O).over (q.X i)) :=
      (SheafOfModules.overFunctor Y.ringCatSheaf (q.X i)).map_isIso _
    have hαunit : IsIso (α.app (O.over (q.X i))) := by
      have : IsIso (α.app (O.over (q.X i)) ≫ θ.hom.app O) :=
        hθ O ▸ hunit
      exact IsIso.of_isIso_comp_right _ (θ.hom.app O)
    have hαfree : IsIso (α.app (SheafOfModules.free
        (R := Y.ringCatSheaf.over (q.X i)) (q.generators i).I)) :=
      isIso_app_coproduct H α (O.over (q.X i))
    have : IsIso (α.app (N.over (q.X i))) :=
      (NatTrans.isIso_app_iff_of_iso α e).mp hαfree
    exact (hθ N).symm ▸ inferInstance
  have : IsIso ((SheafOfModules.toSheaf Y.ringCatSheaf).map (η.app N)) := by
    apply Sheaf.isIso_of_coversTop q.coversTop
    intro i
    have := hlocal i
    change IsIso ((SheafOfModules.toSheaf (Y.ringCatSheaf.over (q.X i))).map
      ((η.app N).over (q.X i)))
    infer_instance
  have : (SheafOfModules.toSheaf Y.ringCatSheaf ⋙
      sheafToPresheaf _ _).ReflectsIsomorphisms :=
    inferInstanceAs (Modules.toPresheaf Y).ReflectsIsomorphisms
  have : (SheafOfModules.toSheaf Y.ringCatSheaf).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_comp _ (sheafToPresheaf _ _)
  exact isIso_of_reflects_iso (η.app N) (SheafOfModules.toSheaf Y.ringCatSheaf)

end AlgebraicGeometry.Scheme
