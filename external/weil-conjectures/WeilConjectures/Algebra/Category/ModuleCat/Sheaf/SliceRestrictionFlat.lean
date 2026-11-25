/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-!
# Flatness under restriction to a slice site

Source: Stacks Project, Modules on Sites, Tag 0E8J, Lemma `lemma-restriction-flat`
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

/-- Restricting a flat module sheaf to the slice site over any object preserves flatness.
Source: Stacks Project, Modules on Sites, Tag 0E8J, Lemma `lemma-restriction-flat`
(auxiliary; not a blueprint node).

Proof:
1. Given an exact three-term complex of modules on the slice, extend it by the
   sheafified direct-sum extension by zero. The forward direction of
   `lem-weil-pbc-ringed-slice-extension-exactness` makes this an exact complex on the site.
2. Tensor that extended complex with `F`. It stays exact by `hF`, namely exactness of
   tensoring with `F` in `def-pc-flat-sheaf-modules`.
3. The natural tensor isomorphisms of `lem-weil-pbc-ringed-slice-extension-tensor`
   identify this complex with the extension by zero of the original complex tensored
   with `F.over U`. Naturality identifies the arrows as well as the objects.
4. The reverse direction of `lem-weil-pbc-ringed-slice-extension-exactness` now shows
   that the tensor complex on the slice is exact. This applies to every three-term
   exact complex, including complexes with a zero end term, so tensoring with `F.over U`
   is exact, which is its flatness by `def-pc-flat-sheaf-modules`. -/
theorem isFlat_over
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : C) (hF : IsFlat F) : IsFlat (R := R.over U) (F.over U)  := by
  let _ := SheafOfModules.monoidalCategory R
  let _ : MonoidalCategory (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) :=
    SheafOfModules.monoidalCategory (R.over U)
  let _ : SymmetricCategory (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) :=
    SheafOfModules.symmetricCategory (R.over U)
  refine (exactFunctor_iff _).2 ⟨?_, ?_⟩
  · exact isFlat_over_preservesFiniteLimits F U hF
      (SheafOfModules.monoidalCategory (R.over U)) rfl
  · obtain ⟨_, ⟨closed⟩, _⟩ := SheafOfModules.tensorClosed (R.over U)
    let _ : MonoidalClosed (SheafOfModules.{u}
        ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) := closed
    exact preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)

end SheafOfModules
