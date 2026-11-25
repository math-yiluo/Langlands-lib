/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkMapEquality

/-! # Finitely many equations of maps between finite free sheaves

Source: lemma-coherent-base-change-invertible-sheaves--3, finite matrix calculation, expanded in
lem-pc-finite-free-stalk-degreewise-shrink, steps 1 and 2.
(blueprint: lem-pc-finite-free-stalk-finite-equations)
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private lemma restrict_eq_trans {Y : Scheme.{u}} {U V W : Y.Opens}
    (hWV : W ≤ V) (hVU : V ≤ U) {M N : U.toScheme.Modules} (f g : M ⟶ N)
    (hfg : (restrictFunctor (Y.homOfLE hVU)).map f =
      (restrictFunctor (Y.homOfLE hVU)).map g) :
    (restrictFunctor (Y.homOfLE (hWV.trans hVU))).map f =
      (restrictFunctor (Y.homOfLE (hWV.trans hVU))).map g := by
  let e := restrictFunctorCongr (Y.homOfLE_homOfLE hWV hVU).symm ≪≫
    restrictFunctorComp (Y.homOfLE hWV) (Y.homOfLE hVU)
  apply (cancel_mono (e.hom.app N)).mp
  rw [e.hom.naturality f, e.hom.naturality g]
  change e.hom.app M ≫ (restrictFunctor (Y.homOfLE hWV)).map
      ((restrictFunctor (Y.homOfLE hVU)).map f) = _
  rw [hfg]
  rfl

/-- Finitely many equations of module maps between finite free sheaves hold near a point
if they hold after pullback to its stalk scheme.

Source: lemma-coherent-base-change-invertible-sheaves--3, finite matrix calculation, expanded in
lem-pc-finite-free-stalk-degreewise-shrink, steps 1 and 2.

Proof: Induct over the finite set of indices, starting with U for the empty set.
Given a neighbourhood V where the previous maps agree, zero sources or targets
have only one map, so keep V. Otherwise restrict the source's finite free
isomorphism to U and apply exists_restrict_eq_of_pullback_eq with the additional
neighbourhood V. It supplies W contained in V where the new pair of maps agrees.
Equality for the previous pairs persists on W: the natural restriction-composition
isomorphism identifies direct restriction to W with restriction to V followed by
restriction to W, and the latter preserves equality. Thus the enlarged family
agrees on W. Apply the induction to all indices. Rank zero is included in the
single-map lemma, and an empty indexing type returns U.
(blueprint: lem-pc-finite-free-stalk-finite-equations) -/
theorem exists_shrink_finite_free_map_eq
    {Y : Scheme.{u}} {ι : Type v} [Finite ι] (A B : ι → Y.Modules)
    (hA : ∀ i, IsZero (A i) ∨ ∃ s : ℕ, Nonempty
      (A i ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (hB : ∀ i, IsZero (B i) ∨ ∃ s : ℕ, Nonempty
      (B i ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y) (U : Y.Opens) (hyU : y ∈ U)
    (f g : ∀ i, (restrictFunctor U.ι).obj (A i) ⟶
      (restrictFunctor U.ι).obj (B i))
    (h : ∀ i, (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (f i) =
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (g i)) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (hVU : V ≤ U),
      ∀ i, (restrictFunctor (Y.homOfLE hVU)).map (f i) =
        (restrictFunctor (Y.homOfLE hVU)).map (g i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have shrink (s : Finset ι) :
      ∃ (V : Y.Opens) (_ : y ∈ V) (hVU : V ≤ U),
        ∀ i ∈ s, (restrictFunctor (Y.homOfLE hVU)).map (f i) =
          (restrictFunctor (Y.homOfLE hVU)).map (g i) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨U, hyU, le_rfl, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨V, hyV, hVU, hV⟩ := ih
      rcases hB i with hz | _hfree
      · refine ⟨V, hyV, hVU, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact congrArg ((restrictFunctor (Y.homOfLE hVU)).map)
            (((restrictFunctor U.ι).map_isZero hz).eq_of_tgt (f j) (g j))
        · exact hV j hj
      · rcases hA i with hz | ⟨r, ⟨e⟩⟩
        · refine ⟨V, hyV, hVU, ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact congrArg ((restrictFunctor (Y.homOfLE hVU)).map)
              (((restrictFunctor U.ι).map_isZero hz).eq_of_src (f j) (g j))
          · exact hV j hj
        · obtain ⟨W, hWV, hyW, hW⟩ := exists_restrict_eq_of_pullback_eq
            r y U hyU ((restrictFunctor U.ι).obj (A i))
            ((restrictFunctor U.ι).obj (B i))
            ⟨(restrictFunctor U.ι).mapIso e⟩ (f i) (g i) (h i) V hVU hyV
          refine ⟨W, hyW, hWV.trans hVU, ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hW
          · exact restrict_eq_trans hWV hVU (f j) (g j) (hV j hj)
  obtain ⟨V, hyV, hVU, hV⟩ := shrink Finset.univ
  exact ⟨V, hyV, hVU, fun i ↦ hV i (Finset.mem_univ i)⟩

end AlgebraicGeometry.Scheme.Modules
