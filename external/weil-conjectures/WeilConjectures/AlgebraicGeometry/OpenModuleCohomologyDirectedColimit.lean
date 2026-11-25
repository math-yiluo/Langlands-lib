/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Topology.Bases
public import Mathlib.Topology.QuasiSeparated
public import WeilConjectures.Topology.OpenModuleCohomology
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FilteredColimitSuccessor
import WeilConjectures.Topology.AbelianSectionsFilteredColimit
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import WeilConjectures.Topology.TopologicalFilteredCohomology
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.RightDerivedExactComposite
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Directed colimits and module cohomology on quasi-compact opens

Source: Stacks Project, Cohomology, Lemma 20.19.1, Tag 01FF
(blueprint: lem-weil-pbc-qs-scheme-cohomology-directed-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- On a scheme with a basis of quasi-compact opens stable under binary intersection,
every cohomology class on a quasi-compact open comes from a stage of a directed system,
and a stage class with zero image vanishes at a later stage. Equivalently, the canonical
map from the directed colimit of cohomology groups is bijective.

Source: Stacks Project, Cohomology, Lemma 20.19.1, Tag 01FF
(blueprint: lem-weil-pbc-qs-scheme-cohomology-directed-colimit).

Proof:
1. Translate the compact-open basis and quasi-separatedness into the hypotheses of
   abelianSections_preservesDirectedColimits. The forgetful functor from module
   sheaves to abelian sheaves preserves colimits, so open module sections do too.
2. Induct on the right-derived degree. At zero use rightDerivedZeroIsoSelf. The
   existing preservesColimitsOfShape_rightDerived_succ packages the injective
   embedding, exact colimit sequence, and natural connecting-map ladder.
3. For its acyclicity premise, apply topological_filtered_cohomology to the underlying
   abelian sheaves of an injective module diagram. Each stage has zero positive
   object cohomology by injective_module_abelian_acyclic, so its cohomology colimit is
   zero. The forgetful functor preserves the original module colimit cocone.
4. Identify object cohomology with derived abelian sections. The exact-composite
   comparison exists_rightDerived_exact_comp_iso identifies these with module-derived
   sections: the same injective-module vanishing verifies its acyclicity premise.
5. Preservation now makes the image of the given cocone a colimit in abelian groups.
   The concrete filtered-colimit API gives stage representatives and eventual equality
   with zero. A transition arrow in the preorder is homOfLE of its underlying inequality.
The empty open, degree zero, and non-antisymmetric directed preorders are included. -/
theorem openModuleCohomology_directedColimit (X : Scheme.{u})
    (hBasis : IsTopologicalBasis {V : Set X | IsOpen V ∧ IsCompact V})
    [QuasiSeparatedSpace X]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (c : Cocone D) (hc : IsColimit c) (U : Opens X) (hU : IsCompact (U : Set X))
    (q : ℕ) :
    (∀ x : (RingedSpace.openModuleCohomology X.toRingedSpace q U).obj c.pt,
      ∃ (i : I) (y : (RingedSpace.openModuleCohomology X.toRingedSpace q U).obj (D.obj i)),
        ((RingedSpace.openModuleCohomology X.toRingedSpace q U).map (c.ι.app i)).hom y = x) ∧
    (∀ (i : I) (y : (RingedSpace.openModuleCohomology X.toRingedSpace q U).obj (D.obj i)),
      ((RingedSpace.openModuleCohomology X.toRingedSpace q U).map (c.ι.app i)).hom y = 0 →
      ∃ (j : I) (hij : i ≤ j),
        ((RingedSpace.openModuleCohomology X.toRingedSpace q U).map
          (D.map (homOfLE hij))).hom y = 0) := by
  have hbas : ∀ (V : Set X), IsOpen V → ∀ x ∈ V,
      ∃ W : Set X, IsOpen W ∧ IsCompact W ∧ x ∈ W ∧ W ⊆ V := by
    intro V hV x hx
    obtain ⟨W, hW, hxW, hWV⟩ := hBasis.exists_subset_of_mem_open hx hV
    exact ⟨W, hW.1, hW.2, hxW, hWV⟩
  have hint : ∀ (V W : Set X), IsOpen V → IsOpen W → IsCompact V →
      IsCompact W → IsCompact (V ∩ W) := by
    intro V W hV hW hVc hWc
    exact hVc.inter_of_isOpen hWc hV hW
  let Γ := RingedSpace.openModuleSections X.toRingedSpace U
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U)
  have : PreservesColimitsOfShape I E :=
    TopCat.abelianSections_preservesDirectedColimits X hbas hint I U hU
  have : PreservesColimitsOfShape I Γ :=
    inferInstanceAs (PreservesColimitsOfShape I (T ⋙ E))
  have : PreservesFiniteLimits Γ :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.toPresheaf (moduleRings X.toRingedSpace).obj ⋙
          (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U)))
  have : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  have hderived (n : ℕ) : PreservesColimitsOfShape I (Γ.rightDerived n) := by
    induction n with
    | zero =>
        exact preservesColimitsOfShape_of_natIso Γ.rightDerivedZeroIsoSelf.symm
    | succ n hn =>
        have := hn
        apply Γ.preservesColimitsOfShape_rightDerived_succ I n
        intro J hJ
        let C := Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) (n + 1) ⋙
          (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U)
        have : IsIso (colimit.post (J ⋙ T) C) :=
          TopCat.topological_filtered_cohomology X hbas hint I (J ⋙ T) (n + 1) U hU
        have : PreservesColimit (J ⋙ T) C := preservesColimit_of_isIso_post C (J ⋙ T)
        have hz : IsZero (C.obj (T.obj (colimit J))) := by
          apply (isColimitOfPreserves C
            (isColimitOfPreserves T (colimit.isColimit J))).isZero_pt
          apply Functor.isZero
          intro i
          have : Injective (J.obj i) := hJ i
          have : Subsingleton (Sheaf.H'.{u} (T.obj (J.obj i)) (n + 1) U) :=
            injective_module_abelian_acyclic U (J.obj i) (n + 1) (Nat.succ_pos n)
          change IsZero (Sheaf.H'.{u} (T.obj (J.obj i)) (n + 1) U)
          exact AddCommGrpCat.isZero_of_subsingleton _
        obtain ⟨e⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
          (Opens.grothendieckTopology X) U (n + 1)
        have hac : ∀ M, Injective M → E.rightAcyclic (T.obj M) := by
          intro M hM k
          have : Injective M := hM
          have : Subsingleton (Sheaf.H'.{u} (T.obj M) (k + 1) U) :=
            injective_module_abelian_acyclic U M (k + 1) (Nat.succ_pos k)
          obtain ⟨d⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
            (Opens.grothendieckTopology X) U (k + 1)
          have hzM : IsZero (Sheaf.H'.{u} (T.obj M) (k + 1) U) :=
            AddCommGrpCat.isZero_of_subsingleton _
          exact hzM.of_iso (d.app (T.obj M)).symm
        have : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
          (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
        obtain ⟨d, _⟩ := Functor.exists_rightDerived_exact_comp_iso T E hac (colimit J) (n + 1)
        exact (hz.of_iso (e.app (T.obj (colimit J))).symm).of_iso d
  have : PreservesColimitsOfShape I
      (RingedSpace.openModuleCohomology X.toRingedSpace q U) := hderived q
  let H := RingedSpace.openModuleCohomology X.toRingedSpace q U
  have hH := isColimitOfPreserves H hc
  constructor
  · intro x
    exact Concrete.isColimit_exists_rep (D ⋙ H) hH x
  · intro i y hy
    have he : H.map (c.ι.app i) y = H.map (c.ι.app i) 0 := by
      simpa only [map_zero] using hy
    obtain ⟨j, f, g, hj⟩ :=
      (Concrete.isColimit_rep_eq_iff_exists (D ⋙ H) hH y 0).mp he
    refine ⟨j, f.le, ?_⟩
    change (H.map (D.map f)).hom y = (H.map (D.map g)).hom 0 at hj
    have hf : f = homOfLE f.le := Subsingleton.elim _ _
    simpa only [Functor.comp_map, map_zero, hf] using hj

end AlgebraicGeometry
