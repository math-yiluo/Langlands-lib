/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
import WeilConjectures.Topology.Sheaves.CechFlasque

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-! # Injective modules are Čech-acyclic on open covers

Source: literature/stacks-project/cohomology.tex, Lemma 01EP.
(blueprint: lem-weil-pbc-module-injective-open-cover-cech-acyclic)
-/

set_option linter.unusedVariables false in
/-- An injective sheaf of `𝒪_X`-modules has vanishing positive Čech cohomology for
any open covering of any open subscheme.

Source: Stacks Project, Cohomology of Sheaves, Lemma 01EP.
(blueprint: lem-weil-pbc-module-injective-open-cover-cech-acyclic)
-/
theorem module_injective_open_cover_cech_acyclic {X : Scheme.{u}}
    (I : X.Modules) [Injective I] (U : X.Opens) (ι : Type w)
    (V : ι → X.Opens) (hV : ∀ i, V i ≤ U) (hcover : ⨆ i, V i = U)
    (S : CategoryTheory.SiteCechComplex V (fun i => homOfLE (hV i))) :
    ∀ p : ℕ, 0 < p →
      IsZero ((S.cohomologyFunctor p).obj
        (((PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
            isTerminalTop.op).obj
          ((SheafOfModules.forget X.ringCatSheaf).obj I)) ⋙
            (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat))) := by
  let S₀ : SiteCechComplex V (fun i => homOfLE (hV i)) :=
    { W := fun p t ↦ ⨅ k : Fin (p + 1), V (t k)
      pr := fun _ t k ↦ homOfLE (iInf_le (fun k ↦ V (t k)) k)
      comm := fun _ _ _ ↦ Subsingleton.elim _ _
      universal := by
        intro p t Z a _
        refine ⟨homOfLE (le_iInf fun k ↦ leOfHom (a k)), ?_, ?_⟩
        · intro k; exact Subsingleton.elim _ _
        · intro b _; exact Subsingleton.elim _ _
      W_zero := by intro t; simp
      pr_zero := fun _ ↦ Subsingleton.elim _ _
      indexMap := fun t α ↦ homOfLE
        (le_iInf fun k ↦ iInf_le (fun k ↦ V (t k)) (α k))
      indexMap_pr := fun _ _ _ ↦ Subsingleton.elim _ _ }
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj I
  have : TopCat.Presheaf.IsFlasque F.obj := isFlasque_of_injective I
  intro p hp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have he := TopCat.Sheaf.exactAt_cechComplex_of_isFlasque V q F
  have he₀ : (S₀.complex F.obj).ExactAt (q + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    intro c hc
    change (S₀.complex F.obj).d (q + 1) ((q + 1) + 1) c = 0 at hc
    simp only [SiteCechComplex.complex, CochainComplex.of_d] at hc
    change S₀.differentialValue F.obj (q + 1) c = 0 at hc
    have hc' : ((TopCat.Presheaf.cechComplex V).obj F.obj).d
        (q + 1) (q + 2) c = 0 := by
      funext t
      rw [TopCat.Presheaf.cechComplex_d_apply]
      simpa only [SiteCechComplex.differentialValue, S₀] using congrFun hc t
    obtain ⟨b, hb⟩ := (TopCat.Presheaf.exactAt_cechComplex_iff V F.obj q).mp he c hc'
    refine ⟨b, ?_⟩
    change (S₀.complex F.obj).d q (q + 1) b = c
    simp only [SiteCechComplex.complex, CochainComplex.of_d]
    funext t
    change S₀.differentialValue F.obj q b t = c t
    exact (TopCat.Presheaf.cechComplex_d_apply V F.obj q b t).symm.trans (congrFun hb t)
  obtain ⟨e, _⟩ := S.comparison_exists S₀
  have hz := he₀.isZero_homology
  exact hz.of_iso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ)
    (q + 1)).mapIso (e.app F.obj))

end AlgebraicGeometry.Scheme.Modules
