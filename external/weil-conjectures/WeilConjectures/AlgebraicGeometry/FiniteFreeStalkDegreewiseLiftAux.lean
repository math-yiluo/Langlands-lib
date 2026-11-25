/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.StalkRestrictionSubopenCompatibility
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- Finite intersection gluing for a finite set of degrees, with explicit outside witnesses.
Source: finite-free-stalk-chain-map-lift-local, finite intersection step.
The proof intersects the finitely many neighbourhoods and transports each representative
along restriction composition; outside the finite set the supplied witnesses are used.
(blueprint: lem-pc-finite-free-stalk-degreewise-lift-core-aux) -/
theorem exists_degreewise_finite_aux
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (y : Y) (t : ∀ n : ℤ,
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P).X n ⟶
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q).X n)
    (I : Finset ℤ)
    (hlocal : ∀ n : ℤ, n ∈ I → ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∃ (g :
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
        ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
          ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n)
    (hout : ∀ n : ℤ, n ∉ I → ∃ (g :
      (((restrictFunctor (⊤ : Y.Opens).ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor (⊤ : Y.Opens).ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (Modules.pullback ((⊤ : Y.Opens).fromSpecStalkOfMem y (by simp))).map g =
        ((stalkRestrictionComplexIso (⊤ : Y.Opens) y (by simp)).app P).hom.f n ≫ t n ≫
          ((stalkRestrictionComplexIso (⊤ : Y.Opens) y (by simp)).app Q).inv.f n) :
    ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∀ n : ℤ, ∃ (g :
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
        ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
          ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n := by
  classical
  let E := fun (U : Y.Opens) (hyU : y ∈ U) (n : ℤ) => ∃ (g :
    (restrictFunctor U.ι).obj (P.X n) ⟶ (restrictFunctor U.ι).obj (Q.X n)),
    (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
      ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
        ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n
  have shrink (U V : Y.Opens) (hyU : y ∈ U) (hyV : y ∈ V)
      (hVU : V ≤ U) (n : ℤ) : E U hyU n → E V hyV n := by
    rintro ⟨g, hg⟩
    let C := NatIso.mapHomologicalComplex
      ((restrictFunctorCongr (Y.homOfLE_ι hVU)).symm ≪≫
        restrictFunctorComp (Y.homOfLE hVU) U.ι) (ComplexShape.up ℤ)
    refine ⟨(C.app P).hom.f n ≫ (restrictFunctor (Y.homOfLE hVU)).map g ≫
      (C.app Q).inv.f n, ?_⟩
    rw [stalkRestrictionComplexIso_map_subopen P Q y U V hyU hyV hVU n g, hg]
    have hP := congrArg (fun f => f.f n)
      ((stalkRestrictionComplexIso U y hyU).app P).inv_hom_id
    have hQ := congrArg (fun f => f.f n)
      ((stalkRestrictionComplexIso U y hyU).app Q).inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hP hQ
    simp only [← Category.assoc, hP, Category.id_comp]
    simp only [Category.assoc, hQ, Category.id_comp]
  have finite : ∀ J : Finset ℤ,
      (∀ n ∈ J, ∃ (U : Y.Opens) (hyU : y ∈ U), E U hyU n) →
        ∃ (U : Y.Opens) (hyU : y ∈ U), ∀ n ∈ J, E U hyU n := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨⊤, by simp, by simp⟩
    | @insert a J ha ih =>
      intro h
      obtain ⟨U, hyU, hU⟩ := ih (fun n hn => h n (Finset.mem_insert_of_mem hn))
      obtain ⟨V, hyV, hV⟩ := h a (Finset.mem_insert_self a J)
      have hy : y ∈ U ⊓ V := ⟨hyU, hyV⟩
      refine ⟨U ⊓ V, hy, ?_⟩
      intro n hn
      rcases Finset.mem_insert.mp hn with rfl | hn
      · exact shrink V (U ⊓ V) hyV hy inf_le_right n hV
      · exact shrink U (U ⊓ V) hyU hy inf_le_left n (hU n hn)
  obtain ⟨U, hyU, hU⟩ := finite I hlocal
  refine ⟨U, hyU, ?_⟩
  intro n
  by_cases hn : n ∈ I
  · exact hU n hn
  · exact shrink ⊤ U (by simp) hyU le_top n (hout n hn)
end AlgebraicGeometry.Scheme.Modules
