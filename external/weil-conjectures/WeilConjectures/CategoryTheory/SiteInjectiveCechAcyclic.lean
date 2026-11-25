/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.SiteCechZeroCohomology
import WeilConjectures.CategoryTheory.SiteCechCofreeExact
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Čech acyclicity of injective sheaves on a site

Source: Stacks Project, Cohomology on Sites, Tags 03AW, 03F6, 03AS, 03AT, 03AU,
03AN (blueprint: lem-weil-pbc-site-injective-cech-acyclic).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- An injective abelian sheaf has vanishing positive Čech cohomology on every covering,
and degree-zero Čech cohomology is its sections on the covered object.
The coefficients are sized to contain the cofree presheaf indexed by all objects and homs.
Source: Stacks 03AW, 03F6, 03AT and 03AN.

Proof: exact sheafification transfers injectivity to the underlying presheaf. Its natural
monomorphism into the cofree presheaf splits by injectivity. The chosen Čech functor maps
this to a split embedding of complexes. Positive cocycles map to cocycles of the cofree
complex; the insertion contraction supplies primitives there. Mapping these primitives
back by the splitting gives primitives of the original cocycles. Hence the positive
homology is zero. The sheaf gluing theorem identifies degree-zero homology with sections.
(blueprint: lem-weil-pbc-site-injective-cech-acyclic) -/
theorem site_injective_cech_acyclic
    {C : Type u} [Category.{v} C]
    {J : Precoverage C} [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type (max u v)} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U)
    (S : SiteCechComplex f hom)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{max u v}) [Injective I] :
    (∀ p : ℕ, 0 < p → IsZero ((S.cohomologyFunctor p).obj I.obj)) ∧
      Nonempty (((S.cohomologyFunctor 0).obj I.obj) ≅
        I.obj.obj (op U)) := by
  have : Injective I.obj := (sheafificationAdjunction _ _).map_injective I inferInstance
  refine ⟨?_, site_cech_zero_cohomology f hom hcover S I⟩
  intro p hp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  let a := S.complexMap (Presheaf.toCofree I.obj)
  let b := S.complexMap (Injective.factorThru (𝟙 I.obj) (Presheaf.toCofree I.obj))
  have hab : a ≫ b = 𝟙 _ := by
    rw [← S.complexMap_comp, Injective.comp_factorThru, S.complexMap_id]
  have hExact : (S.complex I.obj).ExactAt (q + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    intro c hc
    have he := S.exactAt_cofree I.obj q
    rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff] at he
    obtain ⟨d, hd⟩ := he (a.f (q + 1) c) (by
      exact (ConcreteCategory.congr_hom (a.comm (q + 1) (q + 2)) c).trans
        ((congrArg (a.f (q + 2)) hc).trans (map_zero _)))
    refine ⟨b.f q d, ?_⟩
    calc
      _ = b.f (q + 1) ((S.complex (Presheaf.cofree I.obj)).d q (q + 1) d) :=
        ConcreteCategory.congr_hom (b.comm q (q + 1)) d
      _ = b.f (q + 1) (a.f (q + 1) c) := congrArg (b.f (q + 1)) hd
      _ = c := by
        rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, hab,
          HomologicalComplex.id_f, ConcreteCategory.id_apply]
  exact hExact.isZero_homology

end CategoryTheory
