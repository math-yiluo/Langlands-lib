/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisFreeComplex
/-! # Free abelian sheaves for a two-open cover

Source: Stacks Project, Tag 01EB.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
open Opposite

private noncomputable def topFreeComponent (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    AddCommGrpCat.free.obj (U.unop ⟶ (⊤ : X.Opens)) ≅
      AddCommGrpCat.of (ULift.{u} ℤ) := by
  letI : Unique (U.unop ⟶ (⊤ : X.Opens)) :=
    ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso

private noncomputable def topFreeIso (X : Scheme.{u}) :
    H.openFreeSheaf (⊤ : X.Opens) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapIso
    (NatIso.ofComponents (topFreeComponent X) (by
      intro U V f
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro a
      rfl))

private lemma precomp_postcomp {C : Type*} [Category C] [Abelian C] [HasExt.{u} C]
    {A Z F : C} (i : A ≅ Z) (n : ℕ) (a : F ⟶ F) (x : Ext Z F n) :
    Ext.precompAddEquiv i F n (x.comp (Ext.mk₀ a) (add_zero n)) =
      (Ext.precompAddEquiv i F n x).comp (Ext.mk₀ a) (add_zero n) := by
  exact (Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (zero_add n)).symm

private lemma precomp_comparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt.{u} C] [HasExt.{u} D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {A Z F : C} {Z' N : D} (i : A ≅ Z) (c : G.obj Z ≅ Z')
    (φ : G.obj F ⟶ N) (n : ℕ) (x : Ext Z F n) :
    Ext.precompAddEquiv (G.mapIso i ≪≫ c) N n
      (((Ext.mk₀ c.inv).comp (x.mapExactFunctor G) (zero_add n)).comp
        (Ext.mk₀ φ) (add_zero n)) =
    ((Ext.precompAddEquiv i F n x).mapExactFunctor G).comp
      (Ext.mk₀ φ) (add_zero n) := by
  simp only [Ext.precompAddEquiv_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_assoc_of_third_deg_zero]
  congr 1
  rw [Ext.mk₀_comp_mk₀_assoc]
  change (Ext.mk₀ ((G.map i.hom ≫ c.hom) ≫ c.inv)).comp
    (x.mapExactFunctor G) (zero_add n) = _
  rw [Category.assoc, c.hom_inv_id, Category.comp_id]

private theorem extComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt.{u} C] [HasExt.{u} D]
    {α β : Type*} (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {A Z F : C} {Z' N : D} (i : A ≅ Z) (c : G.obj Z ≅ Z')
    (φ : G.obj F ⟶ N) (ρ : α → (F ⟶ F)) (τ : β → (N ⟶ N)) :
    ∃ (e : ∀ n, Ext Z F n ≃+ Ext A F n)
      (e' : ∀ n, Ext Z' N n ≃+ Ext (G.obj A) N n),
      (∀ n a x, e n (x.comp (Ext.mk₀ (ρ a)) (add_zero n)) =
        (e n x).comp (Ext.mk₀ (ρ a)) (add_zero n)) ∧
      (∀ n a x, e' n (x.comp (Ext.mk₀ (τ a)) (add_zero n)) =
        (e' n x).comp (Ext.mk₀ (τ a)) (add_zero n)) ∧
      (∀ n x, e' n (((Ext.mk₀ c.inv).comp
        (x.mapExactFunctor G) (zero_add n)).comp (Ext.mk₀ φ) (add_zero n)) =
        ((e n x).mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n)) := by
  refine ⟨fun n ↦ Ext.precompAddEquiv i F n,
    fun n ↦ Ext.precompAddEquiv (G.mapIso i ≪≫ c) N n, ?_, ?_, ?_⟩
  · intro n a x
    exact precomp_postcomp i n (ρ a) x
  · intro n a x
    exact precomp_postcomp (G.mapIso i ≪≫ c) n (τ a) x
  · intro n x
    exact precomp_comparison G i c φ n x

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}
/-- Compatible Ext presentations for a single cohomology term.
Source: Stacks Project, Tag 01EB and Section 01F7.
(blueprint: lem-pc-global-free-ext-comparison)

Proof: For every open U, Hom(U, top) is a singleton. The free abelian group
on this singleton is canonically ULift integers, naturally in U (check on the
free generators). Sheafifying gives topFreeIso from the free sheaf on top to
the constant integer sheaf. Precomposition with this isomorphism gives e;
precomposition with its inverse-image isomorphism followed by constIso gives e'.
The scalar actions are definitionally Ext postcomposition, so associativity
proves both scalar identities. The definition of H.baseChangeLinear applies
inverse image to Ext and composes with constIso.inv and the coefficient map.
Functoriality of Ext composition, associativity, and cancellation of constIso.hom
with constIso.inv prove the final identity. All equivalences are constructed
explicitly. The construction also applies to the empty scheme, degree zero,
and zero coefficients, without additional hypotheses.
-/
theorem H.globalFreeExtComparison (f : X ⟶ Spec (.of R)) (M : X.Modules) :
    let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
    let G := invImage (baseChangeFst (S := S) f)
    let N := (SheafOfModules.toSheaf (baseChangedScheme (S := S) f).ringCatSheaf).obj
      (baseChangedModule (S := S) f M)
    let φ := coeff (baseChangeFst (S := S) f) (baseChangeUnit (S := S) f M)
    let ρ := (scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let τ := (scalarRep (baseChangedModule (S := S) f M)).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    ∃ (e : ∀ n, HOver f M n ≃+ Ext (H.openFreeSheaf (⊤ : X.Opens)) F n)
      (e' : ∀ n, HOver (baseChangeSnd (S := S) f) (baseChangedModule (S := S) f M) n ≃+
        Ext (G.obj (H.openFreeSheaf (⊤ : X.Opens))) N n),
      (∀ n a x, e n (a • x) = (e n x).comp (Ext.mk₀ (ρ a).asHom) (add_zero n)) ∧
      (∀ n a x, e' n (a • x) = (e' n x).comp (Ext.mk₀ (τ a).asHom) (add_zero n)) ∧
      (∀ n x, e' n (H.baseChangeLinear (S := S) f M n x) =
        ((e n x).mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n)) := by
  exact extComparison (invImage (baseChangeFst (S := S) f)) (topFreeIso X)
    (constIso (baseChangeFst (S := S) f))
    (coeff (baseChangeFst (S := S) f) (baseChangeUnit (S := S) f M))
    (fun a ↦ ((scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom) a).asHom)
    (fun a ↦ ((scalarRep (baseChangedModule (S := S) f M)).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom) a).asHom)

end AlgebraicGeometry.Scheme.Modules
