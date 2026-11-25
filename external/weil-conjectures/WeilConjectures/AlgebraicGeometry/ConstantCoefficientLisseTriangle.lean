/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientLocalModelsComparison
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-! # Finite local constant cohomology and distinguished triangles

Source: Stacks Project, Cohomology on Sites, Tag 094I, using Tag 093U (3).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace SheafOfModules

section Restriction

variable {C : Type u} [Category.{u} C] {T : GrothendieckTopology C}
  {R S : Sheaf T RingCat.{u}}

private noncomputable def restrictCancelIso (α : R ⟶ S) (β : S ⟶ R)
    (h : α ≫ β = 𝟙 R) :
    restrictScalars β ⋙ restrictScalars α ≅ 𝟭 (SheafOfModules.{u} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private noncomputable def coefficientEquivalence (e : R ≅ S) :
    SheafOfModules.{u} S ≌ SheafOfModules.{u} R :=
  CategoryTheory.Equivalence.mk (restrictScalars e.hom) (restrictScalars e.inv)
    (restrictCancelIso e.inv e.hom e.inv_hom_id).symm
    (restrictCancelIso e.hom e.inv e.hom_inv_id)

end Restriction

private theorem closure_of_iso
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing T B))]
    (e : constantCoefficientRing T B ≅ (constantSheaf T RingCat.{u}).obj (RingCat.of B))
    (hcompare : ∀ F, IsLocallyConstantFiniteTypeModules T B F ↔
      IsFiniteTypeLocallyConstant T B ((restrictScalars e.inv).obj F))
    (t : Triangle (DerivedCategory
      (SheafOfModules.{u} (constantCoefficientRing T B))))
    (ht : t ∈ distTriang _)
    (h₁ : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T B
      ((DerivedCategory.homologyFunctor _ i).obj t.obj₁))
    (h₃ : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T B
      ((DerivedCategory.homologyFunctor _ i).obj t.obj₃)) :
    ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T B
      ((DerivedCategory.homologyFunctor _ i).obj t.obj₂) := by
  let R := (constantSheaf T RingCat.{u}).obj (RingCat.of B)
  let P : ObjectProperty (SheafOfModules.{u} R) := IsFiniteTypeLocallyConstant T B
  have hP := finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions T B
  have : P.IsClosedUnderIsomorphisms := by
    constructor
    intro F G e h V
    obtain ⟨S, hS, hs⟩ := h V
    refine ⟨S, hS, ?_⟩
    intro U f hf
    obtain ⟨M, hM, ⟨i⟩⟩ := hs U f hf
    exact ⟨M, hM, ⟨(overFunctor _ U).mapIso e.symm ≪≫ i⟩⟩
  have : P.IsClosedUnderKernels := by
    constructor
    intro X hX
    cases hX with
    | of_isLimit f k hk hf =>
      exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hk)
        (hP.1 _ _ f hf.1 hf.2).1
  have : P.IsClosedUnderCokernels := by
    constructor
    intro X hX
    cases hX with
    | of_isColimit f k hk hf =>
      exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hk)
        (hP.1 _ _ f hf.1 hf.2).2
  have : P.IsClosedUnderExtensions := ⟨fun hS h₁ h₃ ↦ hP.2 _ hS h₁ h₃⟩
  let G := restrictScalars e.inv
  have : G.IsEquivalence := (coefficientEquivalence e.symm).isEquivalence_functor
  let := HasDerivedCategory.standard (SheafOfModules.{u} R)
  let DG := G.mapDerivedCategory
  have trans (X : DerivedCategory (SheafOfModules.{u} (constantCoefficientRing T B)))
      (h : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T B
        ((DerivedCategory.homologyFunctor _ i).obj X)) :
      DerivedCategory.homologyProperty P (DG.obj X) := by
    intro i
    exact P.prop_of_iso ((G.mapDerivedCategoryHomologyFunctorIso i).app X)
      ((hcompare _).mp (h i))
  have h₂ := (DerivedCategory.homologyProperty P).ext_of_isTriangulatedClosed₂
    (DG.mapTriangle.obj t) (DG.map_distinguished t ht) (trans t.obj₁ h₁) (trans t.obj₃ h₃)
  intro i
  apply (hcompare _).mpr
  exact P.prop_of_iso ((G.mapDerivedCategoryHomologyFunctorIso i).app t.obj₂).symm (h₂ i)

/-- Finite locally constant cohomology is closed under the middle term of a
distinguished triangle. Constants are formed in commutative rings as in the
coefficient reduction API. Source: Stacks Project, Tag 094I, first proof paragraph;
Modules on Sites, Tag 093U (3)
(auxiliary; not a blueprint node).

Proof: identify the constant ring with the constant commutative-ring sheaf after
forgetting commutativity. The equivalence on module sheaves carries constant
finite local models to constant finite local models by the constant-module
comparison theorem. The existing Serre theorem gives closure under kernels,
cokernels and extensions on the ring-sheaf side. Apply the five-term exact
cohomology sequence of a distinguished triangle, or equivalently triangulated
closure of its cohomology property. The exact coefficient equivalence commutes
with cohomology. Transport the conclusion back. -/
theorem locallyConstantFiniteTypeModules_of_distinguished
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing T B))]
    (t : Triangle (DerivedCategory
      (SheafOfModules.{u} (constantCoefficientRing T B))))
    (ht : t ∈ distTriang _)
    (h₁ : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T B
      ((DerivedCategory.homologyFunctor _ i).obj t.obj₁))
    (h₃ : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T B
      ((DerivedCategory.homologyFunctor _ i).obj t.obj₃)) :
    ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T B
      ((DerivedCategory.homologyFunctor _ i).obj t.obj₂) := by
  obtain ⟨e, _, hc⟩ := exists_constantCoefficientRing_localModels_comparison T B
  exact closure_of_iso T B e hc t ht h₁ h₃

end SheafOfModules
