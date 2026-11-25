/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedAdicCompleteCriteria
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology

/-!
# Derived adic completeness and homology

Let `A` be an abelian category with exact countable products. Then the derived category `D(A)`
has countable products (`CategoryTheory.derivedCategory_hasCountableProducts`) and the homology
functors `Hᵖ : D(A) ⥤ A` commute with them. Hence a complex `K` is derived `n`-adically
complete if and only if all its homology objects are, the definition
`CategoryTheory.IsDerivedAdicComplete` making sense in `A` itself
(`DerivedCategory.isDerivedAdicComplete_iff_homology`).

As a consequence, the derived `n`-adically complete objects of `A` are stable under cokernels
(`DerivedCategory.isDerivedAdicComplete_cokernel`): for `f : M ⟶ N`, the cokernel of `f` is
`H⁰` of the cone of `f`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe w v u

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasCountableProducts A] [CountableAB4Star A] [HasCountableProducts (DerivedCategory A)]

/-- The homology functors of the derived category of an abelian category with exact countable
products commute with countable products. -/
instance preservesLimitsOfShape_discrete_nat_homologyFunctor (p : ℤ) :
    PreservesLimitsOfShape (Discrete ℕ) (homologyFunctor A p) :=
  (derivedCategory_countableProducts_properties A).2 ℕ p

/-- A complex is derived `n`-adically complete if and only if all its homology objects are. -/
lemma isDerivedAdicComplete_iff_homology {n : ℤ} (K : DerivedCategory A) :
    IsDerivedAdicComplete n K ↔
      ∀ p : ℤ, IsDerivedAdicComplete n ((homologyFunctor A p).obj K) :=
  ⟨fun hK _ ↦ hK.map _, IsDerivedAdicComplete.of_map (fun p : ℤ ↦ homologyFunctor A p)
    fun f hf ↦ (isIso_iff A f).2 hf⟩

/-- An object of `A` which is derived `n`-adically complete in `A` is so in `D(A)`, placed in
any degree. -/
lemma isDerivedAdicComplete_singleFunctor_obj {n : ℤ} {M : A} (hM : IsDerivedAdicComplete n M)
    (q : ℤ) : IsDerivedAdicComplete n ((singleFunctor A q).obj M) := by
  refine (isDerivedAdicComplete_iff_homology _).2 fun p ↦ ?_
  by_cases hp : p = q
  · subst hp
    exact hM.of_iso ((singleFunctorCompHomologyFunctorIso A p).app M).symm
  · exact .of_isZero (isZero_homologyFunctor_obj_of_iso_singleFunctor (Iso.refl _) hp)

/-- The cokernel of a morphism `f : M ⟶ N` is `H⁰` of the third object of a distinguished
triangle on `f`, placed in degree `0`. -/
noncomputable def homologyFunctorZeroObjIsoCokernel {M N : A} (f : M ⟶ N)
    {Z : DerivedCategory A} (g : (singleFunctor A 0).obj N ⟶ Z)
    (h : Z ⟶ ((singleFunctor A 0).obj M)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((singleFunctor A 0).map f) g h ∈ distTriang _) :
    (homologyFunctor A 0).obj Z ≅ cokernel f := by
  have hS := HomologySequence.exact₂ _ hT 0
  have := (HomologySequence.epi_homologyMap_mor₂_iff _ hT 0 1).2
    ((isZero_homologyFunctor_obj_of_iso_singleFunctor (Iso.refl _) (by omega)).eq_of_tgt _ _)
  exact hS.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
    cokernel.mapIso _ f ((singleFunctorCompHomologyFunctorIso A 0).app M)
      ((singleFunctorCompHomologyFunctorIso A 0).app N)
      ((singleFunctorCompHomologyFunctorIso A 0).hom.naturality f)

/-- The derived `n`-adically complete objects of `A` are stable under cokernels. -/
lemma isDerivedAdicComplete_cokernel {n : ℤ} {M N : A} (f : M ⟶ N)
    (hM : IsDerivedAdicComplete n M) (hN : IsDerivedAdicComplete n N) :
    IsDerivedAdicComplete n (cokernel f) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle ((singleFunctor A 0).map f)
  have hZ := IsDerivedAdicComplete.of_distTriang₁₂ _ hT
    (isDerivedAdicComplete_singleFunctor_obj hM 0) (isDerivedAdicComplete_singleFunctor_obj hN 0)
  exact ((isDerivedAdicComplete_iff_homology _).1 hZ 0).of_iso
    (homologyFunctorZeroObjIsoCokernel f g h hT)

end DerivedCategory
