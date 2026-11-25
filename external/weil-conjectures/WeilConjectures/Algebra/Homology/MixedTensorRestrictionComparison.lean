/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.MixedTotalTensor
import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-!
# Restricting the mixed total tensor

Source: Stacks Project, More on Algebra, Section 06Y5 and Lemma 06Y6.
(blueprint: lem-pc-mixed-tensor-restriction-comparison)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace CochainComplex

private noncomputable def coefficientIso {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (E : ModuleCat.{u} R) (N : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars f).obj (((ModuleCat.mixedTensor f).flip.obj E).obj N) ≅
      E ⊗ (ModuleCat.restrictScalars f).obj N := by
  let := f.toAlgebra
  let := Module.compHom N f
  let : IsScalarTower R A N := SMul.comp.isScalarTower f
  exact (((TensorProduct.AlgebraTensorModule.cancelBaseChange R A A N E).restrictScalars R) ≪≫ₗ
    TensorProduct.comm R N E).toModuleIso

private theorem coefficientIso_naturality₁ {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) {E E' : ModuleCat.{u} R} (a : E ⟶ E') (N : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars f).map (((ModuleCat.mixedTensor f).flip.map a).app N) ≫
        (coefficientIso f E' N).hom =
      (coefficientIso f E N).hom ≫ (a ▷ (ModuleCat.restrictScalars f).obj N) := by
  let := f.toAlgebra
  let := Module.compHom N f
  let : IsScalarTower R A N := SMul.comp.isScalarTower f
  ext x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro n t
    refine TensorProduct.inductionOn t ?_ ?_
    · intro b e
      rfl
    · intro x y hx hy
      simp_all [TensorProduct.tmul_add]
  · intro x y hx hy
    simp_all

private theorem coefficientIso_naturality₂ {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (E : ModuleCat.{u} R) {N N' : ModuleCat.{u} A} (a : N ⟶ N') :
    (ModuleCat.restrictScalars f).map (((ModuleCat.mixedTensor f).flip.obj E).map a) ≫
        (coefficientIso f E N').hom =
      (coefficientIso f E N).hom ≫ (E ◁ (ModuleCat.restrictScalars f).map a) := by
  let := f.toAlgebra
  let := Module.compHom N f
  let := Module.compHom N' f
  let : IsScalarTower R A N := SMul.comp.isScalarTower f
  let : IsScalarTower R A N' := SMul.comp.isScalarTower f
  ext x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro n t
    refine TensorProduct.inductionOn t ?_ ?_
    · intro b e
      change A at b
      change e ⊗ₜ[R] (b • a n) = e ⊗ₜ[R] a (b • n)
      rw [map_smul]
    · intro x y hx hy
      simp_all [TensorProduct.tmul_add]
  · intro x y hx hy
    simp_all

private noncomputable def bicomplexIso {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (N : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).obj
        ((((ModuleCat.mixedTensor f).flip.mapBifunctorHomologicalComplex
          (.up ℤ) (.up ℤ)).obj E).obj N) ≅
      (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj E).obj
          (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj N) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p ↦ ?_) ?_
  · refine HomologicalComplex.Hom.isoOfComponents (fun q ↦ coefficientIso f (E.X p) (N.X q)) ?_
    intro q q' hq
    exact (coefficientIso_naturality₂ f (E.X p) (N.d q q')).symm
  · intro p p' hp
    ext1 q
    exact (coefficientIso_naturality₁ f (E.d p p') (N.X q)).symm

private noncomputable def totalComparison {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (N : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
      ((((ModuleCat.mixedTensor f).flip.map₂CochainComplex).obj E).obj N) ≅
      E ⊗ (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj N) :=
  (HomologicalComplex₂.mapTotalIso (ModuleCat.restrictScalars f) _ (.up ℤ)).symm ≪≫
    HomologicalComplex₂.total.mapIso (bicomplexIso f E N) (.up ℤ)

private theorem bicomplexIso_naturality₁ {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) {E E' : CochainComplex (ModuleCat.{u} R) ℤ} (a : E ⟶ E')
    (N : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).map
        ((((ModuleCat.mixedTensor f).flip.mapBifunctorHomologicalComplex
          (.up ℤ) (.up ℤ)).map a).app N) ≫ (bicomplexIso f E' N).hom =
      (bicomplexIso f E N).hom ≫
        (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
          (.up ℤ) (.up ℤ)).map a).app
          (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj N) := by
  ext1 p
  ext1 q
  exact coefficientIso_naturality₁ f (a.f p) (N.X q)

private theorem bicomplexIso_naturality₂ {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (E : CochainComplex (ModuleCat.{u} R) ℤ)
    {N N' : CochainComplex (ModuleCat.{u} A) ℤ} (a : N ⟶ N') :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).map
        ((((ModuleCat.mixedTensor f).flip.mapBifunctorHomologicalComplex
          (.up ℤ) (.up ℤ)).obj E).map a) ≫ (bicomplexIso f E N').hom =
      (bicomplexIso f E N).hom ≫
        (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
          (.up ℤ) (.up ℤ)).obj E).map
          (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map a) := by
  ext1 p
  ext1 q
  exact coefficientIso_naturality₂ f (E.X p) (a.f q)

set_option backward.isDefEq.respectTransparency false in
private theorem totalComparison_naturality₁ {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) {E E' : CochainComplex (ModuleCat.{u} R) ℤ} (a : E ⟶ E')
    (N : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        ((((ModuleCat.mixedTensor f).flip.map₂CochainComplex).map a).app N) ≫
          (totalComparison f E' N).hom =
      (totalComparison f E N).hom ≫
        (a ▷ (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj N)) := by
  change _ = (totalComparison f E N).hom ≫
    HomologicalComplex.mapBifunctorMap a (𝟙 _) (curriedTensor (ModuleCat R)) (.up ℤ)
  let ψ := ((((ModuleCat.mixedTensor f).flip.mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).map a).app N)
  have h₁ := HomologicalComplex₂.mapTotalIso_inv_naturality
    (ModuleCat.restrictScalars f) ψ (.up ℤ)
  have h₂ := congrArg (fun t ↦ HomologicalComplex₂.total.map t (.up ℤ))
    (bicomplexIso_naturality₁ f a N)
  simp only [HomologicalComplex₂.total.map_comp] at h₂
  have h₃ := congrArg (fun t ↦ t ≫
    HomologicalComplex₂.total.map (bicomplexIso f E' N).hom (.up ℤ)) h₁
  have h₄ := congrArg (fun t ↦ (HomologicalComplex₂.mapTotalIso
    (ModuleCat.restrictScalars f) _ (.up ℤ)).inv ≫ t) h₂
  simpa [totalComparison, Functor.map₂CochainComplex, Functor.map₂HomologicalComplex,
    HomologicalComplex.mapBifunctorMap, HomologicalComplex.monoidalCategory,
    HomologicalComplex.monoidalCategoryStruct,
    HomologicalComplex.tensorHom, ψ, Category.assoc] using
    h₃.trans ((Category.assoc _ _ _).trans (h₄.trans (Category.assoc _ _ _).symm))

set_option backward.isDefEq.respectTransparency false in
private theorem totalComparison_naturality₂ {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (E : CochainComplex (ModuleCat.{u} R) ℤ)
    {N N' : CochainComplex (ModuleCat.{u} A) ℤ} (a : N ⟶ N') :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        ((((ModuleCat.mixedTensor f).flip.map₂CochainComplex).obj E).map a) ≫
          (totalComparison f E N').hom =
      (totalComparison f E N).hom ≫
        (E ◁ (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map a)) := by
  change _ = (totalComparison f E N).hom ≫
    HomologicalComplex.mapBifunctorMap (𝟙 E)
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map a)
      (curriedTensor (ModuleCat R)) (.up ℤ)
  let ψ := ((((ModuleCat.mixedTensor f).flip.mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj E).map a)
  have h₁ := HomologicalComplex₂.mapTotalIso_inv_naturality
    (ModuleCat.restrictScalars f) ψ (.up ℤ)
  have h₂ := congrArg (fun t ↦ HomologicalComplex₂.total.map t (.up ℤ))
    (bicomplexIso_naturality₂ f E a)
  simp only [HomologicalComplex₂.total.map_comp] at h₂
  have h₃ := congrArg (fun t ↦ t ≫
    HomologicalComplex₂.total.map (bicomplexIso f E N').hom (.up ℤ)) h₁
  have h₄ := congrArg (fun t ↦ (HomologicalComplex₂.mapTotalIso
    (ModuleCat.restrictScalars f) _ (.up ℤ)).inv ≫ t) h₂
  simpa [totalComparison, Functor.map₂CochainComplex, Functor.map₂HomologicalComplex,
    HomologicalComplex.mapBifunctorMap, HomologicalComplex.monoidalCategory,
    HomologicalComplex.monoidalCategoryStruct,
    HomologicalComplex.tensorHom, ψ, Category.assoc] using
    h₃.trans ((Category.assoc _ _ _).trans (h₄.trans (Category.assoc _ _ _).symm))


/-- Restricting the mixed total tensor gives the ordinary total tensor, naturally in
both complexes. Source: Stacks Project, More on Algebra, Section 06Y5 and Lemma 06Y6.
(blueprint: lem-pc-mixed-tensor-restriction-comparison)

Proof: In bidegree `(p,q)`, identify the restriction of
`N^q ⊗_A (A ⊗_R E^p)` with `E^p ⊗_R N^q` by
`n ⊗ (a ⊗ e) ↦ e ⊗ a n`. The inverse sends `e ⊗ n` to
`n ⊗ (1 ⊗ e)`. Balancing verifies that both maps are well-defined and inverse.
They commute with maps in each factor. Restriction preserves coproducts, so taking
coproducts over `p+q=k` gives inverse maps in each total degree. Both total complexes
have differential `d_E ⊗ 1 + (-1)^p 1 ⊗ d_N`; the bidegree maps commute with
these two summands separately. Thus they form a chain isomorphism, natural in both
variables. No flatness of the ring map is needed. -/
theorem exists_mixedTensor_restriction_iso {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) :
    let S := (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)
    let B := (ModuleCat.mixedTensor f).flip.map₂CochainComplex
    Nonempty (B ⋙ (Functor.whiskeringRight _ _ _).obj S ≅
      curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (Functor.whiskeringLeft _ _ _).obj S) := by
  refine ⟨NatIso.ofComponents (fun E ↦
    NatIso.ofComponents (fun N ↦ totalComparison f E N) (fun a ↦ ?_)) (fun a ↦ ?_)⟩
  · exact totalComparison_naturality₂ f E a
  · apply NatTrans.ext
    funext N
    exact totalComparison_naturality₁ f a N

end CochainComplex
