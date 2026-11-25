/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The homology of the derived single functor on maps of complexes

The canonical isomorphism `H⁰(A[0]) ≅ A` of `DerivedCategory.singleFunctorCompHomologyFunctorIso`
computes the map induced in degree-`0` homology by a morphism of complexes
`f : A[0] ⟶ M`: it is the map `A ⟶ Z⁰(M) ⟶ H⁰(M)` induced by `f` on cycles, up to the
isomorphism `DerivedCategory.singleCyclesHom A : A ≅ Z⁰(A[0])`, which is natural in `A`.

## Main definitions

- `DerivedCategory.singleCyclesHom`: the isomorphism `A ⟶ Z⁰(A[0])`.

## Main statements

- `DerivedCategory.singleFunctorCompHomologyFunctorIso_inv_app_comp_map_Q_map`:
  the degree-`0` homology of `Q(f)` for `f : A[0] ⟶ M`, computed on cycles.
- `DerivedCategory.nonempty_iso_singleFunctor_obj_homologyFunctor_obj`: an object of `D(C)`
  with homology concentrated in degree `n` is the single complex on its `n`-th homology.
-/

@[expose] public section

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The degree-`0` homology of `Q(f)` for `f : A[0] ⟶ M`, through `homologyMap f 0`. -/
lemma singleFunctorCompHomologyFunctorIso_inv_app_comp_map_Q_map_homologyMap
    {A : C} {M : CochainComplex C ℤ} (f : (CochainComplex.singleFunctor C 0).obj A ⟶ M) :
    (singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
      (homologyFunctor C 0).map (Q.map f) =
    ((singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
      (homologyFunctorFactors C 0).hom.app _) ≫
      HomologicalComplex.homologyMap f 0 ≫ (homologyFunctorFactors C 0).inv.app M := by
  have := (homologyFunctorFactors C 0).hom.naturality f
  simp only [Functor.comp_map] at this
  simp only [Category.assoc]
  congr 1
  erw [← reassoc_of% this, Iso.hom_inv_id_app, Category.comp_id]

/-- The isomorphism `A ≅ Z⁰(A[0])` from an object to the degree-`0` cycles of the single
complex, through which the homology of the derived single functor is computed. -/
noncomputable def singleCyclesHom (A : C) :
    A ⟶ ((HomologicalComplex.single C (.up ℤ) 0).obj A).cycles 0 :=
  (singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
    (homologyFunctorFactors C 0).hom.app _ ≫
      (HomologicalComplex.singleObjHomologySelfIso _ 0 A).hom ≫
        (HomologicalComplex.singleObjCyclesSelfIso _ 0 A).inv

instance (A : C) : IsIso (singleCyclesHom A) := by
  dsimp [singleCyclesHom]; infer_instance

/-- The degree-`0` homology of `Q(f)` for `f : A[0] ⟶ M` is the map induced on cycles, followed
by `Z⁰(M) ⟶ H⁰(M)`. -/
lemma singleFunctorCompHomologyFunctorIso_inv_app_comp_map_Q_map
    {A : C} {M : CochainComplex C ℤ} (f : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ M) :
    (singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
      (homologyFunctor C 0).map (Q.map f) =
    singleCyclesHom A ≫ HomologicalComplex.cyclesMap f 0 ≫ M.homologyπ 0 ≫
      (homologyFunctorFactors C 0).inv.app M := by
  rw [singleFunctorCompHomologyFunctorIso_inv_app_comp_map_Q_map_homologyMap f]
  simp only [singleCyclesHom, Category.assoc]
  congr 2
  rw [← cancel_epi (((HomologicalComplex.single C (.up ℤ) 0).obj A).homologyπ 0),
    HomologicalComplex.homologyπ_naturality_assoc]
  simp

/-- `DerivedCategory.singleCyclesHom` is natural. -/
lemma singleCyclesHom_naturality {A A' : C} (φ : A' ⟶ A) :
    singleCyclesHom A' ≫ HomologicalComplex.cyclesMap
      ((HomologicalComplex.single C (.up ℤ) 0).map φ) 0 = φ ≫ singleCyclesHom A := by
  have h₁ := (singleFunctorCompHomologyFunctorIso C 0).inv.naturality φ
  have h₂ := (homologyFunctorFactors C 0).hom.naturality
    ((HomologicalComplex.single C (.up ℤ) 0).map φ)
  simp only [Functor.id_map, Functor.comp_map] at h₁ h₂
  simp only [singleCyclesHom, Category.assoc,
    HomologicalComplex.singleObjCyclesSelfIso_inv_naturality]
  rw [← HomologicalComplex.singleObjHomologySelfIso_hom_naturality_assoc, reassoc_of% h₁]
  erw [reassoc_of% h₂]
  rfl

section Concentrated

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Blueprint `lem-pur-concentrated-complex-shift`: Complexes with cohomology in a single degree

*Concentration in one degree.* If the homology objects `H^i(K)` vanish for every `i ≠ n`, then
the truncation triangles identify `K` with `H^n(K)[-n]`, the object `H^n(K)` placed in
degree `n`. -/
theorem nonempty_iso_singleFunctor_obj_homologyFunctor_obj (K : DerivedCategory C) (n : ℤ)
    (hK : ∀ i, i ≠ n → IsZero ((homologyFunctor C i).obj K)) :
    Nonempty (K ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj K)) := by
  have : K.IsGE n := (isGE_iff K n).2 fun i hi ↦ hK i hi.ne
  have : K.IsLE n := (isLE_iff K n).2 fun i hi ↦ hK i hi.ne'
  obtain ⟨Y, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  exact ⟨e ≪≫ (singleFunctor C n).mapIso
    (((singleFunctorCompHomologyFunctorIso C n).app Y).symm ≪≫ (homologyFunctor C n).mapIso e.symm)⟩

end Concentrated

end DerivedCategory
