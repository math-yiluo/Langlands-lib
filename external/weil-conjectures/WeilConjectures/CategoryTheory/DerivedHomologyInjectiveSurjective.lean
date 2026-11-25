/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.SingleHomology

/-! # Surjectivity of homology on maps to an injective single object

The complex-level lift is constructed by extending from homology to opcycles.
Localization and the homology comparison then give the derived-category lift.
-/

@[expose] public section

universe w uA vA

open CategoryTheory

namespace CategoryTheory

/-- Extend a homology map to opcycles using injectivity, then precompose with the
opcycles quotient to obtain the degree-zero component of a chain map. -/
private theorem homology_to_single_surjective
    {A : Type uA} [Category.{vA} A] [Abelian A]
    (K : CochainComplex A ℤ) (I : A) [Injective I] :
    Function.Surjective
      (HomologicalComplex.homologyMap (i := (0 : ℤ)) :
        (K ⟶ (HomologicalComplex.single A (.up ℤ) 0).obj I) →
        (K.homology 0 ⟶ ((HomologicalComplex.single A (.up ℤ) 0).obj I).homology 0)) := by
  intro g
  let e := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 I
  let r := Injective.factorThru (g ≫ e.hom) (K.homologyι 0)
  let f := HomologicalComplex.mkHomToSingle (K.pOpcycles 0 ≫ r)
    (fun i _ ↦ by simp)
  refine ⟨f, ?_⟩
  rw [← cancel_mono e.hom, ← cancel_epi (K.homologyπ 0)]
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  simp only [e, HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom,
    HomologicalComplex.cyclesMap_i_assoc]
  simp only [f, HomologicalComplex.mkHomToSingle_f, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← HomologicalComplex.homology_π_ι_assoc]
  simp [r, e]

/-- Surjectivity half of the injective-target derived homology comparison.

Source: proof step 1 of `new-stage3-derived-homology-injective-bijective`.
Proof: choose a cochain complex P representing K. Use the localization homology
comparison and the isomorphism K ≅ Q(P) to transport the given map to a map
H⁰(P) → H⁰(I[0]). Identify H⁰(I[0]) with I and extend the map along the
monomorphism H⁰(P) → opcycles⁰(P), using injectivity of I. Precompose with
P⁰ → opcycles⁰(P). This kills incoming boundaries and hence defines a chain
map P → I[0]. The identity homologyπ ≫ homologyι = iCycles ≫ pOpcycles and
naturality of homologyπ show that its homology map is the prescribed map.
Apply Q and precompose with K ≅ Q(P); naturality of the localization homology
comparison proves the desired equality. No K-injective replacement is needed.

(auxiliary; not a blueprint node) -/
theorem derived_homology_injective_surjective
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (I : A) [Injective I] :
    Function.Surjective
      ((DerivedCategory.homologyFunctor A 0).map :
        (K ⟶ (DerivedCategory.singleFunctor A 0).obj I) →
        ((DerivedCategory.homologyFunctor A 0).obj K ⟶
          (DerivedCategory.homologyFunctor A 0).obj
            ((DerivedCategory.singleFunctor A 0).obj I))) := by
  intro g
  let P := DerivedCategory.Q.objPreimage K
  let S := (HomologicalComplex.single A (.up ℤ) 0).obj I
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let cP := (DerivedCategory.homologyFunctorFactors A 0).app P
  let cS := (DerivedCategory.homologyFunctorFactors A 0).app S
  obtain ⟨f, hf⟩ := homology_to_single_surjective P I
    (cP.inv ≫ (DerivedCategory.homologyFunctor A 0).map e.hom ≫ g ≫ cS.hom)
  refine ⟨e.inv ≫ DerivedCategory.Q.map f, ?_⟩
  rw [Functor.map_comp, ← cancel_mono cS.hom, Category.assoc]
  have hnat : (DerivedCategory.homologyFunctor A 0).map (DerivedCategory.Q.map f) ≫
      cS.hom = cP.hom ≫ HomologicalComplex.homologyMap f 0 :=
    DerivedCategory.homologyFunctorFactors_hom_naturality f 0
  dsimp only at hf
  rw [hnat]
  simp only [hf, Iso.hom_inv_id_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

end CategoryTheory
