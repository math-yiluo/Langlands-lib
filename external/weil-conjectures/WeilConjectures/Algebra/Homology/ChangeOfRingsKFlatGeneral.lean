/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Change of rings preserves K-flat complexes

Source: Stacks Project, Cohomology on Sites, Lemma 21.18.1, Tag 0G7E.

Unlike `SheafOfModules.changeOfRings_isKFlat_of_flat_terms`, no flatness of the terms is
assumed: K-flatness of `K ⊗_R S` only uses the tensor cancellation
`U(N ⊗_S (M ⊗_R S)) ≅ UN ⊗_R M` and the exactness of restriction of scalars.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace SheafOfModules

open CategoryTheory.Limits in
private theorem restrictScalars_exact_kflatGeneral
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    {A B : Sheaf J RingCat.{max u v}} (α : A ⟶ B) :
    PreservesFiniteLimits (restrictScalars.{max u v} α) ∧
      PreservesFiniteColimits (restrictScalars.{max u v} α) := by
  let U := restrictScalars.{max u v} α
  have : PreservesFiniteLimits (U ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf B))
  have : PreservesFiniteColimits (U ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf B))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves U (toSheaf A),
    preservesFiniteColimits_of_reflects_of_preserves U (toSheaf A)⟩

open CategoryTheory.Limits in
private theorem acyclic_restrictScalars_kflatGeneral
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    {A B : Sheaf J RingCat.{max u v}} (α : A ⟶ B)
    (L : CochainComplex (SheafOfModules.{max u v} B) ℤ) (hL : L.Acyclic) :
    (((restrictScalars α).mapHomologicalComplex (.up ℤ)).obj L).Acyclic := by
  have := (restrictScalars_exact_kflatGeneral α).1
  have := (restrictScalars_exact_kflatGeneral α).2
  intro i
  exact (hL i).map (restrictScalars α)

open CategoryTheory.Limits in
private theorem acyclic_of_restrictScalars_kflatGeneral
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    {A B : Sheaf J RingCat.{max u v}} (α : A ⟶ B)
    (L : CochainComplex (SheafOfModules.{max u v} B) ℤ)
    (hL : (((restrictScalars α).mapHomologicalComplex (.up ℤ)).obj L).Acyclic) :
    L.Acyclic := by
  intro i
  apply ((L.sc i).exact_map_iff_of_faithful (toSheaf B)).mp
  exact (hL i).map (toSheaf A)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  {R S : Sheaf J CommRingCat.{max u v}} (φ : R ⟶ S)
  (K : CochainComplex (SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)

private theorem changeOfRingsHom_id_kflatGeneral
    (M : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :
    changeOfRingsHom φ M (𝟙 M) = 𝟙 (changeOfRings φ M) := by
  let a := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj S).obj)
  let t : changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ M :=
    { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (𝟙 (M.val.obj U))
      naturality := changeOfRingsHom_naturality φ M (𝟙 M) }
  have ht : t = 𝟙 _ := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_id (M.val.obj U)
  change a.map t = 𝟙 _
  rw [ht]
  exact a.map_id _


/-- Change of rings preserves K-flatness.
Source: Stacks, Tag 0G7E.

Proof: if `F` is acyclic over `S`, its restriction `UF` is acyclic over `R`, so
`Tot(UF ⊗_R K)` is acyclic. The tensor cancellation isomorphisms
`U(F^i ⊗_S (K^j ⊗_R S)) ≅ UF^i ⊗_R K^j` assemble to an isomorphism of total complexes, and
restriction of scalars reflects acyclicity. -/
theorem changeOfRings_isKFlat (hK : CochainComplex.IsKFlatTensor K) :
    CochainComplex.IsKFlatTensor (changeOfRingsComplex φ K) :=
  open CategoryTheory.Limits MonoidalCategory in by
  classical
  let := monoidalCategory R
  let := monoidalCategory S
  let α := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map φ
  let U := restrictScalars.{max u v} α
  have hU := restrictScalars_exact_kflatGeneral α
  have : PreservesFiniteLimits U := hU.1
  have : PreservesFiniteColimits U := hU.2
  have : U.ReflectsIsomorphisms := by
    have : (U ⋙ toSheaf
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).ReflectsIsomorphisms :=
      inferInstanceAs ((toSheaf
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)).ReflectsIsomorphisms)
    exact reflectsIsomorphisms_of_comp U (toSheaf _)
  obtain ⟨e, he⟩ := exists_changeOfRings_tensorCancellation φ
  intro F hF
  let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj F).obj
    (changeOfRingsComplex φ K)
  have hcolim (D : Type) [Category.{0} D] : PreservesColimitsOfShape D U := by
    have : PreservesColimitsOfShape D (U ⋙ toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape D (toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj S)))
    have : ReflectsColimitsOfShape D (toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves U (toSheaf _)
  have : PreservesColimitsOfSize.{0, 0} U := ⟨fun {D} instD ↦ @hcolim D instD⟩
  have : U.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
  let t := (HomologicalComplex₂.mapTotalIso U T (.up ℤ)).symm
  let f :
      (((U.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
      (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        ((U.mapHomologicalComplex (.up ℤ)).obj F)).obj K :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ HomologicalComplex.Hom.isoOfComponents
        (fun j ↦ e (F.X i) (K.X j)) (by
          intro j j' hj
          change (e (F.X i) (K.X j)).hom ≫ whiskerLeft (U.obj (F.X i)) (K.d j j') =
            U.map (whiskerLeft (F.X i) (changeOfRingsHom φ (K.X j) (K.d j j'))) ≫
              (e (F.X i) (K.X j')).hom
          have hh := he (𝟙 (F.X i)) (K.d j j')
          change U.map (tensorHom (𝟙 (F.X i)) (changeOfRingsHom φ (K.X j) (K.d j j'))) ≫
              (e (F.X i) (K.X j')).hom =
            (e (F.X i) (K.X j)).hom ≫ tensorHom (U.map (𝟙 (F.X i))) (K.d j j') at hh
          rw [U.map_id, id_tensorHom, id_tensorHom] at hh
          exact hh.symm))
      (by
        intro i i' hi
        apply HomologicalComplex.Hom.ext
        funext j
        change (e (F.X i) (K.X j)).hom ≫ whiskerRight (U.map (F.d i i')) (K.X j) =
          U.map (whiskerRight (F.d i i') (changeOfRings φ (K.X j))) ≫
            (e (F.X i') (K.X j)).hom
        simpa only [changeOfRingsHom_id_kflatGeneral φ, tensorHom_id]
          using (he (F.d i i') (𝟙 (K.X j))).symm)
  have h := hK ((U.mapHomologicalComplex (.up ℤ)).obj F)
    (acyclic_restrictScalars_kflatGeneral α F hF)
  apply acyclic_of_restrictScalars_kflatGeneral α
  intro i
  exact (h i).of_iso (t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ)).symm

set_option synthInstance.maxSize 256 in
open MonoidalCategory in
/-- K-flatness is invariant under isomorphisms of complexes. -/
theorem isKFlatTensor_of_iso
    {P Q : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (e : P ≅ Q) (hP : P.IsKFlatTensor) : Q.IsKFlatTensor := by
  let := monoidalCategory R
  intro A hA n
  let F := Functor.mapBifunctorHomologicalComplex (MonoidalCategory.curriedTensor
    (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let e' : CochainComplex.mapBifunctor A P (curriedTensor _) ≅
      CochainComplex.mapBifunctor A Q (curriedTensor _) :=
    HomologicalComplex₂.total.mapIso ((F.obj A).mapIso e) (ComplexShape.up ℤ)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hP A hA n)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso e').symm |>
      (HomologicalComplex.exactAt_iff_isZero_homology _ n).2

/-- A functor agreeing with change of rings on objects and morphisms preserves K-flatness. -/
theorem isKFlatTensor_mapHomologicalComplex_of_changeOfRings
    (E : SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) ⥤
      SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj S))
    [E.Additive] (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm : ∀ {M N} (a : M ⟶ N),
      E.map a = eqToHom (h M) ≫ changeOfRingsHom φ M a ≫ eqToHom (h N).symm)
    (hK : CochainComplex.IsKFlatTensor K) :
    CochainComplex.IsKFlatTensor ((E.mapHomologicalComplex (.up ℤ)).obj K) := by
  refine isKFlatTensor_of_iso ?_ (changeOfRings_isKFlat φ K hK)
  refine (HomologicalComplex.Hom.isoOfComponents (fun i ↦ eqToIso (h (K.X i))) ?_).symm
  intro i j _
  simp [hm]
  rfl

end SheafOfModules
