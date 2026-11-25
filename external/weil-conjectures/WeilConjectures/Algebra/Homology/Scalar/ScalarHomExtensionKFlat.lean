/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import WeilConjectures.Algebra.Homology.ScalarHomCancellation.ScalarHomTensorCancellation
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Scalar extension preserves all K-flat complexes

Source: Stacks Project, Modules on Sites, Tag 05V4 and Cohomology on Sites, Tag 0G7E.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory WeilConjectures
namespace SheafOfModules
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
  [HasDerivedCategory.{w} (scalarModules J R)]
  [HasDerivedCategory.{w} (scalarModules J S)]

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] monoidalCategory

/-- Scalar extension preserves K-flatness without any flat-term assumption.
Source: Stacks 05V4 (tensor cancellation) and 0G7E (K-flat pullback)
(blueprint: lem-sfb-scalar-extension-kflat).
Proof: restriction is exact and reflects exactness on underlying abelian sheaves.
For any acyclic S-complex Z, restriction of Tot(Z tensor_S E(P)) is naturally
isomorphic to Tot(U(Z) tensor_R P), by the balanced tensor cancellation map
z tensor (s tensor p) mapped to sz tensor p. Restriction commutes with the
coproducts in the total complex; naturality of cancellation respects both signed
differentials. Exactness of restriction makes U(Z) acyclic; K-flatness of P
makes its tensor acyclic. Reflection of exactness proves the assertion. -/
private theorem kflatOfScalarExtensionIdentification
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (eo : ∀ M, E.obj M = changeOfRings a M)
    (em : ∀ {M N : scalarModules J R} (f : M ⟶ N),
      E.map f = eqToHom (eo M) ≫ changeOfRingsHom a M f ≫ eqToHom (eo N).symm)
    (P : CochainComplex (scalarModules J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
      ((scalarComplex E inferInstance).obj P) := by
  classical
  let instPresheafCoproducts (A : Sheaf J CommRingCat.{r}) (I : Type r) :
      HasColimitsOfShape (Discrete I)
        (PresheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  let := monoidalCategory R
  let := monoidalCategory S
  let U := scalarRestriction a
  let V := toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let V' := toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
  have : U.ReflectsIsomorphisms := by
    have : (U ⋙ V).ReflectsIsomorphisms :=
      inferInstanceAs V'.ReflectsIsomorphisms
    exact reflectsIsomorphisms_of_comp U V
  have hcolim (D : Type) [Category.{0} D] : PreservesColimitsOfShape D U := by
    have : PreservesColimitsOfShape D (U ⋙ V) :=
      inferInstanceAs (PreservesColimitsOfShape D V')
    have : ReflectsColimitsOfShape D V := reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves U V
  have : PreservesColimitsOfSize.{0, 0} U := ⟨fun {D} instD ↦ @hcolim D instD⟩
  obtain ⟨e, he⟩ := ScalarHomCancellation.exists_changeOfRings_tensorCancellation a
  let e' (M : scalarModules J S) (N : scalarModules J R) :
      U.obj (M ⊗ E.obj N) ≅ U.obj M ⊗ N :=
    U.mapIso (tensorIso (Iso.refl M) (eqToIso (eo N))) ≪≫ e M N
  have he' {M M' : scalarModules J S} {N N' : scalarModules J R}
      (f : M ⟶ M') (g : N ⟶ N') :
      U.map (f ⊗ₘ E.map g) ≫ (e' M' N').hom =
        (e' M N).hom ≫ (U.map f ⊗ₘ g) := by
    change U.map (f ⊗ₘ E.map g) ≫
        U.map ((𝟙 M') ⊗ₘ eqToHom (eo N')) ≫ (e M' N').hom =
      (U.map ((𝟙 M) ⊗ₘ eqToHom (eo N)) ≫ (e M N).hom) ≫
        (U.map f ⊗ₘ g)
    have hn : E.map g ≫ eqToHom (eo N') =
        eqToHom (eo N) ≫ changeOfRingsHom a N g := by
      rw [em]
      simp
    rw [← Category.assoc, ← U.map_comp, tensorHom_comp_tensorHom,
      Category.comp_id, hn]
    rw [← Category.id_comp f, ← tensorHom_comp_tensorHom, U.map_comp]
    rw [Category.assoc, he f g, Category.assoc]
    simp only [Category.id_comp]
    rfl
  intro Z hZ
  let EP := (scalarComplex E inferInstance).obj P
  let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj Z).obj EP
  have : U.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
  let t := (HomologicalComplex₂.mapTotalIso U T (.up ℤ)).symm
  let f : (((U.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
      (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        ((U.mapHomologicalComplex (.up ℤ)).obj Z)).obj P :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ HomologicalComplex.Hom.isoOfComponents
        (fun j ↦ e' (Z.X i) (P.X j)) (by
          intro j j' hj
          change (e' (Z.X i) (P.X j)).hom ≫ whiskerLeft (U.obj (Z.X i)) (P.d j j') =
            U.map (whiskerLeft (Z.X i) (E.map (P.d j j'))) ≫
              (e' (Z.X i) (P.X j')).hom
          simpa only [U.map_id, id_tensorHom] using
            (he' (𝟙 (Z.X i)) (P.d j j')).symm))
      (by
        intro i i' hi
        apply HomologicalComplex.Hom.ext
        funext j
        change (e' (Z.X i) (P.X j)).hom ≫ whiskerRight (U.map (Z.d i i')) (P.X j) =
          U.map (whiskerRight (Z.d i i') (E.obj (P.X j))) ≫
            (e' (Z.X i') (P.X j)).hom
        simpa only [E.map_id, tensorHom_id]
          using (he' (Z.d i i') (𝟙 (P.X j))).symm)
  have hUZ : ((U.mapHomologicalComplex (.up ℤ)).obj Z).Acyclic := by
    intro i
    exact (hZ i).map U
  have ht := hP ((U.mapHomologicalComplex (.up ℤ)).obj Z) hUZ
  intro i
  let W := (CochainComplex.mapBifunctor Z EP (curriedTensor _)).sc i
  apply (W.exact_map_iff_of_faithful V').mp
  have hh := (ht i).map V
  have hi := (V.mapHomologicalComplex (.up ℤ)).mapIso
    (t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ))
  exact ShortComplex.exact_of_iso
    ((HomologicalComplex.shortComplexFunctor _ _ i).mapIso hi.symm) hh

/-- Scalar extension preserves K-flatness without any flat-term assumption.
Source: Stacks 05V4 (tensor cancellation) and 0G7E (K-flat pullback)
(blueprint: lem-sfb-scalar-extension-kflat).
Proof: restriction is exact and reflects exactness on underlying abelian sheaves.
For any acyclic S-complex Z, restriction of Tot(Z tensor_S E(P)) is naturally
isomorphic to Tot(U(Z) tensor_R P), by the balanced tensor cancellation map
z tensor (s tensor p) mapped to sz tensor p. Restriction commutes with the
coproducts in the total complex; naturality of cancellation respects both signed
differentials. Exactness of restriction makes U(Z) acyclic; K-flatness of P
makes its tensor acyclic. Reflection of exactness proves the assertion. -/
theorem scalarExtension_preservesKFlat (s : ScalarDerivedPair a)
    (P : CochainComplex (scalarModules J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
      ((scalarComplex s.extension s.extension_additive).obj P) := by
  have := s.extension_additive
  exact kflatOfScalarExtensionIdentification a s.extension
    s.extension_obj s.extension_map P hP

end SheafOfModules
