import Langlands.Geometry.EtaleComplexPullbackCoherence

/-! # Geometric identity and composition on actual derived inverse images -/

noncomputable section

universe u wX wZ wV

namespace Langlands.Geometry.EtaleDerivedInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z V : Scheme.{u}} (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]

/-- Identity for the actual unbounded derived geometric inverse image,
by localization of the ordinary geometric comparison. -/
def functorId (X : Scheme.{u}) [HasDerivedCategory.{wX} (ModuleSheaf X R)] :
    functor (𝟙 X) R ≅ 𝟭 (DerivedCategory (ModuleSheaf X R)) := by
  dsimp only [functor]
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X R) (.up ℤ))
    ((inverseImage (𝟙 X) R).mapHomologicalComplex _ ⋙ DerivedCategory.Q)
    DerivedCategory.Q _ _
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (inverseImageId R X) (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso (ModuleSheaf X R) (.up ℤ))
      DerivedCategory.Q ≪≫ Functor.leftUnitor _)

/-- Recovery of the identity comparison on every complex representative. -/
@[reassoc] theorem functorId_hom_app_Q (K : CochainComplex (ModuleSheaf X R) ℤ) :
    (functorId R X).hom.app (DerivedCategory.Q.obj K) =
      (factors (𝟙 X) R).hom.app K ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (inverseImageId R X) (.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso (ModuleSheaf X R) (.up ℤ)).hom.app K) := by
  dsimp only [functorId, functor]
  exact (Localization.liftNatTrans_app ..).trans (by
    simp [Localization.Lifting.iso, factors])

/-- The same identity isomorphism restricted to bounded-below derived objects. -/
def plusFunctorId (X : Scheme.{u}) [HasDerivedCategory.{wX} (ModuleSheaf X R)] :
    plusFunctor (𝟙 X) R ≅ 𝟭 (DerivedCategory.Plus (ModuleSheaf X R)) :=
  NatIso.ofComponents
    (fun K => (DerivedCategory.Plus.ι (C := ModuleSheaf X R)).preimageIso
      ((functorId R X).app K.obj))
    (fun {_K _L} a => by
      apply (DerivedCategory.Plus.ι (C := ModuleSheaf X R)).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (functorId R X).hom.naturality a.hom)

/-- The bounded-below identity comparison is exactly localization of the
constructed coefficient-complex identity, through the actual factors. -/
@[reassoc] theorem plusFunctorId_hom_app_Q
    (K : CochainComplex.Plus (ModuleSheaf X R)) :
    (plusFunctorId R X).hom.app (DerivedCategory.Plus.Q.obj K) =
      (plusFactors (𝟙 X) R).hom.app K ≫
        DerivedCategory.Plus.Q.map ((inverseImageComplexId R X).hom.app K) := by
  apply (DerivedCategory.Plus.ι (C := ModuleSheaf X R)).map_injective
  simp only [plusFunctorId, NatIso.ofComponents_hom_app, Iso.app_hom,
    Functor.preimageIso_hom, Functor.map_preimage, Functor.map_comp]
  change (functorId R X).hom.app (DerivedCategory.Q.obj K.obj) =
    (DerivedCategory.Plus.ι (C := ModuleSheaf X R)).map
      ((plusFactors (𝟙 X) R).hom.app K) ≫
    DerivedCategory.Q.map ((inverseImageComplexId R X).hom.app K).hom
  dsimp only [plusFactors, NatIso.ofComponents_hom_app, Iso.app_hom,
    Functor.preimageIso_hom]
  rw [Functor.map_preimage, functorId_hom_app_Q]
  congr 1
  change DerivedCategory.Q.map _ = DerivedCategory.Q.map _
  congr 1
  apply HomologicalComplex.hom_ext
  intro i
  simp [inverseImageComplexId_hom_f]

variable [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wV} (ModuleSheaf V R)]

/-- Composition for actual unbounded derived geometric inverse images,
by localization of the actual ordinary comparison. -/
def functorComp (f : Z ⟶ X) (g : V ⟶ Z) :
    functor f R ⋙ functor g R ≅ functor (g ≫ f) R := by
  dsimp only [functor]
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleSheaf X R) (.up ℤ))
    ((inverseImage f R).mapHomologicalComplex _ ⋙
      (inverseImage g R).mapHomologicalComplex _ ⋙ DerivedCategory.Q)
    ((inverseImage (g ≫ f) R).mapHomologicalComplex _ ⋙ DerivedCategory.Q) _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (inverseImageComp R f g) (.up ℤ))
        DerivedCategory.Q)

/-- The actual composition comparison on every complex representative. -/
@[reassoc] theorem functorComp_hom_app_Q (f : Z ⟶ X) (g : V ⟶ Z)
    (K : CochainComplex (ModuleSheaf X R) ℤ) :
    (functorComp R f g).hom.app (DerivedCategory.Q.obj K) =
      (functor g R).map ((factors f R).hom.app K) ≫
        (factors g R).hom.app ((inverseImage f R).mapHomologicalComplex _ |>.obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (inverseImageComp R f g) (.up ℤ)).hom.app K) ≫
        (factors (g ≫ f) R).inv.app K := by
  dsimp only [functorComp, functor]
  exact (Localization.liftNatTrans_app ..).trans (by
    simp [Localization.Lifting.iso, factors, Category.assoc])

/-- The same actual composition comparison on bounded-below derived objects. -/
def plusFunctorComp (f : Z ⟶ X) (g : V ⟶ Z) :
    plusFunctor f R ⋙ plusFunctor g R ≅ plusFunctor (g ≫ f) R :=
  NatIso.ofComponents
    (fun K => (DerivedCategory.Plus.ι (C := ModuleSheaf V R)).preimageIso
      ((functorComp R f g).app K.obj))
    (fun {_K _L} a => by
      apply (DerivedCategory.Plus.ι (C := ModuleSheaf V R)).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (functorComp R f g).hom.naturality a.hom)

/-- Localization of the constructed coefficient-complex composition, normalized
by the existing inverse-image factors, is the actual derived comparison. -/
@[reassoc] theorem plusFunctorComp_hom_app_Q (f : Z ⟶ X) (g : V ⟶ Z)
    (K : CochainComplex.Plus (ModuleSheaf X R)) :
    (plusFunctorComp R f g).hom.app (DerivedCategory.Plus.Q.obj K) =
      (plusFunctor g R).map ((plusFactors f R).hom.app K) ≫
        (plusFactors g R).hom.app ((inverseImage f R).mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Plus.Q.map ((inverseImageComplexComp R f g).hom.app K) ≫
        (plusFactors (g ≫ f) R).inv.app K := by
  apply (DerivedCategory.Plus.ι (C := ModuleSheaf V R)).map_injective
  simp only [plusFunctorComp, NatIso.ofComponents_hom_app, Iso.app_hom,
    Functor.preimageIso_hom, Functor.map_preimage, Functor.map_comp]
  change (functorComp R f g).hom.app (DerivedCategory.Q.obj K.obj) =
    (functor g R).map ((DerivedCategory.Plus.ι (C := ModuleSheaf Z R)).map
      ((plusFactors f R).hom.app K)) ≫
    (DerivedCategory.Plus.ι (C := ModuleSheaf V R)).map
      ((plusFactors g R).hom.app ((inverseImage f R).mapCochainComplexPlus.obj K)) ≫
    DerivedCategory.Q.map ((inverseImageComplexComp R f g).hom.app K).hom ≫
    (DerivedCategory.Plus.ι (C := ModuleSheaf V R)).map
      ((plusFactors (g ≫ f) R).inv.app K)
  dsimp only [plusFactors, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    Iso.app_hom, Iso.app_inv, Functor.preimageIso_hom, Functor.preimageIso_inv]
  simp only [Functor.map_preimage]
  rw [functorComp_hom_app_Q]
  congr 1
  congr 1
  congr 1
  congr 1
  apply HomologicalComplex.hom_ext
  intro i
  simp [inverseImageComplexComp_hom_f]

end Langlands.Geometry.EtaleDerivedInverseImage
