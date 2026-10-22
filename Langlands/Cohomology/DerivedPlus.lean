import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Derived complexes in the bounded below derived category

For an additive functor `F` between abelian categories whose source has enough
injectives, the derived complex of an object `X` is Mathlib's right derived
functor on bounded below derived categories applied to `X` placed in degree
zero. It is represented by `F` applied to any injective resolution of `X`, and
its cohomology in degree `n ≥ 0` is the classical right derived functor
`F.rightDerived n` at `X`. Its cohomology in negative degrees vanishes.
-/

noncomputable section

namespace Langlands.Cohomology.DerivedPlus

open CategoryTheory CategoryTheory.Limits

section Extend

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (K : HomologicalComplex C c)

/-- Termwise comparison between extending the image of a complex and the image
of the extended complex. -/
def extendXMapIso : (i : Option ι) →
    HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) i ≅
      F.obj (HomologicalComplex.extend.X K i)
  | some _ => Iso.refl _
  | none => IsZero.iso (HomologicalComplex.extend.isZero_X _ rfl)
      (F.map_isZero (HomologicalComplex.extend.isZero_X K rfl))

theorem extendXMapIso_hom_d (i j : Option ι) :
    (extendXMapIso F K i).hom ≫ F.map (HomologicalComplex.extend.d K i j) =
      HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) i j ≫
        (extendXMapIso F K j).hom :=
  match i, j with
  | none, _ => by
      simp only [HomologicalComplex.extend.d_none_eq_zero _ _ _ rfl, F.map_zero, comp_zero,
        zero_comp]
  | some i, some j => by
      dsimp [extendXMapIso, HomologicalComplex.extend.d]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  | some _, none => by
      simp only [HomologicalComplex.extend.d_none_eq_zero' _ _ _ rfl, F.map_zero, comp_zero,
        zero_comp]

/-- Extending the image of a complex is isomorphic to the image of the extended
complex. -/
def mapExtendIso (e : c.Embedding c') :
    ((F.mapHomologicalComplex c).obj K).extend e ≅
      (F.mapHomologicalComplex c').obj (K.extend e) :=
  HomologicalComplex.Hom.isoOfComponents (fun i' => extendXMapIso F K (e.r i'))
    (fun _ _ _ => extendXMapIso_hom_d F K _ _)

end Extend

section Derived

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive]

/-- An injective resolution, extended by zero to a bounded below complex
indexed by the integers. -/
def resolutionPlus {X : C} (R : InjectiveResolution X) : CochainComplex.Plus C :=
  ⟨R.cochainComplex, ⟨0, inferInstance⟩⟩

/-- The derived complex functor: an object placed in degree zero, followed by
the right derived functor on bounded below derived categories. -/
def derivedComplex : C ⥤ DerivedCategory.Plus D :=
  DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus

/-- An object in degree zero is isomorphic, in the bounded below derived
category, to any of its injective resolutions. -/
def singleIsoOfResolution {X : C} (R : InjectiveResolution X) :
    (DerivedCategory.Plus.singleFunctor C 0).obj X ≅
      DerivedCategory.Plus.Q.obj (resolutionPlus R) :=
  have : IsIso (DerivedCategory.Q.map R.ι') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := C) R.ι').2 inferInstance
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.Plus.singleFunctorιIso C 0).app X ≪≫
      (DerivedCategory.singleFunctorIsoCompQ C 0).app X ≪≫
      asIso (DerivedCategory.Q.map R.ι') ≪≫
      ((DerivedCategory.Plus.QCompιIso C).app (resolutionPlus R)).symm)

instance injective_resolutionPlus_X {X : C} (R : InjectiveResolution X) (n : ℤ) :
    Injective ((resolutionPlus R).obj.X n) :=
  inferInstanceAs (Injective (R.cochainComplex.X n))

instance isIso_rightDerivedFunctorPlusUnit_app {X : C} (R : InjectiveResolution X) :
    IsIso (F.rightDerivedFunctorPlusUnit.app (resolutionPlus R)) := by
  rw [F.rightDerivedFunctorPlusUnit_app]
  have : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient C).obj (resolutionPlus R))) := inferInstance
  have : IsIso (DerivedCategory.Plus.Qh.map
      (F.quotientCompMapHomotopyCategoryPlusIso.inv.app (resolutionPlus R))) := inferInstance
  have : IsIso (F.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.quotientCompQhIso C).hom.app (resolutionPlus R))) := inferInstance
  have : IsIso ((DerivedCategory.Plus.quotientCompQhIso D).inv.app
      (F.mapCochainComplexPlus.obj (resolutionPlus R))) := inferInstance
  exact IsIso.comp_isIso

/-- The derived complex of `X` is `F` applied to any injective resolution of
`X`. -/
def derivedComplexIso {X : C} (R : InjectiveResolution X) :
    (derivedComplex F).obj X ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj (resolutionPlus R)) :=
  F.rightDerivedFunctorPlus.mapIso (singleIsoOfResolution R) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app (resolutionPlus R))).symm

/-- Cohomology of the derived complex in a degree `n` is the cohomology of `F`
applied to the integer-indexed injective resolution. -/
def homologyResolutionIso {X : C} (R : InjectiveResolution X) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj ((derivedComplex F).obj X) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex).homology n :=
  (DerivedCategory.Plus.homologyFunctor D n).mapIso (derivedComplexIso F R) ≪≫
    (DerivedCategory.homologyFunctor D n).mapIso
      ((DerivedCategory.Plus.QCompιIso D).app (F.mapCochainComplexPlus.obj (resolutionPlus R))) ≪≫
    (DerivedCategory.homologyFunctorFactors D n).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex)

/-- In degree `n : ℕ`, cohomology of the derived complex of `X` is the right
derived functor `F.rightDerived n` at `X`, computed with any injective
resolution. -/
def homologyIso {X : C} (R : InjectiveResolution X) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj ((derivedComplex F).obj X) ≅
      (F.rightDerived n).obj X :=
  homologyResolutionIso F R n ≪≫
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).mapIso
      (mapExtendIso F R.cocomplex ComplexShape.embeddingUpNat).symm ≪≫
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) rfl ≪≫
    (R.isoRightDerivedObj F n).symm

/-- Cohomology of the derived complex vanishes in negative degrees. -/
theorem isZero_homology_of_neg (X : C) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D n).obj ((derivedComplex F).obj X)) := by
  let R := injectiveResolution X
  refine IsZero.of_iso ?_ (homologyResolutionIso F R n)
  apply ShortComplex.isZero_homology_of_isZero_X₂
  exact F.map_isZero (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 n hn)

end Derived

end Langlands.Cohomology.DerivedPlus
