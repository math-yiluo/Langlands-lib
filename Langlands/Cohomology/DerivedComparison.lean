import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Additive

/-!
# Comparing right derived functors along exact functors

An exact functor that preserves injective objects carries injective
resolutions to injective resolutions. Consequently right derived functors
commute with such a functor on the source and with any exact functor on the
target.
-/

noncomputable section

namespace Langlands.Cohomology.DerivedComparison

open CategoryTheory CategoryTheory.Limits

universe vC uC vD uD vE uE vF uF

variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]

section Resolution

variable (T : C ⥤ D) [T.Additive] [T.PreservesHomology] [T.PreservesInjectiveObjects]

/-- An exact functor preserving injective objects maps an injective resolution
to an injective resolution of the image. -/
abbrev mapInjectiveResolution {X : C} (I : InjectiveResolution X) :
    InjectiveResolution (T.obj X) where
  cocomplex := (T.mapHomologicalComplex _).obj I.cocomplex
  injective n := T.injective_obj_of_injective (I.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).inv.app X ≫
    (T.mapHomologicalComplex _).map I.ι
  quasiIso := inferInstance

/-- The mapped resolution has the termwise image complex. -/
theorem mapInjectiveResolution_cocomplex {X : C} (I : InjectiveResolution X) :
    (mapInjectiveResolution T I).cocomplex = (T.mapHomologicalComplex _).obj I.cocomplex :=
  rfl

/-- In degree zero, the mapped augmentation is the image of the augmentation. -/
theorem mapInjectiveResolution_ι_f_zero {X : C} (I : InjectiveResolution X) :
    (mapInjectiveResolution T I).ι.f 0 = T.map (I.ι.f 0) := by
  simp only [mapInjectiveResolution, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, CochainComplex.single₀ObjXSelf, Iso.refl_hom,
    Iso.refl_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

/-- The image of a chain map lifting `f` lifts `T.map f`. -/
theorem mapInjectiveResolution_comm {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    (mapInjectiveResolution T I).ι.f 0 ≫ ((T.mapHomologicalComplex _).map φ).f 0 =
      T.map f ≫ (mapInjectiveResolution T J).ι.f 0 := by
  rw [mapInjectiveResolution_ι_f_zero, mapInjectiveResolution_ι_f_zero,
    Functor.mapHomologicalComplex_map_f]
  exact (T.map_comp _ _).symm.trans ((congrArg T.map comm).trans (T.map_comp _ _))

end Resolution

section Homology

variable {E : Type uE} [Category.{vE} E] [Abelian E]
variable {E' : Type uF} [Category.{vF} E'] [Abelian E']
variable (P : E ⥤ E') [P.Additive] [P.PreservesHomology]

/-- An exact functor commutes with the homology of cochain complexes. -/
def mapHomologyIso (K : CochainComplex E ℕ) (q : ℕ) :
    (HomologicalComplex.homologyFunctor E' _ q).obj ((P.mapHomologicalComplex _).obj K) ≅
      P.obj ((HomologicalComplex.homologyFunctor E _ q).obj K) :=
  (K.sc q).mapHomologyIso P

/-- The homology comparison is natural in the complex. -/
@[reassoc]
theorem mapHomologyIso_inv_naturality {K L : CochainComplex E ℕ} (φ : K ⟶ L) (q : ℕ) :
    P.map ((HomologicalComplex.homologyFunctor E _ q).map φ) ≫ (mapHomologyIso P L q).inv =
      (mapHomologyIso P K q).inv ≫
        (HomologicalComplex.homologyFunctor E' _ q).map ((P.mapHomologicalComplex _).map φ) :=
  ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor E (ComplexShape.up ℕ) q).map φ) P

end Homology

section Comparison

variable {E : Type uE} [Category.{vE} E] [Abelian E]
variable {E' : Type uF} [Category.{vF} E'] [Abelian E']
variable (Φ : C ⥤ E) [Φ.Additive] (P : E ⥤ E') [P.Additive]
variable (T : C ⥤ D) [T.Additive] (Ψ : D ⥤ E') [Ψ.Additive] (e : Φ ⋙ P ≅ T ⋙ Ψ)

/-- The termwise isomorphism of complexes induced by `e`. -/
def complexIso (K : CochainComplex C ℕ) :
    (P.mapHomologicalComplex _).obj ((Φ.mapHomologicalComplex _).obj K) ≅
      (Ψ.mapHomologicalComplex _).obj ((T.mapHomologicalComplex _).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => e.app (K.X n))
    (fun i j _ => (e.hom.naturality (K.d i j)).symm)

/-- The termwise isomorphism is natural in the complex. -/
@[reassoc]
theorem complexIso_hom_naturality {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    (P.mapHomologicalComplex _).map ((Φ.mapHomologicalComplex _).map φ) ≫
        (complexIso Φ P T Ψ e L).hom =
      (complexIso Φ P T Ψ e K).hom ≫
        (Ψ.mapHomologicalComplex _).map ((T.mapHomologicalComplex _).map φ) := by
  ext n
  exact e.hom.naturality (φ.f n)

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
variable [P.PreservesHomology] [T.PreservesHomology] [T.PreservesInjectiveObjects]

/-- The comparison isomorphism computed with a given injective resolution. -/
def compIsoOfResolution {X : C} (I : InjectiveResolution X) (q : ℕ) :
    P.obj ((Φ.rightDerived q).obj X) ≅ (Ψ.rightDerived q).obj (T.obj X) :=
  P.mapIso (I.isoRightDerivedObj Φ q) ≪≫ (mapHomologyIso P _ q).symm ≪≫
    (HomologicalComplex.homologyFunctor E' _ q).mapIso (complexIso Φ P T Ψ e I.cocomplex) ≪≫
    ((mapInjectiveResolution T I).isoRightDerivedObj Ψ q).symm

/-- The comparison isomorphisms are compatible with any chain map lifting a
morphism between the resolved objects. -/
theorem compIsoOfResolution_naturality {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    P.map ((Φ.rightDerived q).map f) ≫ (compIsoOfResolution Φ P T Ψ e J q).hom =
      (compIsoOfResolution Φ P T Ψ e I q).hom ≫ (Ψ.rightDerived q).map (T.map f) := by
  have s1 := InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ comm Φ q
  have s4 := InjectiveResolution.isoRightDerivedObj_inv_naturality (T.map f)
    (mapInjectiveResolution T I) (mapInjectiveResolution T J)
    ((T.mapHomologicalComplex _).map φ) (mapInjectiveResolution_comm T f I J φ comm) Ψ q
  simp only [Functor.comp_map] at s1 s4
  simp only [compIsoOfResolution, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [s4, ← (HomologicalComplex.homologyFunctor E' (ComplexShape.up ℕ) q).map_comp_assoc,
    ← complexIso_hom_naturality, Functor.map_comp_assoc, ← mapHomologyIso_inv_naturality_assoc,
    ← P.map_comp_assoc, ← P.map_comp_assoc, ← s1]

/-- If `Φ ⋙ P ≅ T ⋙ Ψ` with `P` exact and `T` exact and preserving injective
objects, then the right derived functors satisfy
`Φ.rightDerived q ⋙ P ≅ T ⋙ Ψ.rightDerived q`. -/
def rightDerivedCompIso (q : ℕ) : Φ.rightDerived q ⋙ P ≅ T ⋙ Ψ.rightDerived q :=
  NatIso.ofComponents (fun X => compIsoOfResolution Φ P T Ψ e (injectiveResolution X) q)
    (fun {X Y} f => compIsoOfResolution_naturality Φ P T Ψ e f _ _
      (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X))
      (InjectiveResolution.desc_commutes_zero f _ _) q)

end Comparison

end Langlands.Cohomology.DerivedComparison
