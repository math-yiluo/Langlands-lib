import Langlands.AlgebraicGeometry.TensorSectionsHomologyTransport
import Langlands.Algebra.ExtendScalarsTensor
import Langlands.Cohomology.PerfectModuleComplex

/-! # Tensor homology presheaves and extension of scalars -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.TensorSections

attribute [local instance] FiniteLinearEquations.sectionsAlgebra

variable {R S : CommRingCat.{u}} [Algebra R S]

/-- Composition with `Spec S → Spec R` scales sections through `R → S`. -/
lemma sectionScalars_map (T : Over (Spec S)) :
    FiniteLinearEquations.sectionScalars
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj T) =
      (FiniteLinearEquations.sectionScalars T).comp (algebraMap R S) := by
  change ((Scheme.ΓSpecIso R).inv ≫
      (T.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop).hom =
    (CommRingCat.ofHom (algebraMap R S) ≫ (Scheme.ΓSpecIso S).inv ≫ T.hom.appTop).hom
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc]

variable (R) in
/-- Global sections of a test over `Spec S`, regarded over the coefficient ring `R`. -/
abbrev restrictedSections (T : Over (Spec S)) : ModuleCat.{u} R :=
  sectionModules.obj (op ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj T))

variable (R) in
/-- The coefficient-ring structure on the sections of a test over `Spec S`. -/
abbrev restrictedAlgebra (T : Over (Spec S)) : Algebra R Γ(T.left, ⊤) :=
  FiniteLinearEquations.sectionsAlgebra
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj T)

/-- The two coefficient actions on the sections of a test form a scalar tower. -/
lemma isScalarTower_sections (T : Over (Spec S)) :
    letI : Algebra R Γ(T.left, ⊤) := restrictedAlgebra R T
    IsScalarTower R S Γ(T.left, ⊤) := by
  let : Algebra R Γ(T.left, ⊤) := restrictedAlgebra R T
  refine IsScalarTower.of_algebraMap_eq (fun r ↦ ?_)
  change FiniteLinearEquations.sectionScalars
      ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj T) r =
    FiniteLinearEquations.sectionScalars T (algebraMap R S r)
  rw [sectionScalars_map]
  rfl

/-- Degreewise cancellation of a scalar extension against the sections of a test,
linear over the coefficient ring `R`. -/
def cancelEquiv (T : Over (Spec S)) (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj
        (sectionModules.obj (op T) ⊗ (ModuleCat.extendScalars (algebraMap R S)).obj M) ≃ₗ[R]
      (restrictedSections R T ⊗ M : ModuleCat.{u} R) := by
  letI : Algebra R Γ(T.left, ⊤) := restrictedAlgebra R T
  haveI : IsScalarTower R S Γ(T.left, ⊤) := isScalarTower_sections T
  let e₁ : (sectionModules.obj (op T) ⊗ (ModuleCat.extendScalars (algebraMap R S)).obj M :
      ModuleCat.{u} S) ≃ₗ[S] Γ(T.left, ⊤) ⊗[S] (S ⊗[R] M) :=
    TensorProduct.congr (LinearEquiv.refl S Γ(T.left, ⊤))
      (Langlands.Scheme.Modules.extendScalarsAlgebraEquiv R S M)
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S Γ(T.left, ⊤) M
  let e := e₁ ≪≫ₗ e₂
  exact
    { toFun := e
      invFun := e.symm
      map_add' := map_add e
      map_smul' := fun r x ↦ by
        change e (algebraMap R S r • x) = r • e x
        rw [map_smul, algebraMap_smul]
      left_inv := e.left_inv
      right_inv := e.right_inv }

variable (R) in
/-- The identity of global sections, from the test over `Spec S` to its image over `Spec R`. -/
def toRestricted (T : Over (Spec S)) (x : Γ(T.left, ⊤)) : restrictedSections R T := x

open scoped ChangeOfRings in
lemma cancelEquiv_tmul (T : Over (Spec S)) (M : ModuleCat.{u} R) (γ : Γ(T.left, ⊤)) (c : S)
    (m : M) :
    cancelEquiv T M (γ ⊗ₜ[S] (c ⊗ₜ[R, algebraMap R S] m)) =
      toRestricted R T (c • γ) ⊗ₜ[R] m :=
  rfl

/-- The cancellation commutes with every map of coefficient modules. -/
lemma cancelEquiv_naturality (T : Over (Spec S)) {M M' : ModuleCat.{u} R} (g : M ⟶ M')
    (x : (ModuleCat.restrictScalars (algebraMap R S)).obj
      (sectionModules.obj (op T) ⊗ (ModuleCat.extendScalars (algebraMap R S)).obj M)) :
    cancelEquiv T M'
        ((sectionModules.obj (op T) ◁ (ModuleCat.extendScalars (algebraMap R S)).map g) x) =
      (restrictedSections R T ◁ g) (cancelEquiv T M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul γ y =>
    induction y using TensorProduct.inductionOn with
    | tmul c m => rfl
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, hx, hx']

/-- Restriction of sections along a map of tests commutes with the coefficient action. -/
lemma pullSections_smul {T U : Over (Spec S)} (q : T ⟶ U) (c : S) (γ : Γ(U.left, ⊤)) :
    FiniteLinearEquations.pullSections q (c • γ) =
      c • FiniteLinearEquations.pullSections q γ :=
  map_smul (FiniteLinearEquations.pullSections q) c γ

/-- The cancellation commutes with restriction of sections along every map of tests. -/
lemma cancelEquiv_naturality_sections {T U : Over (Spec S)} (q : T ⟶ U) (M : ModuleCat.{u} R)
    (x : (ModuleCat.restrictScalars (algebraMap R S)).obj
      (sectionModules.obj (op U) ⊗ (ModuleCat.extendScalars (algebraMap R S)).obj M)) :
    cancelEquiv T M
        ((sectionModules.map q.op ▷ (ModuleCat.extendScalars (algebraMap R S)).obj M) x) =
      (sectionModules.map
          ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map q).op ▷ M)
        (cancelEquiv U M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul γ y =>
    induction y using TensorProduct.inductionOn with
    | tmul c m =>
      change toRestricted R T (c • FiniteLinearEquations.pullSections q γ) ⊗ₜ[R] m =
        toRestricted R T (FiniteLinearEquations.pullSections q (c • γ)) ⊗ₜ[R] m
      rw [pullSections_smul]
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, hx, hx']

/-- For one test, restriction of scalars of the extended tensor complex is the
original tensor complex of the sections over `R`. -/
def tensorComplexBaseChangeIso (T : Over (Spec S)) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((tensorComplex ((Cohomology.ModuleComplex.baseChange (algebraMap R S)).obj K)).obj
          (sectionModules.obj (op T))) ≅
      (tensorComplex K).obj (restrictedSections R T) :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ (cancelEquiv T (K.X i)).toModuleIso)
    (fun i j _ ↦ by
      ext x
      exact (cancelEquiv_naturality T (K.d i j) x).symm)

/-- The tensor complexes over `R` of the image tests are the restrictions of scalars of the
extended tensor complexes, naturally on the slice over `Spec S`. -/
def complexesBaseChangeIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    complexes ((Cohomology.ModuleComplex.baseChange (algebraMap R S)).obj K) ⋙
        (ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap R S)))).op ⋙ complexes K :=
  NatIso.ofComponents (fun T ↦ tensorComplexBaseChangeIso T.unop K) (by
    intro T U q
    apply HomologicalComplex.hom_ext
    intro i
    ext x
    exact cancelEquiv_naturality_sections q.unop (K.X i) x)

/-- Restriction of scalars commutes with homology of cochain complexes. -/
def restrictScalarsHomologyIso (n : ℤ) :
    (ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n ⋙
        ModuleCat.restrictScalars (algebraMap R S) :=
  NatIso.ofComponents
    (fun L ↦ (L.sc n).mapHomologyIso (ModuleCat.restrictScalars (algebraMap R S)))
    (fun f ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ n).map f)
      (ModuleCat.restrictScalars (algebraMap R S)))

/-- Restriction of scalars does not change underlying sets. -/
def restrictScalarsForgetIso :
    ModuleCat.restrictScalars (algebraMap R S) ⋙ forget (ModuleCat.{u} R) ≅
      forget (ModuleCat.{u} S) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- Tensor homology presheaves commute with base change along `R → S`, naturally on the
entire slice over `Spec S`. -/
def homologyPresheafBaseChangeIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap R S)))).op ⋙ homologyPresheaf K n ≅
      homologyPresheaf ((Cohomology.ModuleComplex.baseChange (algebraMap R S)).obj K) n :=
  Functor.isoWhiskerRight (complexesBaseChangeIso K).symm
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n ⋙
        forget (ModuleCat.{u} R) ⋙ uliftFunctor.{u + 1}) ≪≫
    Functor.isoWhiskerLeft
      (complexes ((Cohomology.ModuleComplex.baseChange (algebraMap R S)).obj K))
      (Functor.isoWhiskerRight (restrictScalarsHomologyIso n)
          (forget (ModuleCat.{u} R) ⋙ uliftFunctor.{u + 1}) ≪≫
        Functor.isoWhiskerLeft
          (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n)
          (Functor.isoWhiskerRight restrictScalarsForgetIso uliftFunctor.{u + 1}))

end Langlands.AlgebraicGeometry.TensorSections
