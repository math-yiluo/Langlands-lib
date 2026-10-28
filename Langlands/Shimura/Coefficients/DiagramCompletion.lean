import Langlands.Shimura.Coefficients.VaryingCoverReduction

/-! # Actual adic completion of varying-group coefficient diagrams -/

noncomputable section

universe u v uJ vJ

namespace Langlands.Coefficients.AdicSystem

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The actual compatible-sequence module, functorially in linear maps. -/
def completionFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (AdicCompletion I M)
  map f := ModuleCat.ofHom ((AdicCompletion.map I f.hom).restrictScalars R)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun (AdicCompletion.map_id I M) x
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (AdicCompletion.map_comp_apply I f.hom g.hom x).symm

/-- Evaluation of the completion in the genuine power quotient. -/
def completionProjection (n : ℕ) : completionFunctor I ⟶ powerReduction I n where
  app M := ModuleCat.ofHom (AdicCompletion.eval I M n)
  naturality {M N} f := by
    ext x
    rfl

/-- The canonical map from a module to its actual completion. -/
def completionUnit : 𝟭 (ModuleCat.{v} R) ⟶ completionFunctor I where
  app M := ModuleCat.ofHom (AdicCompletion.of I M)
  naturality {M N} f := by
    ext x
    rfl

@[reassoc (attr := simp)]
theorem completionUnit_projection (n : ℕ) :
    completionUnit I ≫ completionProjection I n = quotientMap I n := by
  ext M x
  rfl

end Langlands.Coefficients.AdicSystem

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {J : Type uJ} [Category.{vJ} J] {D : J ⥤ GrpCat.{u}}

/-- Complete every module, action and transition in the coefficient diagram. -/
def coefficientDiagramCompletion :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      EquivariantDiagram D (ModuleCat.{u} R) :=
  EquivariantDiagram.mapFunctor (Langlands.Coefficients.AdicSystem.completionFunctor I)

/-- The actual evaluation maps are morphisms of varying-group diagrams. -/
def coefficientDiagramCompletionProjection (n : ℕ) :
    coefficientDiagramCompletion (D := D) I ⟶ (coefficientDiagramPowers I).obj (op n) :=
  EquivariantDiagram.mapNatTrans (Langlands.Coefficients.AdicSystem.completionProjection I n)

/-- The original diagram maps naturally into its completion. -/
def coefficientDiagramCompletionUnit :
    𝟭 (EquivariantDiagram D (ModuleCat.{u} R)) ⟶ coefficientDiagramCompletion I :=
  EquivariantDiagram.mapNatTrans (Langlands.Coefficients.AdicSystem.completionUnit I)

@[reassoc (attr := simp)]
theorem coefficientDiagramCompletionUnit_projection (n : ℕ) :
    coefficientDiagramCompletionUnit (D := D) I ≫
        coefficientDiagramCompletionProjection I n = coefficientDiagramPowerUnit I n := by
  apply NatTrans.ext
  funext M
  apply EquivariantDiagram.Hom.ext
  apply NatTrans.ext
  funext j
  rfl

/-- Completion evaluations satisfy all power-transition equations. -/
@[reassoc (attr := simp)]
theorem coefficientDiagramCompletionProjection_transition {m n : ℕ} (h : m ≤ n) :
    coefficientDiagramCompletionProjection (D := D) I n ≫
        (coefficientDiagramPowers I).map (homOfLE h).op =
      coefficientDiagramCompletionProjection I m := by
  apply NatTrans.ext
  funext M
  apply EquivariantDiagram.Hom.ext
  apply NatTrans.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact x.property h

/-- The completion is the vertex of the genuine power-evaluation cone. -/
def coefficientDiagramCompletionCone (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    Cone ((coefficientDiagramReductionFunctor I).obj M) where
  pt := (coefficientDiagramCompletion I).obj M
  π :=
    { app n := (coefficientDiagramCompletionProjection I n.unop).app M
      naturality {_m _n} f := by
        change 𝟙 _ ≫ (coefficientDiagramCompletionProjection I _n.unop).app M =
          (coefficientDiagramCompletionProjection I _m.unop).app M ≫
            ((coefficientDiagramPowers I).map f).app M
        rw [Category.id_comp]
        simpa only [NatTrans.comp_app,
          show (homOfLE (leOfHom f.unop)).op = f from Subsingleton.elim _ _] using
          (congrArg (fun a => a.app M)
            (coefficientDiagramCompletionProjection_transition (D := D) I
              (leOfHom f.unop))).symm }

/-- A compatible cone lifts by the actual module completion lift at each index. -/
def coefficientDiagramCompletionLift (M : EquivariantDiagram D (ModuleCat.{u} R))
    (s : Cone ((coefficientDiagramReductionFunctor I).obj M)) :
    s.pt ⟶ (coefficientDiagramCompletion I).obj M where
  hom :=
    { app j := ModuleCat.ofHom (AdicCompletion.lift I
        (fun n => ((s.π.app (op n)).hom.app j).hom)
        (by
          intro m n h
          exact ModuleCat.hom_ext_iff.mp
            (congrArg (fun a => a.hom.app j) (s.w (homOfLE h).op))))
      naturality {i j} f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply AdicCompletion.ext
        intro n
        exact congrArg (fun a : s.pt.obj.obj i ⟶ _ => a x)
          ((s.π.app (op n)).hom.naturality f) }
  comm j g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply AdicCompletion.ext
    intro n
    exact congrArg (fun a : s.pt.obj.obj j ⟶ _ => a x) ((s.π.app (op n)).comm j g)

@[reassoc (attr := simp)]
theorem coefficientDiagramCompletionLift_projection
    (M : EquivariantDiagram D (ModuleCat.{u} R))
    (s : Cone ((coefficientDiagramReductionFunctor I).obj M)) (n : ℕ) :
    coefficientDiagramCompletionLift I M s ≫
        (coefficientDiagramCompletionProjection I n).app M = s.π.app (op n) := by
  apply EquivariantDiagram.Hom.ext
  apply NatTrans.ext
  funext j
  rfl

/-- The constructed completion cone is a limit in varying-group diagrams. -/
def coefficientDiagramCompletionConeIsLimit
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    IsLimit (coefficientDiagramCompletionCone I M) where
  lift := coefficientDiagramCompletionLift I M
  fac s n := coefficientDiagramCompletionLift_projection I M s n.unop
  uniq s f hf := by
    apply EquivariantDiagram.Hom.ext
    apply NatTrans.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply AdicCompletion.ext
    intro n
    exact congrArg (fun a : s.pt.obj.obj j ⟶ _ => a x)
      (congrArg (fun a => a.hom.app j) (hf (op n)))

/-- Completion evaluation is surjective in every module coordinate. -/
theorem coefficientDiagramCompletionProjection_surjective
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (j : J) (n : ℕ) :
    Function.Surjective (((coefficientDiagramCompletionProjection I n).app M).hom.app j) :=
  AdicCompletion.eval_surjective I (M.obj.obj j) n

end Langlands.Shimura.Coefficients
