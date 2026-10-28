import Langlands.Shimura.Coefficients.DiagramCompletion
import Langlands.CategoryTheory.EquivariantDiagramPreadditive
import Mathlib.Algebra.Homology.Additive

/-! # Actual power reductions and adic completion of coefficient complexes -/

noncomputable section

universe u v uJ vJ uι

namespace Langlands.Coefficients.AdicSystem

open CategoryTheory

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Ideal-power reduction preserves addition of actual module morphisms. -/
instance powerReduction_additive (n : ℕ) : (powerReduction.{u, v} I n).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    change ((LinearMap.reduceModIdeal (I ^ n)) (f.hom + g.hom)).restrictScalars R =
      ((LinearMap.reduceModIdeal (I ^ n)) f.hom).restrictScalars R +
        ((LinearMap.reduceModIdeal (I ^ n)) g.hom).restrictScalars R
    rw [map_add, LinearMap.restrictScalars_add]

/-- Compatible-sequence completion preserves addition of module morphisms. -/
instance completionFunctor_additive : (completionFunctor.{u, v} I).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    change ((AdicCompletion.map I) (f.hom + g.hom)).restrictScalars R =
      ((AdicCompletion.map I) f.hom).restrictScalars R +
        ((AdicCompletion.map I) g.hom).restrictScalars R
    rw [map_add, LinearMap.restrictScalars_add]

end Langlands.Coefficients.AdicSystem

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits Opposite

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {J : Type uJ} [Category.{vJ} J] {D : J ⥤ GrpCat.{u}}
variable {ι : Type uι} (c : ComplexShape ι)

instance coefficientDiagramPower_additive (n : ℕᵒᵖ) :
    ((coefficientDiagramPowers (D := D) I).obj n).Additive :=
  inferInstanceAs
    (EquivariantDiagram.mapFunctor
      (Langlands.Coefficients.AdicSystem.powerReduction I n.unop)).Additive

instance coefficientDiagramCompletion_additive :
    (coefficientDiagramCompletion (D := D) I).Additive :=
  inferInstanceAs
    (EquivariantDiagram.mapFunctor
      (Langlands.Coefficients.AdicSystem.completionFunctor I)).Additive

/-- The actual power-quotient endofunctors on complexes of coefficient diagrams. -/
def coefficientComplexPowers :
    ℕᵒᵖ ⥤
      (HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
        HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) where
  obj n := ((coefficientDiagramPowers I).obj n).mapHomologicalComplex c
  map f := ((coefficientDiagramPowers I).map f).mapHomologicalComplex c
  map_id n := by
    rw [(coefficientDiagramPowers I).map_id, NatTrans.mapHomologicalComplex_id]
  map_comp f g := by
    rw [(coefficientDiagramPowers I).map_comp, NatTrans.mapHomologicalComplex_comp]

/-- The full inverse system of quotient complexes, functorial in the input complex. -/
def coefficientComplexReductionFunctor :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      (ℕᵒᵖ ⥤ HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) :=
  (coefficientComplexPowers I c).flip

/-- The quotient chain maps, natural in the original complex. -/
def coefficientComplexPowerUnit (n : ℕ) :
    𝟭 (HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) ⟶
      (coefficientComplexPowers I c).obj (op n) :=
  (Functor.mapHomologicalComplexIdIso _ c).inv ≫
    (coefficientDiagramPowerUnit I n).mapHomologicalComplex c

@[reassoc (attr := simp)]
theorem coefficientComplexPowerUnit_transition {m n : ℕ} (h : m ≤ n) :
    coefficientComplexPowerUnit (D := D) I c n ≫
        (coefficientComplexPowers I c).map (homOfLE h).op =
      coefficientComplexPowerUnit I c m := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.hom_ext
  intro i
  change (𝟙 _ ≫ (coefficientDiagramPowerUnit I n).app (K.X i)) ≫
    ((coefficientDiagramPowers I).map (homOfLE h).op).app (K.X i) =
      𝟙 _ ≫ (coefficientDiagramPowerUnit I m).app (K.X i)
  simp only [Category.id_comp]
  exact NatTrans.congr_app (coefficientDiagramPowerUnit_transition (D := D) I h) (K.X i)

/-- Apply the actual diagram completion functor to every degree and differential. -/
def coefficientComplexCompletion :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c :=
  (coefficientDiagramCompletion I).mapHomologicalComplex c

/-- Evaluation of a completed complex in each actual quotient complex. -/
def coefficientComplexCompletionProjection (n : ℕ) :
    coefficientComplexCompletion (D := D) I c ⟶
      (coefficientComplexPowers I c).obj (op n) :=
  (coefficientDiagramCompletionProjection I n).mapHomologicalComplex c

/-- The canonical chain map from a complex to its degreewise completion. -/
def coefficientComplexCompletionUnit :
    𝟭 (HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) ⟶
      coefficientComplexCompletion I c :=
  (Functor.mapHomologicalComplexIdIso _ c).inv ≫
    (coefficientDiagramCompletionUnit I).mapHomologicalComplex c

@[reassoc (attr := simp)]
theorem coefficientComplexCompletionUnit_projection (n : ℕ) :
    coefficientComplexCompletionUnit (D := D) I c ≫
        coefficientComplexCompletionProjection I c n = coefficientComplexPowerUnit I c n := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.hom_ext
  intro i
  change (𝟙 _ ≫ (coefficientDiagramCompletionUnit I).app (K.X i)) ≫
    (coefficientDiagramCompletionProjection I n).app (K.X i) =
      𝟙 _ ≫ (coefficientDiagramPowerUnit I n).app (K.X i)
  simp only [Category.id_comp]
  exact NatTrans.congr_app (coefficientDiagramCompletionUnit_projection (D := D) I n) (K.X i)

@[reassoc (attr := simp)]
theorem coefficientComplexCompletionProjection_transition {m n : ℕ} (h : m ≤ n) :
    coefficientComplexCompletionProjection (D := D) I c n ≫
        (coefficientComplexPowers I c).map (homOfLE h).op =
      coefficientComplexCompletionProjection I c m := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.hom_ext
  intro i
  exact NatTrans.congr_app
    (coefficientDiagramCompletionProjection_transition (D := D) I h) (K.X i)

@[simp]
theorem coefficientComplexPowers_obj_X (n : ℕᵒᵖ)
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (i : ι) :
    (((coefficientComplexPowers I c).obj n).obj K).X i =
      ((coefficientDiagramPowers I).obj n).obj (K.X i) := rfl

@[simp]
theorem coefficientComplexPowers_obj_d (n : ℕᵒᵖ)
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (i j : ι) :
    (((coefficientComplexPowers I c).obj n).obj K).d i j =
      ((coefficientDiagramPowers I).obj n).map (K.d i j) := rfl

@[simp]
theorem coefficientComplexPowers_map_f (n : ℕᵒᵖ)
    {K L : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c}
    (f : K ⟶ L) (i : ι) :
    (((coefficientComplexPowers I c).obj n).map f).f i =
      ((coefficientDiagramPowers I).obj n).map (f.f i) := rfl

@[simp]
theorem coefficientComplexCompletion_obj_X
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (i : ι) :
    ((coefficientComplexCompletion I c).obj K).X i =
      (coefficientDiagramCompletion I).obj (K.X i) := rfl

@[simp]
theorem coefficientComplexCompletion_obj_d
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (i j : ι) :
    ((coefficientComplexCompletion I c).obj K).d i j =
      (coefficientDiagramCompletion I).map (K.d i j) := rfl

@[simp]
theorem coefficientComplexCompletion_map_f
    {K L : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c}
    (f : K ⟶ L) (i : ι) :
    ((coefficientComplexCompletion I c).map f).f i =
      (coefficientDiagramCompletion I).map (f.f i) := rfl

/-- The actual completion evaluations form a cone of chain maps. -/
def coefficientComplexCompletionCone
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) :
    Cone ((coefficientComplexReductionFunctor I c).obj K) where
  pt := (coefficientComplexCompletion I c).obj K
  π :=
    { app n := (coefficientComplexCompletionProjection I c n.unop).app K
      naturality {_m _n} f := by
        change 𝟙 _ ≫ (coefficientComplexCompletionProjection I c _n.unop).app K =
          (coefficientComplexCompletionProjection I c _m.unop).app K ≫
            ((coefficientComplexPowers I c).map f).app K
        rw [Category.id_comp]
        simpa only [NatTrans.comp_app,
          show (homOfLE (leOfHom f.unop)).op = f from Subsingleton.elim _ _] using
          (NatTrans.congr_app
            (coefficientComplexCompletionProjection_transition (D := D) I c
              (leOfHom f.unop)) K).symm }

/-- Evaluate any cone of quotient complexes at a degree, retaining its actual legs. -/
def coefficientComplexConeAt
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (s : Cone ((coefficientComplexReductionFunctor I c).obj K)) (i : ι) :
    Cone ((coefficientDiagramReductionFunctor I).obj (K.X i)) where
  pt := s.pt.X i
  π :=
    { app n := (s.π.app n).f i
      naturality {_m _n} f := by
        change 𝟙 _ ≫ (s.π.app _n).f i =
          (s.π.app _m).f i ≫ ((coefficientDiagramReductionFunctor I).obj (K.X i)).map f
        rw [Category.id_comp]
        exact (congrArg (fun a => a.f i) (s.w f)).symm }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degreewise completion lifts commute with the actual differentials. -/
def coefficientComplexCompletionLift
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (s : Cone ((coefficientComplexReductionFunctor I c).obj K)) :
    s.pt ⟶ (coefficientComplexCompletion I c).obj K where
  f i := coefficientDiagramCompletionLift I (K.X i) (coefficientComplexConeAt I c K s i)
  comm' i j _ := by
    apply (coefficientDiagramCompletionConeIsLimit I (K.X j)).hom_ext
    intro n
    change
      (coefficientDiagramCompletionLift I (K.X i) (coefficientComplexConeAt I c K s i) ≫
        (coefficientDiagramCompletion I).map (K.d i j)) ≫
          (coefficientDiagramCompletionProjection I n.unop).app (K.X j) =
      (s.pt.d i j ≫
        coefficientDiagramCompletionLift I (K.X j) (coefficientComplexConeAt I c K s j)) ≫
          (coefficientDiagramCompletionProjection I n.unop).app (K.X j)
    calc
      _ = (s.π.app n).f i ≫ ((coefficientDiagramPowers I).obj n).map (K.d i j) := by
        rw [Category.assoc, (coefficientDiagramCompletionProjection I n.unop).naturality,
          ← Category.assoc, coefficientDiagramCompletionLift_projection]
        rfl
      _ = s.pt.d i j ≫ (s.π.app n).f j := (s.π.app n).comm i j
      _ = _ := by
        rw [Category.assoc, coefficientDiagramCompletionLift_projection]
        rfl

@[reassoc (attr := simp)]
theorem coefficientComplexCompletionLift_projection
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (s : Cone ((coefficientComplexReductionFunctor I c).obj K)) (n : ℕ) :
    coefficientComplexCompletionLift I c K s ≫
        (coefficientComplexCompletionProjection I c n).app K = s.π.app (op n) := by
  apply HomologicalComplex.hom_ext
  intro i
  exact coefficientDiagramCompletionLift_projection I (K.X i)
    (coefficientComplexConeAt I c K s i) n

/-- Degreewise compatible-sequence completion is the limit of the quotient complexes. -/
def coefficientComplexCompletionConeIsLimit
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) :
    IsLimit (coefficientComplexCompletionCone I c K) where
  lift := coefficientComplexCompletionLift I c K
  fac s n := coefficientComplexCompletionLift_projection I c K s n.unop
  uniq s f hf := by
    apply HomologicalComplex.hom_ext
    intro i
    apply (coefficientDiagramCompletionConeIsLimit I (K.X i)).hom_ext
    intro n
    change f.f i ≫ (coefficientDiagramCompletionProjection I n.unop).app (K.X i) =
      coefficientDiagramCompletionLift I (K.X i) (coefficientComplexConeAt I c K s i) ≫
        (coefficientDiagramCompletionProjection I n.unop).app (K.X i)
    rw [coefficientDiagramCompletionLift_projection]
    exact congrArg (fun a => a.f i) (hf n)

end Langlands.Shimura.Coefficients
