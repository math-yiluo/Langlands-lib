import Langlands.Shimura.Coefficients.AssociatedComplex
import Langlands.Shimura.Coefficients.DiagramAdicComplex
import Langlands.Shimura.Coefficients.VaryingCoverCompletion
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Ordinary completion comparison for associated coefficient complexes -/

noncomputable section

universe u uJ vJ uι

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {J : Type uJ} [Category.{vJ} J] {D : J ⥤ GrpCat.{u}}
variable (X : Scheme.{u}) (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j))
variable {ι : Type uι} (c : ComplexShape ι)

/-- Associate the full inverse system of actual coefficient quotient complexes. -/
def etaleAssociatedComplexPowerSystems :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      (ℕᵒᵖ ⥤ HomologicalComplex
        (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c) :=
  coefficientComplexReductionFunctor I c ⋙
    (Functor.whiskeringRight ℕᵒᵖ
      (HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
      (HomologicalComplex (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c)).obj
        (etaleAssociatedVaryingComplexFunctor X Y hY c)

/-- The ordinary inverse limit of the associated coefficient quotient complexes. -/
def etaleAssociatedComplexPowerLimit :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      HomologicalComplex (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c :=
  etaleAssociatedComplexPowerSystems I X Y hY c ⋙ lim

/-- Form associated complexes after actual degreewise coefficient completion. -/
def etaleAssociatedCompletedComplexFunctor :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      HomologicalComplex (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c :=
  coefficientComplexCompletion I c ⋙ etaleAssociatedVaryingComplexFunctor X Y hY c

/-- Map the actual completion cone through the associated-complex functor. -/
def etaleAssociatedComplexCompletionCone
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) :
    Cone ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) :=
  (etaleAssociatedVaryingComplexFunctor X Y hY c).mapCone
    (coefficientComplexCompletionCone I c K)

@[simp]
theorem etaleAssociatedComplexCompletionCone_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕ) :
    (etaleAssociatedComplexCompletionCone I X Y hY c K).π.app (op n) =
      (etaleAssociatedVaryingComplexFunctor X Y hY c).map
        ((coefficientComplexCompletionProjection I c n).app K) := rfl

/-- The canonical chain map from associated completion to the quotient-complex limit. -/
def etaleAssociatedComplexCompletionComparison :
    etaleAssociatedCompletedComplexFunctor I X Y hY c ⟶
      etaleAssociatedComplexPowerLimit I X Y hY c where
  app K := limit.lift _ (etaleAssociatedComplexCompletionCone I X Y hY c K)
  naturality {K L} f := by
    change (etaleAssociatedVaryingComplexFunctor X Y hY c).map
        ((coefficientComplexCompletion I c).map f) ≫
          limit.lift _ (etaleAssociatedComplexCompletionCone I X Y hY c L) =
      limit.lift _ (etaleAssociatedComplexCompletionCone I X Y hY c K) ≫
        limMap ((etaleAssociatedComplexPowerSystems I X Y hY c).map f)
    apply limit.hom_ext
    intro n
    rw [Category.assoc, limit.lift_π, Category.assoc, limMap_π,
      ← Category.assoc, limit.lift_π]
    change (etaleAssociatedVaryingComplexFunctor X Y hY c).map
        ((coefficientComplexCompletion I c).map f) ≫
          (etaleAssociatedVaryingComplexFunctor X Y hY c).map
            ((coefficientComplexCompletionProjection I c n.unop).app L) =
      (etaleAssociatedVaryingComplexFunctor X Y hY c).map
          ((coefficientComplexCompletionProjection I c n.unop).app K) ≫
        (etaleAssociatedVaryingComplexFunctor X Y hY c).map
          (((coefficientComplexPowers I c).obj n).map f)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (fun a => (etaleAssociatedVaryingComplexFunctor X Y hY c).map a)
      ((coefficientComplexCompletionProjection I c n.unop).naturality f)

/-- Every projection is association of the genuine completion evaluation chain map. -/
@[reassoc (attr := simp)]
theorem etaleAssociatedComplexCompletionComparison_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕ) :
    (etaleAssociatedComplexCompletionComparison I X Y hY c).app K ≫
        limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) (op n) =
      (etaleAssociatedVaryingComplexFunctor X Y hY c).map
        ((coefficientComplexCompletionProjection I c n).app K) :=
  limit.lift_π _ _

/-- The genuine coefficient quotient chain maps form an associated-complex cone. -/
def etaleAssociatedComplexPowerCone
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) :
    Cone ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) where
  pt := (etaleAssociatedVaryingComplexFunctor X Y hY c).obj K
  π :=
    { app n := (etaleAssociatedVaryingComplexFunctor X Y hY c).map
        ((coefficientComplexPowerUnit I c n.unop).app K)
      naturality {_m _n} f := by
        change 𝟙 _ ≫ (etaleAssociatedVaryingComplexFunctor X Y hY c).map
            ((coefficientComplexPowerUnit I c _n.unop).app K) =
          (etaleAssociatedVaryingComplexFunctor X Y hY c).map
              ((coefficientComplexPowerUnit I c _m.unop).app K) ≫
            (etaleAssociatedVaryingComplexFunctor X Y hY c).map
              (((coefficientComplexPowers I c).map f).app K)
        rw [Category.id_comp, ← CategoryTheory.Functor.map_comp]
        apply congrArg (fun a => (etaleAssociatedVaryingComplexFunctor X Y hY c).map a)
        simpa only [NatTrans.comp_app,
          show (homOfLE (leOfHom f.unop)).op = f from Subsingleton.elim _ _] using
          (NatTrans.congr_app
            (coefficientComplexPowerUnit_transition (D := D) I c
              (leOfHom f.unop)) K).symm }

/-- The canonical map from an associated complex to its coefficient-power limit. -/
def etaleAssociatedComplexPowerLimitUnit :
    etaleAssociatedVaryingComplexFunctor X Y hY c ⟶
      etaleAssociatedComplexPowerLimit I X Y hY c where
  app K := limit.lift _ (etaleAssociatedComplexPowerCone I X Y hY c K)
  naturality {K L} f := by
    change (etaleAssociatedVaryingComplexFunctor X Y hY c).map f ≫
        limit.lift _ (etaleAssociatedComplexPowerCone I X Y hY c L) =
      limit.lift _ (etaleAssociatedComplexPowerCone I X Y hY c K) ≫
        limMap ((etaleAssociatedComplexPowerSystems I X Y hY c).map f)
    apply limit.hom_ext
    intro n
    rw [Category.assoc, limit.lift_π, Category.assoc, limMap_π,
      ← Category.assoc, limit.lift_π]
    change (etaleAssociatedVaryingComplexFunctor X Y hY c).map f ≫
        (etaleAssociatedVaryingComplexFunctor X Y hY c).map
          ((coefficientComplexPowerUnit I c n.unop).app L) =
      (etaleAssociatedVaryingComplexFunctor X Y hY c).map
          ((coefficientComplexPowerUnit I c n.unop).app K) ≫
        (etaleAssociatedVaryingComplexFunctor X Y hY c).map
          (((coefficientComplexPowers I c).obj n).map f)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (fun a => (etaleAssociatedVaryingComplexFunctor X Y hY c).map a)
      ((coefficientComplexPowerUnit I c n.unop).naturality f)

@[reassoc (attr := simp)]
theorem etaleAssociatedComplexPowerLimitUnit_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕ) :
    (etaleAssociatedComplexPowerLimitUnit I X Y hY c).app K ≫
        limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) (op n) =
      (etaleAssociatedVaryingComplexFunctor X Y hY c).map
        ((coefficientComplexPowerUnit I c n).app K) :=
  limit.lift_π _ _

/-- The original quotient-limit unit factors through the actual completed complex. -/
theorem etaleAssociatedComplexCompletionComparison_unit :
    Functor.whiskerRight (coefficientComplexCompletionUnit I c)
        (etaleAssociatedVaryingComplexFunctor X Y hY c) ≫
      etaleAssociatedComplexCompletionComparison I X Y hY c =
        etaleAssociatedComplexPowerLimitUnit I X Y hY c := by
  apply NatTrans.ext
  funext K
  apply limit.hom_ext
  intro n
  change ((etaleAssociatedVaryingComplexFunctor X Y hY c).map
      ((coefficientComplexCompletionUnit I c).app K) ≫
        (etaleAssociatedComplexCompletionComparison I X Y hY c).app K) ≫
          limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) n =
    (etaleAssociatedComplexPowerLimitUnit I X Y hY c).app K ≫
      limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) n
  rw [Category.assoc, etaleAssociatedComplexCompletionComparison_π,
    etaleAssociatedComplexPowerLimitUnit_π, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun a => (etaleAssociatedVaryingComplexFunctor X Y hY c).map a)
    (NatTrans.congr_app (coefficientComplexCompletionUnit_projection (D := D) I c n.unop) K)

/-- Quotient projections characterize the completion comparison among actual chain maps. -/
theorem etaleAssociatedComplexCompletionComparison_unique
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (f : (etaleAssociatedCompletedComplexFunctor I X Y hY c).obj K ⟶
      (etaleAssociatedComplexPowerLimit I X Y hY c).obj K)
    (hf : ∀ n : ℕ,
      f ≫ limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) (op n) =
        (etaleAssociatedVaryingComplexFunctor X Y hY c).map
          ((coefficientComplexCompletionProjection I c n).app K)) :
    f = (etaleAssociatedComplexCompletionComparison I X Y hY c).app K := by
  apply limit.hom_ext
  intro n
  exact (hf n.unop).trans
    (etaleAssociatedComplexCompletionComparison_π I X Y hY c K n.unop).symm

@[simp]
theorem etaleAssociatedComplexPowerSystems_obj_X
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (n : ℕᵒᵖ) (i : ι) :
    (((etaleAssociatedComplexPowerSystems I X Y hY c).obj K).obj n).X i =
      (etaleAssociatedVaryingSystemFunctor X Y hY).obj
        (((coefficientDiagramPowers I).obj n).obj (K.X i)) := rfl

@[simp]
theorem etaleAssociatedComplexPowerSystems_obj_d
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (n : ℕᵒᵖ) (i j : ι) :
    (((etaleAssociatedComplexPowerSystems I X Y hY c).obj K).obj n).d i j =
      (etaleAssociatedVaryingSystemFunctor X Y hY).map
        (((coefficientDiagramPowers I).obj n).map (K.d i j)) := rfl

@[simp]
theorem etaleAssociatedComplexPowerSystems_transition_f
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    {m n : ℕᵒᵖ} (a : m ⟶ n) (i : ι) :
    (((etaleAssociatedComplexPowerSystems I X Y hY c).obj K).map a).f i =
      (etaleAssociatedVaryingSystemFunctor X Y hY).map
        (((coefficientDiagramPowers I).map a).app (K.X i)) := rfl

@[simp]
theorem etaleAssociatedComplexPowerSystems_map_app_f
    {K L : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c}
    (f : K ⟶ L) (n : ℕᵒᵖ) (i : ι) :
    (((etaleAssociatedComplexPowerSystems I X Y hY c).map f).app n).f i =
      (etaleAssociatedVaryingSystemFunctor X Y hY).map
        (((coefficientDiagramPowers I).obj n).map (f.f i)) := rfl

/-- Each degree of the complex limit is the ordinary associated coefficient-power limit. -/
def etaleAssociatedComplexPowerLimitDegreeIso
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (i : ι) :
    ((etaleAssociatedComplexPowerLimit I X Y hY c).obj K).X i ≅
      (etaleAssociatedCoefficientPowerLimit I X Y hY).obj (K.X i) :=
  preservesLimitIso (HomologicalComplex.eval _ c i)
    ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K)

@[reassoc (attr := simp)]
theorem etaleAssociatedComplexPowerLimitDegreeIso_hom_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (i : ι) (n : ℕ) :
    (etaleAssociatedComplexPowerLimitDegreeIso I X Y hY c K i).hom ≫
        limit.π ((etaleAssociatedCoefficientPowerSystems I X Y hY).obj (K.X i)) (op n) =
      (limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) (op n)).f i :=
  preservesLimitIso_hom_π _ _ _

/-- Degree evaluation of the new comparison is the published ordinary comparison. -/
theorem etaleAssociatedComplexCompletionComparison_degree
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (i : ι) :
    ((etaleAssociatedComplexCompletionComparison I X Y hY c).app K).f i ≫
        (etaleAssociatedComplexPowerLimitDegreeIso I X Y hY c K i).hom =
      (etaleAssociatedCompletionComparison I X Y hY).app (K.X i) := by
  apply limit.hom_ext
  intro n
  rw [Category.assoc, etaleAssociatedComplexPowerLimitDegreeIso_hom_π,
    etaleAssociatedCompletionComparison_π]
  exact congrArg (fun a => a.f i)
    (etaleAssociatedComplexCompletionComparison_π I X Y hY c K n.unop)

end Langlands.Shimura.Coefficients
