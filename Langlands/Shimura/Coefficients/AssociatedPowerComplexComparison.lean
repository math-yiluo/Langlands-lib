import Langlands.Shimura.Coefficients.AssociatedComplexCompletion
import Langlands.Shimura.Coefficients.SheafDiagramAdicComplex

/-! # Comparing sheaf-power and associated coefficient-power complexes -/

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

/-- Form the full sheaf-power system of the actual associated complex. -/
def etaleAssociatedSheafComplexPowerSystems :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      (ℕᵒᵖ ⥤ HomologicalComplex
        (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c) :=
  etaleAssociatedVaryingComplexFunctor X Y hY c ⋙
    sheafDiagramComplexReductionFunctor X.smallEtaleTopology I J c

/-- The original diagram comparison commutes with the actual differentials. -/
def etaleAssociatedComplexPowerComparison
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕᵒᵖ) :
    ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K).obj n ⟶
      ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K).obj n where
  f i := ((etaleAssociatedVaryingReductionSystemsComparison I X Y hY).app
    (K.X i)).app n
  comm' i k _ := by
    exact (NatTrans.congr_app
      ((etaleAssociatedVaryingReductionSystemsComparison I X Y hY).naturality
        (K.d i k)) n).symm

/-- The comparison is natural in powers and in coefficient chain maps. -/
def etaleAssociatedComplexReductionSystemsComparison :
    etaleAssociatedSheafComplexPowerSystems I X Y hY c ⟶
      etaleAssociatedComplexPowerSystems I X Y hY c where
  app K :=
    { app n := etaleAssociatedComplexPowerComparison I X Y hY c K n
      naturality {_m _n} a := by
        apply HomologicalComplex.hom_ext
        intro i
        exact ((etaleAssociatedVaryingReductionSystemsComparison I X Y hY).app
          (K.X i)).naturality a }
  naturality {K L} f := by
    apply NatTrans.ext
    funext n
    apply HomologicalComplex.hom_ext
    intro i
    exact NatTrans.congr_app
      ((etaleAssociatedVaryingReductionSystemsComparison I X Y hY).naturality
        (f.f i)) n

@[simp]
theorem etaleAssociatedComplexReductionSystemsComparison_app_f
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (n : ℕ) (i : ι) (j : J) :
    ((((etaleAssociatedComplexReductionSystemsComparison I X Y hY c).app K).app
        (op n)).f i).app j =
      (constantAssociatedPowerReductionComparison I X (Y.action j) n).app
        ((K.X i).action j) := rfl

/-- Sheaf quotients followed by comparison are association of coefficient quotients. -/
theorem etaleAssociatedComplexReductionSystemsComparison_unit
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕ) :
    (sheafDiagramComplexPowerUnit X.smallEtaleTopology I J c n).app
        ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K) ≫
      ((etaleAssociatedComplexReductionSystemsComparison I X Y hY c).app K).app
        (op n) =
      (etaleAssociatedVaryingComplexFunctor X Y hY c).map
        ((coefficientComplexPowerUnit I c n).app K) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply NatTrans.ext
  funext j
  change (𝟙 _ ≫ (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n).app
      ((etaleAssociatedVaryingSystem X Y hY (K.X i)).obj j)) ≫
        (constantAssociatedPowerReductionComparison I X (Y.action j) n).app
          ((K.X i).action j) =
    ((etaleAssociatedVaryingSystemFunctor X Y hY).map
      (𝟙 _ ≫ (coefficientDiagramPowerUnit I n).app (K.X i))).app j
  simp only [Category.id_comp]
  exact etaleAssociatedVaryingPowerUnit_app I X Y hY (K.X i) n j

/-- The ordinary inverse limit of the sheaf-power complexes of association. -/
def etaleAssociatedSheafComplexPowerLimit :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      HomologicalComplex (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c :=
  etaleAssociatedSheafComplexPowerSystems I X Y hY c ⋙ lim

/-- The genuine sheaf quotient cone induces its natural ordinary-limit unit. -/
def etaleAssociatedSheafComplexPowerLimitUnit :
    etaleAssociatedVaryingComplexFunctor X Y hY c ⟶
      etaleAssociatedSheafComplexPowerLimit I X Y hY c :=
  Functor.whiskerLeft (etaleAssociatedVaryingComplexFunctor X Y hY c)
    (sheafDiagramComplexPowerLimitUnit X.smallEtaleTopology I J c)

/-- Take the ordinary limit of the actual quotient-complex system comparison. -/
def etaleAssociatedComplexPowerLimitComparison :
    etaleAssociatedSheafComplexPowerLimit I X Y hY c ⟶
      etaleAssociatedComplexPowerLimit I X Y hY c :=
  Functor.whiskerRight
    (etaleAssociatedComplexReductionSystemsComparison I X Y hY c) lim

@[reassoc (attr := simp)]
theorem etaleAssociatedSheafComplexPowerLimitUnit_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕ) :
    (etaleAssociatedSheafComplexPowerLimitUnit I X Y hY c).app K ≫
        limit.π ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K) (op n) =
      (sheafDiagramComplexPowerUnit X.smallEtaleTopology I J c n).app
        ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K) :=
  sheafDiagramComplexPowerLimitUnit_π X.smallEtaleTopology I J c _ n

@[reassoc (attr := simp)]
theorem etaleAssociatedComplexPowerLimitComparison_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕ) :
    (etaleAssociatedComplexPowerLimitComparison I X Y hY c).app K ≫
        limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) (op n) =
      limit.π ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K) (op n) ≫
        ((etaleAssociatedComplexReductionSystemsComparison I X Y hY c).app K).app
          (op n) :=
  limMap_π _ _

/-- The two genuine quotient-limit units agree after the comparison. -/
theorem etaleAssociatedComplexPowerLimitComparison_unit :
    etaleAssociatedSheafComplexPowerLimitUnit I X Y hY c ≫
        etaleAssociatedComplexPowerLimitComparison I X Y hY c =
      etaleAssociatedComplexPowerLimitUnit I X Y hY c := by
  apply NatTrans.ext
  funext K
  apply limit.hom_ext
  intro n
  change ((etaleAssociatedSheafComplexPowerLimitUnit I X Y hY c).app K ≫
      (etaleAssociatedComplexPowerLimitComparison I X Y hY c).app K) ≫
        limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) n =
    (etaleAssociatedComplexPowerLimitUnit I X Y hY c).app K ≫
      limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) n
  rw [Category.assoc, etaleAssociatedComplexPowerLimitComparison_π,
    etaleAssociatedSheafComplexPowerLimitUnit_π_assoc,
    etaleAssociatedComplexPowerLimitUnit_π]
  exact etaleAssociatedComplexReductionSystemsComparison_unit I X Y hY c K n.unop

/-- The actual quotient-system projections characterize the comparison chain map. -/
theorem etaleAssociatedComplexPowerLimitComparison_unique
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (f : (etaleAssociatedSheafComplexPowerLimit I X Y hY c).obj K ⟶
      (etaleAssociatedComplexPowerLimit I X Y hY c).obj K)
    (hf : ∀ n : ℕ,
      f ≫ limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) (op n) =
        limit.π ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K) (op n) ≫
          ((etaleAssociatedComplexReductionSystemsComparison I X Y hY c).app K).app
            (op n)) :
    f = (etaleAssociatedComplexPowerLimitComparison I X Y hY c).app K := by
  apply limit.hom_ext
  intro n
  exact (hf n.unop).trans
    (etaleAssociatedComplexPowerLimitComparison_π I X Y hY c K n.unop).symm

/-- Degree evaluation recovers the published ordinary sheaf-power limit. -/
def etaleAssociatedSheafComplexPowerLimitDegreeIso
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (i : ι) :
    ((etaleAssociatedSheafComplexPowerLimit I X Y hY c).obj K).X i ≅
      (etaleAssociatedSheafPowerLimit I X Y hY).obj (K.X i) :=
  sheafDiagramComplexPowerLimitDegreeIso X.smallEtaleTopology I J c
    ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K) i

@[reassoc (attr := simp)]
theorem etaleAssociatedSheafComplexPowerLimitDegreeIso_hom_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (i : ι) (n : ℕ) :
    (etaleAssociatedSheafComplexPowerLimitDegreeIso I X Y hY c K i).hom ≫
        limit.π ((etaleAssociatedSheafPowerSystems I X Y hY).obj (K.X i)) (op n) =
      (limit.π ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K) (op n)).f i :=
  sheafDiagramComplexPowerLimitDegreeIso_hom_π X.smallEtaleTopology I J c
    ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K) i n

/-- In each degree the new map is the existing comparison of ordinary limits. -/
theorem etaleAssociatedComplexPowerLimitComparison_degree
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (i : ι) :
    ((etaleAssociatedComplexPowerLimitComparison I X Y hY c).app K).f i ≫
        (etaleAssociatedComplexPowerLimitDegreeIso I X Y hY c K i).hom =
      (etaleAssociatedSheafComplexPowerLimitDegreeIso I X Y hY c K i).hom ≫
        (etaleAssociatedPowerLimitComparison I X Y hY).app (K.X i) := by
  apply limit.hom_ext
  intro n
  rw [Category.assoc, etaleAssociatedComplexPowerLimitDegreeIso_hom_π,
    Category.assoc, etaleAssociatedPowerLimitComparison_π,
    ← Category.assoc, etaleAssociatedSheafComplexPowerLimitDegreeIso_hom_π]
  exact congrArg (fun a => a.f i)
    (etaleAssociatedComplexPowerLimitComparison_π I X Y hY c K n.unop)

end Langlands.Shimura.Coefficients
