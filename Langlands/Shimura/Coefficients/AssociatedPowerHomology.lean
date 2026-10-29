import Langlands.Shimura.Coefficients.AssociatedPowerComplexComparison
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Homology sheaf systems of actual associated power complexes -/

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
variable {ι : Type uι} (c : ComplexShape ι) (i : ι)

/-- Actual homology in the abelian category of small-etale sheaf diagrams. -/
abbrev etaleSheafDiagramHomologyFunctor :
    HomologicalComplex (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c ⥤
      (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  HomologicalComplex.homologyFunctor _ c i

/-- Homology sheaves of the actual associated complex, natural in coefficient complexes. -/
def etaleAssociatedHomologyFunctor :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  etaleAssociatedVaryingComplexFunctor X Y hY c ⋙
    etaleSheafDiagramHomologyFunctor X c i

/-- The full inverse system of homology sheaves of sheaf-power quotient complexes. -/
def etaleAssociatedSheafPowerHomologySystems :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      (ℕᵒᵖ ⥤ (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) :=
  etaleAssociatedSheafComplexPowerSystems I X Y hY c ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (etaleSheafDiagramHomologyFunctor X c i)

/-- The full inverse system of homology sheaves of associated coefficient-power complexes. -/
def etaleAssociatedPowerHomologySystems :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      (ℕᵒᵖ ⥤ (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) :=
  etaleAssociatedComplexPowerSystems I X Y hY c ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (etaleSheafDiagramHomologyFunctor X c i)

/-- Apply actual homology to the published comparison of quotient-complex systems. -/
def etaleAssociatedPowerHomologySystemsComparison :
    etaleAssociatedSheafPowerHomologySystems I X Y hY c i ⟶
      etaleAssociatedPowerHomologySystems I X Y hY c i :=
  Functor.whiskerRight (etaleAssociatedComplexReductionSystemsComparison I X Y hY c)
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (etaleSheafDiagramHomologyFunctor X c i))

@[simp]
theorem etaleAssociatedPowerHomologySystemsComparison_app
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕᵒᵖ) :
    ((etaleAssociatedPowerHomologySystemsComparison I X Y hY c i).app K).app n =
      HomologicalComplex.homologyMap
        (((etaleAssociatedComplexReductionSystemsComparison I X Y hY c).app K).app n)
        i := rfl

/-- The ordinary inverse limit of the sheaf-power homology diagrams. -/
def etaleAssociatedSheafPowerHomologyLimit :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  etaleAssociatedSheafPowerHomologySystems I X Y hY c i ⋙ lim

/-- The ordinary inverse limit of the associated coefficient-power homology diagrams. -/
def etaleAssociatedPowerHomologyLimit :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  etaleAssociatedPowerHomologySystems I X Y hY c i ⋙ lim

/-- Take the ordinary limit of the actual homology-system comparison. -/
def etaleAssociatedPowerHomologyLimitComparison :
    etaleAssociatedSheafPowerHomologyLimit I X Y hY c i ⟶
      etaleAssociatedPowerHomologyLimit I X Y hY c i :=
  Functor.whiskerRight (etaleAssociatedPowerHomologySystemsComparison I X Y hY c i) lim

@[reassoc (attr := simp)]
theorem etaleAssociatedPowerHomologyLimitComparison_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕᵒᵖ) :
    (etaleAssociatedPowerHomologyLimitComparison I X Y hY c i).app K ≫
        limit.π ((etaleAssociatedPowerHomologySystems I X Y hY c i).obj K) n =
      limit.π ((etaleAssociatedSheafPowerHomologySystems I X Y hY c i).obj K) n ≫
        ((etaleAssociatedPowerHomologySystemsComparison I X Y hY c i).app K).app n :=
  limMap_π _ _

/-- The canonical map from homology of the sheaf-power complex limit to the homology limit. -/
def etaleAssociatedSheafPowerLimitHomologyComparison :
    etaleAssociatedSheafComplexPowerLimit I X Y hY c ⋙
        etaleSheafDiagramHomologyFunctor X c i ⟶
      etaleAssociatedSheafPowerHomologyLimit I X Y hY c i where
  app K := limit.post ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K)
    (etaleSheafDiagramHomologyFunctor X c i)
  naturality {_K _L} f := limit.map_post
    ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).map f)
    (etaleSheafDiagramHomologyFunctor X c i)

/-- The canonical map from homology of the associated complex limit to the homology limit. -/
def etaleAssociatedPowerLimitHomologyComparison :
    etaleAssociatedComplexPowerLimit I X Y hY c ⋙
        etaleSheafDiagramHomologyFunctor X c i ⟶
      etaleAssociatedPowerHomologyLimit I X Y hY c i where
  app K := limit.post ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K)
    (etaleSheafDiagramHomologyFunctor X c i)
  naturality {_K _L} f := limit.map_post
    ((etaleAssociatedComplexPowerSystems I X Y hY c).map f)
    (etaleSheafDiagramHomologyFunctor X c i)

@[reassoc (attr := simp)]
theorem etaleAssociatedSheafPowerLimitHomologyComparison_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕᵒᵖ) :
    (etaleAssociatedSheafPowerLimitHomologyComparison I X Y hY c i).app K ≫
        limit.π ((etaleAssociatedSheafPowerHomologySystems I X Y hY c i).obj K) n =
      HomologicalComplex.homologyMap
        (limit.π ((etaleAssociatedSheafComplexPowerSystems I X Y hY c).obj K) n) i :=
  limit.post_π _ _ _

@[reassoc (attr := simp)]
theorem etaleAssociatedPowerLimitHomologyComparison_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕᵒᵖ) :
    (etaleAssociatedPowerLimitHomologyComparison I X Y hY c i).app K ≫
        limit.π ((etaleAssociatedPowerHomologySystems I X Y hY c i).obj K) n =
      HomologicalComplex.homologyMap
        (limit.π ((etaleAssociatedComplexPowerSystems I X Y hY c).obj K) n) i :=
  limit.post_π _ _ _

/-- Homology of the complex-limit comparison and the limit of homology comparisons agree. -/
theorem etaleAssociatedPowerLimitHomologyComparison_square :
    Functor.whiskerRight (etaleAssociatedComplexPowerLimitComparison I X Y hY c)
        (etaleSheafDiagramHomologyFunctor X c i) ≫
      etaleAssociatedPowerLimitHomologyComparison I X Y hY c i =
    etaleAssociatedSheafPowerLimitHomologyComparison I X Y hY c i ≫
      etaleAssociatedPowerHomologyLimitComparison I X Y hY c i := by
  apply NatTrans.ext
  funext K
  exact limit.map_post
    ((etaleAssociatedComplexReductionSystemsComparison I X Y hY c).app K)
    (etaleSheafDiagramHomologyFunctor X c i)

/-- Map the genuine sheaf quotient cone through the actual homology functor. -/
def etaleAssociatedSheafPowerHomologyCone
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) :
    Cone ((etaleAssociatedSheafPowerHomologySystems I X Y hY c i).obj K) :=
  (etaleSheafDiagramHomologyFunctor X c i).mapCone
    (sheafDiagramComplexPowerCone X.smallEtaleTopology I J c
      ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K))

/-- Map the genuine associated coefficient quotient cone through actual homology. -/
def etaleAssociatedPowerHomologyCone
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) :
    Cone ((etaleAssociatedPowerHomologySystems I X Y hY c i).obj K) :=
  (etaleSheafDiagramHomologyFunctor X c i).mapCone
    (etaleAssociatedComplexPowerCone I X Y hY c K)

/-- The natural homology unit induced by the genuine sheaf quotient maps. -/
def etaleAssociatedSheafPowerHomologyLimitUnit :
    etaleAssociatedHomologyFunctor X Y hY c i ⟶
      etaleAssociatedSheafPowerHomologyLimit I X Y hY c i :=
  Functor.whiskerRight (etaleAssociatedSheafComplexPowerLimitUnit I X Y hY c)
      (etaleSheafDiagramHomologyFunctor X c i) ≫
    etaleAssociatedSheafPowerLimitHomologyComparison I X Y hY c i

/-- The natural homology unit induced by the genuine coefficient quotient maps. -/
def etaleAssociatedPowerHomologyLimitUnit :
    etaleAssociatedHomologyFunctor X Y hY c i ⟶
      etaleAssociatedPowerHomologyLimit I X Y hY c i :=
  Functor.whiskerRight (etaleAssociatedComplexPowerLimitUnit I X Y hY c)
      (etaleSheafDiagramHomologyFunctor X c i) ≫
    etaleAssociatedPowerLimitHomologyComparison I X Y hY c i

/-- The sheaf homology unit is precisely the lift of the mapped genuine quotient cone. -/
theorem etaleAssociatedSheafPowerHomologyLimitUnit_eq_lift
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) :
    (etaleAssociatedSheafPowerHomologyLimitUnit I X Y hY c i).app K =
      limit.lift _ (etaleAssociatedSheafPowerHomologyCone I X Y hY c i K) :=
  limit.lift_post _ (etaleSheafDiagramHomologyFunctor X c i)
    (sheafDiagramComplexPowerCone X.smallEtaleTopology I J c
      ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K))

/-- The coefficient homology unit is precisely the lift of its mapped genuine quotient cone. -/
theorem etaleAssociatedPowerHomologyLimitUnit_eq_lift
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) :
    (etaleAssociatedPowerHomologyLimitUnit I X Y hY c i).app K =
      limit.lift _ (etaleAssociatedPowerHomologyCone I X Y hY c i K) :=
  limit.lift_post _ (etaleSheafDiagramHomologyFunctor X c i)
    (etaleAssociatedComplexPowerCone I X Y hY c K)

@[reassoc (attr := simp)]
theorem etaleAssociatedSheafPowerHomologyLimitUnit_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕ) :
    (etaleAssociatedSheafPowerHomologyLimitUnit I X Y hY c i).app K ≫
        limit.π ((etaleAssociatedSheafPowerHomologySystems I X Y hY c i).obj K) (op n) =
      HomologicalComplex.homologyMap
        ((sheafDiagramComplexPowerUnit X.smallEtaleTopology I J c n).app
          ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K)) i := by
  rw [etaleAssociatedSheafPowerHomologyLimitUnit_eq_lift, limit.lift_π]
  rfl

@[reassoc (attr := simp)]
theorem etaleAssociatedPowerHomologyLimitUnit_π
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕ) :
    (etaleAssociatedPowerHomologyLimitUnit I X Y hY c i).app K ≫
        limit.π ((etaleAssociatedPowerHomologySystems I X Y hY c i).obj K) (op n) =
      HomologicalComplex.homologyMap
        ((etaleAssociatedVaryingComplexFunctor X Y hY c).map
          ((coefficientComplexPowerUnit I c n).app K)) i := by
  rw [etaleAssociatedPowerHomologyLimitUnit_eq_lift, limit.lift_π]
  rfl

/-- The genuine quotient-chain-map factorization remains valid on actual homology. -/
theorem etaleAssociatedPowerHomologySystemsComparison_unit
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((sheafDiagramComplexPowerUnit X.smallEtaleTopology I J c n).app
          ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K)) i ≫
      ((etaleAssociatedPowerHomologySystemsComparison I X Y hY c i).app K).app (op n) =
    HomologicalComplex.homologyMap
      ((etaleAssociatedVaryingComplexFunctor X Y hY c).map
        ((coefficientComplexPowerUnit I c n).app K)) i := by
  change (etaleSheafDiagramHomologyFunctor X c i).map _ ≫
    (etaleSheafDiagramHomologyFunctor X c i).map _ =
      (etaleSheafDiagramHomologyFunctor X c i).map _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f => (etaleSheafDiagramHomologyFunctor X c i).map f)
    (etaleAssociatedComplexReductionSystemsComparison_unit I X Y hY c K n)

/-- The homology-limit comparison carries the genuine sheaf unit to the coefficient unit. -/
theorem etaleAssociatedPowerHomologyLimitComparison_unit :
    etaleAssociatedSheafPowerHomologyLimitUnit I X Y hY c i ≫
        etaleAssociatedPowerHomologyLimitComparison I X Y hY c i =
      etaleAssociatedPowerHomologyLimitUnit I X Y hY c i := by
  apply NatTrans.ext
  funext K
  apply limit.hom_ext
  intro n
  change ((etaleAssociatedSheafPowerHomologyLimitUnit I X Y hY c i).app K ≫
      (etaleAssociatedPowerHomologyLimitComparison I X Y hY c i).app K) ≫
        limit.π ((etaleAssociatedPowerHomologySystems I X Y hY c i).obj K) n =
    (etaleAssociatedPowerHomologyLimitUnit I X Y hY c i).app K ≫
      limit.π ((etaleAssociatedPowerHomologySystems I X Y hY c i).obj K) n
  rw [Category.assoc, etaleAssociatedPowerHomologyLimitComparison_π,
    etaleAssociatedSheafPowerHomologyLimitUnit_π_assoc,
    etaleAssociatedPowerHomologyLimitUnit_π]
  exact etaleAssociatedPowerHomologySystemsComparison_unit I X Y hY c i K n.unop

end Langlands.Shimura.Coefficients
