import Langlands.CategoryTheory.EquivariantDiagramAbelian
import Langlands.Shimura.Coefficients.EtaleExact
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Exact varying-cover association and canonical diagram homology -/

noncomputable section

universe u uJ vJ uι

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {J : Type uJ} [Category.{vJ} J] {D : J ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j))

include hY

/-- Association at each cover preserves finite limits of coefficient diagrams. -/
theorem etaleAssociatedAtPreservesFiniteLimits (j : J) :
    PreservesFiniteLimits (etaleAssociatedAt (R := R) X Y j) := by
  have := etaleAssociatedFunctorPreservesFiniteLimits (R := R) X (Y.action j) (hY j)
  unfold etaleAssociatedAt
  infer_instance

/-- Association at each cover preserves finite colimits of coefficient diagrams. -/
theorem etaleAssociatedAtPreservesFiniteColimits (j : J) :
    PreservesFiniteColimits (etaleAssociatedAt (R := R) X Y j) := by
  have := etaleAssociatedFunctorPreservesFiniteColimits (R := R) X (Y.action j) (hY j)
  unfold etaleAssociatedAt
  infer_instance

/-- Evaluation identifies the whole association functor with association at that cover. -/
def etaleAssociatedVaryingEvaluationIso (j : J) :
    etaleAssociatedVaryingSystemFunctor (R := R) X Y hY ⋙
        (evaluation J (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).obj j ≅
      etaleAssociatedAt X Y j :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    exact Category.comp_id _ |>.trans (Category.id_comp _).symm)

/-- The constructed associated-sheaf diagram functor preserves finite limits. -/
theorem etaleAssociatedVaryingSystemFunctorPreservesFiniteLimits :
    PreservesFiniteLimits (etaleAssociatedVaryingSystemFunctor (R := R) X Y hY) := by
  apply preservesFiniteLimits_of_evaluation
  intro j
  have := etaleAssociatedAtPreservesFiniteLimits (R := R) X Y hY j
  exact preservesFiniteLimits_of_natIso (etaleAssociatedVaryingEvaluationIso X Y hY j).symm

/-- The constructed associated-sheaf diagram functor preserves finite colimits. -/
theorem etaleAssociatedVaryingSystemFunctorPreservesFiniteColimits :
    PreservesFiniteColimits (etaleAssociatedVaryingSystemFunctor (R := R) X Y hY) := by
  apply preservesFiniteColimits_of_evaluation
  intro j
  have := etaleAssociatedAtPreservesFiniteColimits (R := R) X Y hY j
  exact preservesFiniteColimits_of_natIso (etaleAssociatedVaryingEvaluationIso X Y hY j).symm

/-- Exact varying-cover association preserves the actual construction of homology. -/
theorem etaleAssociatedVaryingSystemFunctorPreservesHomology :
    (etaleAssociatedVaryingSystemFunctor (R := R) X Y hY).PreservesHomology := by
  have := etaleAssociatedVaryingSystemFunctorPreservesFiniteLimits (R := R) X Y hY
  have := etaleAssociatedVaryingSystemFunctorPreservesFiniteColimits (R := R) X Y hY
  infer_instance

variable {ι : Type uι} (c : ComplexShape ι)

/-- Homology of the associated diagram complex is the diagram associated to
the coefficient homology, naturally in the coefficient complex. -/
def etaleAssociatedVaryingHomologyIso (q : ι) :
    etaleAssociatedVaryingComplexFunctor (R := R) X Y hY c ⋙
        HomologicalComplex.homologyFunctor
          (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c q ≅
      HomologicalComplex.homologyFunctor
          (EquivariantDiagram D (ModuleCat.{u} R)) c q ⋙
        etaleAssociatedVaryingSystemFunctor X Y hY := by
  have := etaleAssociatedVaryingSystemFunctorPreservesHomology (R := R) X Y hY
  exact Langlands.Cohomology.mapHomologicalComplexHomologyIso
    (etaleAssociatedVaryingSystemFunctor X Y hY) c q

/-- The canonical homology isomorphism intertwines induced coefficient chain maps. -/
@[reassoc]
theorem etaleAssociatedVaryingHomologyIso_naturality
    {K L : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c}
    (f : K ⟶ L) (q : ι) :
    HomologicalComplex.homologyMap
        ((etaleAssociatedVaryingComplexFunctor X Y hY c).map f) q ≫
        (etaleAssociatedVaryingHomologyIso X Y hY c q).hom.app L =
      (etaleAssociatedVaryingHomologyIso X Y hY c q).hom.app K ≫
        (etaleAssociatedVaryingSystemFunctor X Y hY).map
          (HomologicalComplex.homologyMap f q) :=
  (etaleAssociatedVaryingHomologyIso X Y hY c q).hom.naturality f

/-- The same homology comparison commutes with every varying-cover transition. -/
@[reassoc]
theorem etaleAssociatedVaryingHomologyIso_transition
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (q : ι) {i j : J} (a : i ⟶ j) :
    (((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K).homology q).map a ≫
        ((etaleAssociatedVaryingHomologyIso X Y hY c q).hom.app K).app j =
      ((etaleAssociatedVaryingHomologyIso X Y hY c q).hom.app K).app i ≫
        (etaleAssociatedTransition X Y hY a).app (K.homology q) :=
  ((etaleAssociatedVaryingHomologyIso X Y hY c q).hom.app K).naturality a

/-- Exact varying-cover association preserves coefficient quasi-isomorphisms. -/
theorem etaleAssociatedVaryingComplexFunctor_preserves_quasiIso
    {K L : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((etaleAssociatedVaryingComplexFunctor (R := R) X Y hY c).map f) := by
  have := etaleAssociatedVaryingSystemFunctorPreservesHomology (R := R) X Y hY
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f
    (etaleAssociatedVaryingSystemFunctor X Y hY)

end Langlands.Shimura.Coefficients
