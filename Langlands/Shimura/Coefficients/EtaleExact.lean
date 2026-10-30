import Langlands.Sheaf.SliceExact
import Langlands.Shimura.Coefficients.EtaleCoverComparisonProof
import Langlands.Shimura.Coefficients.AssociatedComplex
import Langlands.Cohomology.DivisibleSystem.InverseLimit
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.QuasiIso

/-! # Exact associated coefficient sheaves on finite geometric etale torsors -/
noncomputable section
universe u uι
namespace Langlands.Shimura.Coefficients
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {G : Type u} [Group G] (Y : Action X.Etale G)
variable (hY : IsFiniteGeometricTorsor X Y)

include hY

/-- Restriction to the genuine etale torsor detects isomorphisms. -/
theorem etaleTorsorPullbackReflectsIsomorphisms :
    (X.smallEtaleTopology.overPullback (ModuleCat.{u} R) Y.V).ReflectsIsomorphisms :=
  Langlands.Sheaf.overPullbackReflectsIsomorphisms _ _ _
    (etale_coversTop_of_surjective Y.V hY.2.2.1)

/-- Association on an actual finite geometric etale torsor preserves finite limits. -/
theorem etaleAssociatedFunctorPreservesFiniteLimits :
    PreservesFiniteLimits (etaleAssociatedFunctor (R := R) X Y) := by
  let L := X.smallEtaleTopology.overPullback (ModuleCat.{u} R) Y.V
  have : L.ReflectsIsomorphisms := etaleTorsorPullbackReflectsIsomorphisms X Y hY
  have : PreservesFiniteLimits (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)) := by
    unfold constantSheaf
    infer_instance
  have : PreservesFiniteLimits (etaleAssociatedFunctor (R := R) X Y ⋙ L) :=
    preservesFiniteLimits_of_natIso
      (constantAssociatedTrivializationOfSplitting X.smallEtaleTopology Y
        (etaleTorsorSectionSplitting X G Y hY R)).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ L

/-- Association on an actual finite geometric etale torsor preserves finite colimits. -/
theorem etaleAssociatedFunctorPreservesFiniteColimits :
    PreservesFiniteColimits (etaleAssociatedFunctor (R := R) X Y) := by
  let L := X.smallEtaleTopology.overPullback (ModuleCat.{u} R) Y.V
  have : L.ReflectsIsomorphisms := etaleTorsorPullbackReflectsIsomorphisms X Y hY
  have : PreservesColimitsOfSize.{0,0}
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
    (constantSheafAdj _ _ (etaleIdIsTerminal X)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (etaleAssociatedFunctor (R := R) X Y ⋙ L) :=
    preservesFiniteColimits_of_natIso
      (constantAssociatedTrivializationOfSplitting X.smallEtaleTopology Y
        (etaleTorsorSectionSplitting X G Y hY R)).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ L

/-- Exact association preserves the genuine kernel/cokernel construction of homology. -/
theorem etaleAssociatedFunctorPreservesHomology :
    (etaleAssociatedFunctor (R := R) X Y).PreservesHomology := by
  have := etaleAssociatedFunctorPreservesFiniteLimits (R := R) X Y hY
  have := etaleAssociatedFunctorPreservesFiniteColimits (R := R) X Y hY
  infer_instance

variable {ι : Type uι} (c : ComplexShape ι)

/-- The homology of the actual associated complex is naturally the sheaf associated
to the coefficient homology representation. -/
def etaleAssociatedHomologyIso (q : ι) :
    etaleAssociatedComplexFunctor (R := R) X Y c ⋙
        HomologicalComplex.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c q ≅
      HomologicalComplex.homologyFunctor (Action (ModuleCat.{u} R) G) c q ⋙
        etaleAssociatedFunctor X Y := by
  have := etaleAssociatedFunctorPreservesHomology (R := R) X Y hY
  exact Langlands.Cohomology.mapHomologicalComplexHomologyIso
    (etaleAssociatedFunctor X Y) c q

/-- The canonical homology comparison intertwines the genuine induced maps. -/
@[reassoc]
theorem etaleAssociatedHomologyIso_naturality
    {K L : HomologicalComplex (Action (ModuleCat.{u} R) G) c}
    (f : K ⟶ L) (q : ι) :
    HomologicalComplex.homologyMap
        ((etaleAssociatedComplexFunctor X Y c).map f) q ≫
        (etaleAssociatedHomologyIso X Y hY c q).hom.app L =
      (etaleAssociatedHomologyIso X Y hY c q).hom.app K ≫
        (etaleAssociatedFunctor X Y).map (HomologicalComplex.homologyMap f q) :=
  (etaleAssociatedHomologyIso X Y hY c q).hom.naturality f

/-- Exact association sends coefficient quasi-isomorphisms to sheaf
quasi-isomorphisms for every complex shape. -/
theorem etaleAssociatedComplexFunctor_preserves_quasiIso
    {K L : HomologicalComplex (Action (ModuleCat.{u} R) G) c}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((etaleAssociatedComplexFunctor (R := R) X Y c).map f) := by
  have := etaleAssociatedFunctorPreservesHomology (R := R) X Y hY
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f
    (etaleAssociatedFunctor X Y)

end Langlands.Shimura.Coefficients
