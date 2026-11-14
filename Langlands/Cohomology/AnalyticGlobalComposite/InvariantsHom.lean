import Langlands.Cohomology.AnalyticGlobalComposite.Statement
import Langlands.Cohomology.LeftExactHomology
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Smooth invariants as maps from the trivial representation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace Langlands.Cohomology.AnalyticGlobalComposite

universe uR uG

variable (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]

local instance : (smoothTrivialFunctor.{uR, uG, uR} R G).Additive :=
  (smoothTrivialAdjunction R G).left_adjoint_additive

/-- Evaluation at one identifies maps from the trivial smooth representation with invariants. -/
def trivialHomInvariantsAddEquiv (M : SmoothRep.{uR, uG, uR} R G) :
    (trivialSmoothRep R G ⟶ M) ≃+ (smoothInvariantsFunctor R G).obj M :=
  ((smoothTrivialAdjunction R G).homAddEquiv (ModuleCat.of R R) M).trans
    ((ModuleCat.homAddEquiv).trans (LinearMap.ringLmapEquivSelf R ℕ _).toAddEquiv)

/-- The invariant group is naturally the group of maps from the trivial representation. -/
def invariantsHomIso :
    smoothInvariantsFunctor R G ⋙ forget₂ (ModuleCat.{uR} R) AddCommGrpCat ≅
      preadditiveCoyoneda.obj (op (trivialSmoothRep R G)) :=
  (NatIso.ofComponents
    (fun M => (trivialHomInvariantsAddEquiv R G M).toAddCommGrpIso)
    (fun f => by ext a; rfl)).symm

/-- Invariant-complex homology, with scalars forgotten, is Hom-complex homology. -/
def invariantsHomologyIso {ι : Type*} (c : ComplexShape ι) (i : ι) :
    ((smoothInvariantsFunctor R G).mapHomologicalComplex c ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{uR} R) c i) ⋙
        forget₂ (ModuleCat.{uR} R) AddCommGrpCat ≅
    (preadditiveCoyoneda.obj (op (trivialSmoothRep R G))).mapHomologicalComplex c ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat c i :=
  Functor.isoWhiskerLeft ((smoothInvariantsFunctor R G).mapHomologicalComplex c)
    (asIso (LeftExactHomology.homologyNatTrans
      (forget₂ (ModuleCat.{uR} R) AddCommGrpCat) c i)).symm ≪≫
  Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso (invariantsHomIso R G) c)
    (HomologicalComplex.homologyFunctor AddCommGrpCat c i)

end Langlands.Cohomology.AnalyticGlobalComposite
