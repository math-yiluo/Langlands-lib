import Langlands.Cohomology.LeftExactHomology
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.RepresentationTheory.Invariants
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Invariants as additive maps from the trivial representation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace Langlands.Cohomology.EquivariantComposite

universe u

variable (R G : Type u) [CommRing R] [Group G]

local instance : (Rep.trivialFunctor R G).Additive :=
  (Rep.invariantsAdjunction R G).left_adjoint_additive

/-- Evaluate an equivariant map from the trivial representation at one. -/
def trivialHomInvariantsAddEquiv (M : Rep.{u} R G) :
    (Rep.trivial R G R ⟶ M) ≃+ (Rep.invariantsFunctor R G).obj M :=
  ((Rep.invariantsAdjunction R G).homAddEquiv (ModuleCat.of R R) M).trans
    ((ModuleCat.homAddEquiv).trans (LinearMap.ringLmapEquivSelf R ℕ _).toAddEquiv)

/-- Invariant vectors are naturally additive maps from the trivial representation. -/
def invariantsHomIso :
    Rep.invariantsFunctor R G ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat ≅
      preadditiveCoyoneda.obj (op (Rep.trivial R G R)) :=
  (NatIso.ofComponents
    (fun M => (trivialHomInvariantsAddEquiv R G M).toAddCommGrpIso)
    (fun f => by ext a; rfl)).symm

/-- Forgetting scalar multiplication in invariant homology gives Hom-complex homology. -/
def invariantsHomologyIso {ι : Type*} (c : ComplexShape ι) (i : ι) :
    ((Rep.invariantsFunctor R G).mapHomologicalComplex c ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c i) ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat ≅
    (preadditiveCoyoneda.obj (op (Rep.trivial R G R))).mapHomologicalComplex c ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat c i :=
  Functor.isoWhiskerLeft ((Rep.invariantsFunctor R G).mapHomologicalComplex c)
    (asIso (LeftExactHomology.homologyNatTrans
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat) c i)).symm ≪≫
  Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso (invariantsHomIso R G) c)
    (HomologicalComplex.homologyFunctor AddCommGrpCat c i)

end Langlands.Cohomology.EquivariantComposite
