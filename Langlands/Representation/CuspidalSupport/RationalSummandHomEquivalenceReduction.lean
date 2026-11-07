import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement
import Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceStatement
import Langlands.Representation.Category.ConstituentSerre
import Langlands.CategoryTheory.Renard.SmallProgeneratorEquivalence

/-! Renard VI.4.1: the Theorem follows from the Proposition through A.VIII.2
on the inherited abelian structure of the actual inertia block. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Block

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalSummandHomEquivalenceTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- The Serre-class structure of the actual inertia block, as in the published
`rationalInertiaBlockProperty_isSerreClass`. It is restated under a
module-specific name because `RationalInertiaPresentations` cannot be imported
together with the statement module: both declare the same automatically named
local topology instance. -/
local instance rationalSummandHomEquivalenceSerreClass
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G)) :
    (rationalInertiaBlockProperty G π).IsSerreClass :=
  SmoothRep.irreducibleSubquotientsProperty_isSerreClass (IsRationalInertiaRelated G π)

/-- Closure of the actual inertia block under finite products, as in the
published `rationalInertiaBlockProperty_isClosedUnderFiniteProducts`. -/
local instance rationalSummandHomEquivalenceFiniteProducts
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G)) :
    (rationalInertiaBlockProperty G π).IsClosedUnderFiniteProducts :=
  SmoothRep.irreducibleSubquotientsProperty_isClosedUnderFiniteProducts
    (IsRationalInertiaRelated G π)

/-- The inherited abelian structure of the actual inertia block has the
full-subcategory additive structure, as in `rationalInertiaBlock_abelian`. -/
theorem rationalSummandBlock_abelian
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G)) :
    ∃ a : Abelian (RationalInertiaBlock G π),
      a.toPreadditive = Preadditive.fullSubcategory (rationalInertiaBlockProperty G π) :=
  ⟨inferInstance, rfl⟩

/-- The block-lifting condition of the small-progenerator predicate is
Mathlib projectivity in the actual inertia block. -/
theorem projective_of_isRationalInertiaSmallProgenerator
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    {X : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G)}
    (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π) X)
    (hlift : ∀ (Y Z : RationalInertiaBlock G (rationalInertiaBaseLift G π)) (q : Y ⟶ Z),
      Epi q → ∀ f : (⟨X, hmem⟩ : RationalInertiaBlock G (rationalInertiaBaseLift G π)) ⟶ Z,
        ∃ g : (⟨X, hmem⟩ : RationalInertiaBlock G (rationalInertiaBaseLift G π)) ⟶ Y,
          g ≫ q = f) :
    Projective (⟨X, hmem⟩ : RationalInertiaBlock G (rationalInertiaBaseLift G π)) :=
  ⟨fun {E Y} f e he => hlift E Y e he f⟩

/-- The small-progenerator predicate gives membership and Renard's A.VIII.2
small progenerator in the inherited abelian structure, at coproduct size
`max uF uV`. -/
theorem homSmallProgenerator_of_isRationalInertiaSmallProgenerator
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (X : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
    (hX : IsRationalInertiaSmallProgenerator G π X) :
    ∃ (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π) X)
      (hcop : HasCoproducts.{max uF uV} (RationalInertiaBlock G (rationalInertiaBaseLift G π))),
      letI := hcop
      Langlands.Renard.HomSmallProgenerator.{max uF uV}
        (⟨X, hmem⟩ : RationalInertiaBlock G (rationalInertiaBaseLift G π)) := by
  obtain ⟨hmem, hlift, hfaith, hcop, hpres⟩ := hX
  let hcop' : HasCoproducts.{max uF uV}
      (RationalInertiaBlock G (rationalInertiaBaseLift G π)) := fun I => hcop I
  refine ⟨hmem, hcop', ?_⟩
  have hproj := projective_of_isRationalInertiaSmallProgenerator G π hmem hlift
  exact ⟨⟨(Langlands.Renard.homProjectiveComparison _).mpr hproj, hpres⟩, hfaith⟩

/-- Renard VI.4.1, Theorem, objectwise: for any object satisfying the
small-progenerator predicate, `Hom(P, •)` is an equivalence from the actual
inertia block to unital right `End P`-modules. -/
theorem isEquivalence_preadditiveCoyonedaObj_of_isRationalInertiaSmallProgenerator
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (X : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
    (hX : IsRationalInertiaSmallProgenerator G π X) :
    ∃ hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π) X,
      (preadditiveCoyonedaObj
        (⟨X, hmem⟩ : RationalInertiaBlock G (rationalInertiaBaseLift G π))).IsEquivalence := by
  obtain ⟨hmem, hcop, hP⟩ := homSmallProgenerator_of_isRationalInertiaSmallProgenerator G π X hX
  let := hcop
  exact ⟨hmem, Langlands.Renard.preadditiveCoyonedaObj_isEquivalence_of_homSmallProgenerator hP⟩

end Block

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- The Proposition of Renard VI.4.1 implies its Theorem, with the same
quantifiers, premises and universes. -/
theorem rationalSummandHomEquivalence_of_smallProgenerator
    (hProp : RationalSummandSmallProgeneratorStatement.{uF, uV}) :
    RationalSummandHomEquivalenceStatement.{uF, uV} := by
  intro F _ _ _ _ G hG T i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  exact isEquivalence_preadditiveCoyonedaObj_of_isRationalInertiaSmallProgenerator G π _
    (hProp F G hG T i hi ν hν hStandard hRoots hU π hπ hcusp ρ hρ j hj)

end Langlands.CuspidalSupport
