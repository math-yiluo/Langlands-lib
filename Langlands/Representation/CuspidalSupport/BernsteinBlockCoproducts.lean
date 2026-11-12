import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.CuspidalSupport.RationalInertiaCoproducts
import Langlands.Representation.Category.ConstituentSerre
import Langlands.Representation.Category.FiniteGenerationCoproducts
import Langlands.CategoryTheory.Renard.SmallProgeneratorEquivalence
import Langlands.CategoryTheory.Renard.HomGeneratorCriteria

/-! # Abelian structure, coproducts and smallness in a Bernstein block

These constructions use the published all-irreducible-subquotients block.
They require no Bernstein decomposition or uniqueness of cuspidal support.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinBlockCoproductsAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance bernsteinBlockCoproductsTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)
  (s : BernsteinInertialClass.{uF, max uF uV} i ν family)

/-- The published saturated block is a Serre class in the actual smooth category. -/
instance bernsteinSaturatedBlockProperty_isSerreClass :
    (bernsteinSaturatedBlockProperty i ν family s).IsSerreClass :=
  SmoothRep.irreducibleSubquotientsProperty_isSerreClass
    (IsBernsteinInertialSupport i ν family s)

/-- Finite products preserve the published saturated block property. -/
instance bernsteinSaturatedBlockProperty_isClosedUnderFiniteProducts :
    (bernsteinSaturatedBlockProperty i ν family s).IsClosedUnderFiniteProducts :=
  SmoothRep.irreducibleSubquotientsProperty_isClosedUnderFiniteProducts
    (IsBernsteinInertialSupport i ν family s)

/-- The abelian structure has exactly the full-subcategory additive structure. -/
theorem bernsteinSaturatedBlock_abelian :
    ∃ a : Abelian (BernsteinSaturatedBlock i ν family s),
      a.toPreadditive = Preadditive.fullSubcategory
        (bernsteinSaturatedBlockProperty i ν family s) :=
  ⟨inferInstance, rfl⟩

variable {I : Type (max uF uV)} [DecidableEq I]

/-- Every irreducible subquotient of a direct sum occurs in one summand,
so direct sums preserve the saturated block property. -/
theorem bernsteinSaturatedBlockProperty_directSum
    (A : I → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hA : ∀ t, bernsteinSaturatedBlockProperty i ν family s (A t)) :
    bernsteinSaturatedBlockProperty i ν family s (SmoothRep.directSum A) := by
  intro D hD h
  obtain ⟨t, ht⟩ := SmoothRep.irreducibleSubquotient_directSum A hD h
  exact hA t D hD ht

/-- The actual smooth direct sum and its summand inclusions in the block. -/
def bernsteinSaturatedBlockDirectSumCofan
    (A : I → BernsteinSaturatedBlock i ν family s) : Cofan A :=
  SmoothRep.fullSubcategoryDirectSumCofan
    (bernsteinSaturatedBlockProperty i ν family s) A
    (bernsteinSaturatedBlockProperty_directSum i ν family s
      (fun t => (A t).obj) (fun t => (A t).property))

/-- The actual direct-sum cofan is a coproduct in the published block. -/
def bernsteinSaturatedBlockDirectSumIsColimit
    (A : I → BernsteinSaturatedBlock i ν family s) :
    IsColimit (bernsteinSaturatedBlockDirectSumCofan i ν family s A) :=
  SmoothRep.fullSubcategoryDirectSumIsColimit
    (bernsteinSaturatedBlockProperty i ν family s) A _

omit [DecidableEq I] in
/-- Coproducts exist at the full Hom universe of the published saturated block. -/
instance bernsteinSaturatedBlock_hasColimitsOfShape :
    HasColimitsOfShape (Discrete I) (BernsteinSaturatedBlock i ν family s) := by
  classical
  refine ⟨fun A => ?_⟩
  let B : I → BernsteinSaturatedBlock i ν family s := fun t => A.obj ⟨t⟩
  have : HasColimit (Discrete.functor (A.obj ∘ Discrete.mk)) :=
    ⟨⟨bernsteinSaturatedBlockDirectSumCofan i ν family s B,
      bernsteinSaturatedBlockDirectSumIsColimit i ν family s B⟩⟩
  exact hasColimit_of_iso (Discrete.natIsoFunctor (F := A))

/-- Assemble the actual coproduct constructions for every Hom-sized index type. -/
instance bernsteinSaturatedBlock_hasCoproducts :
    HasCoproducts.{max uF uV} (BernsteinSaturatedBlock i ν family s) := by
  classical
  exact fun J => bernsteinSaturatedBlock_hasColimitsOfShape i ν family s (I := J)

omit [DecidableEq I] in
/-- Finite group-algebra generation makes the actual integer-module Hom
functor preserve every coproduct indexed in the block's Hom universe. -/
theorem bernsteinSaturatedBlock_homPreservesCoproducts
    (P : BernsteinSaturatedBlock i ν family s)
    [Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) P.obj.representation.asModule] :
    Langlands.Renard.HomPreservesCoproducts.{max uF uV} P := by
  intro J
  exact SmoothRep.hom_preservesFullSubcategoryCoproducts
    (bernsteinSaturatedBlockProperty i ν family s)
    (fun B _ => bernsteinSaturatedBlockProperty_directSum i ν family s
      (fun t => (B t).obj) (fun t => (B t).property)) P

/-- A finitely generated projective generator of the actual block has a
module-valued Hom equivalence. No additional block structure is assumed. -/
theorem bernsteinSaturatedBlock_homEquivalence_of_finite_projective_generator
    (P : BernsteinSaturatedBlock i ν family s)
    (hproj : ∀ (Y Z : BernsteinSaturatedBlock i ν family s) (q : Y ⟶ Z),
      Epi q → ∀ f : P ⟶ Z, ∃ g : P ⟶ Y, g ≫ q = f)
    (hfinite : Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
      P.obj.representation.asModule)
    (hgen : ∀ (X Y : BernsteinSaturatedBlock i ν family s) (f g : X ⟶ Y),
      f ≠ g → ∃ h : P ⟶ X, h ≫ f ≠ h ≫ g) :
    (preadditiveCoyonedaObj P).IsEquivalence := by
  let := hfinite
  have hprojective : Projective P := ⟨fun {E Y} f e he => hproj E Y e he f⟩
  have hseparator : IsSeparator P := by
    rw [isSeparator_def]
    intro X Y f g h
    by_contra hfg
    obtain ⟨k, hk⟩ := hgen X Y f g hfg
    exact hk (h k)
  apply Langlands.Renard.preadditiveCoyonedaObj_isEquivalence_of_homSmallProgenerator
  exact ⟨⟨(Langlands.Renard.homProjectiveComparison P).mpr hprojective,
    bernsteinSaturatedBlock_homPreservesCoproducts i ν family s P⟩,
    (Langlands.Renard.homGeneratorComparison P).mpr hseparator⟩

end Langlands.CuspidalSupport
