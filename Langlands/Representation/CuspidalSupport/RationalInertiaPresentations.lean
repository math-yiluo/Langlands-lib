import Langlands.Representation.Category.ConstituentSerre
import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement
import Langlands.CategoryTheory.Renard.GeneratorPresentation
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Actual rational inertia blocks and generator presentations

The actual constituent predicates give abelian full subcategories with exact
inclusions. The explicit small-progenerator hypothesis supplies presentations
by two coproducts of the actual norm-kernel compact induction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))

/-- The actual inertia block's full-subcategory inclusion. -/
def rationalInertiaBlockInclusion :
    RationalInertiaBlock G π ⥤ SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G) :=
  (rationalInertiaBlockProperty G π).ι

/-- The actual inertia complement's full-subcategory inclusion. -/
def rationalInertiaComplementInclusion :
    RationalInertiaComplement G π ⥤ SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G) :=
  (rationalInertiaComplementProperty G π).ι

/-- The actual inertia-block constituent predicate is a Serre class. -/
instance rationalInertiaBlockProperty_isSerreClass :
    (rationalInertiaBlockProperty G π).IsSerreClass :=
  SmoothRep.irreducibleSubquotientsProperty_isSerreClass
    (IsRationalInertiaRelated G π)

/-- The complementary actual constituent predicate is also a Serre class. -/
instance rationalInertiaComplementProperty_isSerreClass :
    (rationalInertiaComplementProperty G π).IsSerreClass :=
  SmoothRep.irreducibleSubquotientsProperty_isSerreClass
    (fun D => ¬ IsRationalInertiaRelated G π D)

/-- Finite products preserve the actual inertia block. -/
instance rationalInertiaBlockProperty_isClosedUnderFiniteProducts :
    (rationalInertiaBlockProperty G π).IsClosedUnderFiniteProducts :=
  SmoothRep.irreducibleSubquotientsProperty_isClosedUnderFiniteProducts
    (IsRationalInertiaRelated G π)

/-- Finite products preserve the complementary actual constituent property. -/
instance rationalInertiaComplementProperty_isClosedUnderFiniteProducts :
    (rationalInertiaComplementProperty G π).IsClosedUnderFiniteProducts :=
  SmoothRep.irreducibleSubquotientsProperty_isClosedUnderFiniteProducts
    (fun D => ¬ IsRationalInertiaRelated G π D)

/-- The actual inertia block has its inherited abelian structure. -/
theorem rationalInertiaBlock_abelian :
    ∃ a : Abelian (RationalInertiaBlock G π),
      a.toPreadditive = Preadditive.fullSubcategory (rationalInertiaBlockProperty G π) :=
  ⟨inferInstance, rfl⟩

/-- The actual complementary subcategory has its inherited abelian structure. -/
theorem rationalInertiaComplement_abelian :
    ∃ a : Abelian (RationalInertiaComplement G π),
      a.toPreadditive =
        Preadditive.fullSubcategory (rationalInertiaComplementProperty G π) :=
  ⟨inferInstance, rfl⟩

/-- The actual inertia-block inclusion preserves finite limits. -/
instance rationalInertiaBlockInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (rationalInertiaBlockProperty G π).ι :=
  SmoothRep.irreducibleSubquotientsInclusion_preservesFiniteLimits
    (IsRationalInertiaRelated G π)

/-- The actual inertia-block inclusion preserves finite colimits. -/
instance rationalInertiaBlockInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (rationalInertiaBlockProperty G π).ι :=
  SmoothRep.irreducibleSubquotientsInclusion_preservesFiniteColimits
    (IsRationalInertiaRelated G π)

/-- The complementary inclusion preserves finite limits. -/
instance rationalInertiaComplementInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (rationalInertiaComplementProperty G π).ι :=
  SmoothRep.irreducibleSubquotientsInclusion_preservesFiniteLimits
    (fun D => ¬ IsRationalInertiaRelated G π D)

/-- The complementary inclusion preserves finite colimits. -/
instance rationalInertiaComplementInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (rationalInertiaComplementProperty G π).ι :=
  SmoothRep.irreducibleSubquotientsInclusion_preservesFiniteColimits
    (fun D => ¬ IsRationalInertiaRelated G π D)

/-- An exact inertia-block row remains exact in actual smooth representations. -/
theorem rationalInertiaBlock_exact_map
    {S : ShortComplex (RationalInertiaBlock G π)} (hS : S.Exact) :
    (S.map (rationalInertiaBlockProperty G π).ι).Exact :=
  hS.map _

/-- A block epimorphism is surjective on the actual smooth carrier. -/
theorem rationalInertiaBlock_surjective_of_epi
    {A B : RationalInertiaBlock G π} (f : A ⟶ B) [Epi f] :
    Function.Surjective (SmoothRep.hom ((rationalInertiaBlockProperty G π).ι.map f)) := by
  exact (SmoothRep.epi_iff_surjective _).mp inferInstance

/-- Every object of the actual lifted inertia block has a right-exact
presentation by two Hom-sized coproducts of the actual compact induction.
The same row is exact and surjective in smooth representations. -/
theorem rationalNormKernelGeneratorPresentation
    (hP : IsRationalNormKernelSmallProgenerator G π) :
    ∃ (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
        (rationalNormKernelCompactInduction G π))
      (hcop : HasCoproducts.{max uF uV}
        (RationalInertiaBlock G (rationalInertiaBaseLift G π))),
      let P : RationalInertiaBlock G (rationalInertiaBaseLift G π) :=
        ⟨rationalNormKernelCompactInduction G π, hmem⟩
      letI := hcop
      ∀ M : RationalInertiaBlock G (rationalInertiaBaseLift G π),
        ∃ (I J : Type (max uF uV))
          (f : (∐ fun _ : J => P) ⟶ (∐ fun _ : I => P))
          (g : (∐ fun _ : I => P) ⟶ M) (h : f ≫ g = 0),
          (ShortComplex.mk f g h).Exact ∧ Epi g ∧
          ((ShortComplex.mk f g h).map
            (rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)).ι).Exact ∧
          Function.Surjective (SmoothRep.hom
            ((rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)).ι.map g)) := by
  obtain ⟨hmem, _, hfaith, hcop, _⟩ := hP
  let : HasCoproducts.{max uF uV}
      (RationalInertiaBlock G (rationalInertiaBaseLift G π)) := hcop
  let P : RationalInertiaBlock G (rationalInertiaBaseLift G π) :=
    ⟨rationalNormKernelCompactInduction G π, hmem⟩
  refine ⟨hmem, hcop, ?_⟩
  dsimp only
  intro M
  obtain ⟨I, J, f, g, h, he, hg⟩ :=
    Langlands.Renard.generatorPresentation P hfaith M
  let := hg
  exact ⟨I, J, f, g, h, he, hg,
    rationalInertiaBlock_exact_map G _ he,
    rationalInertiaBlock_surjective_of_epi G _ g⟩

end Langlands.CuspidalSupport
