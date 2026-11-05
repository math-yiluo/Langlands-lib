import Langlands.Global.AdelicSiegelReductionStatement
import Langlands.Global.AdelicDerivedNormOne
import Langlands.GroupScheme.Torus.UnipotentHom

/-! # Norm-one containment from the actual algebraic Siegel setup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global

open Langlands.GroupScheme

namespace AdelicGroupPoints

variable (F : Type u) [Field F]
  (H G : GroupScheme (Spec (CommRingCat.of F)))

/-- Every ambient rational character is trivial along a morphism from an actual
unipotent group scheme. -/
theorem charactersTrivialAlong_of_isUnipotent (f : H ⟶ G) (hH : IsUnipotent H) :
    CharactersTrivialAlong F H G f := by
  intro χ
  exact hH.hom_eq_zero_of_isSplitTorus isSplitTorus_gm (f ≫ χ)

end AdelicGroupPoints

namespace AdelicSiegelFactors

open AdelicGroupPoints

variable (F : Type u) [Field F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- The actual torus composite supplied by the Siegel setup has all-test image
in the ambient derived subgroup. -/
theorem IsSiegelAlgebraicSetup.torus_range_le_derived
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    SubgroupFunctor.range (CommGroupScheme.groupHom j ≫ i) ≤ derivedSubgroup G := by
  obtain ⟨_, _, _, _, _, _, _, ⟨D, d, t₀, hd, _, hcomp⟩, _⟩ := h
  rw [← hcomp]
  intro U x hx
  obtain ⟨y, rfl⟩ := hx
  change U ⟶ T₀.toGrp.X at y
  apply hd.2.le U
  refine ⟨y ≫ t₀.hom.hom, ?_⟩
  change (y ≫ t₀.hom.hom) ≫ d.hom.hom = y ≫ (t₀ ≫ d).hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

/-- The geometric radical clause of the actual setup makes the canonical
unipotent source unipotent. -/
theorem IsSiegelAlgebraicSetup.isUnipotent_standard
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    IsUnipotent (Standard.unipotentScheme i ν ∅) := by
  obtain ⟨_, _, _, _, hN, _, _, _, _⟩ := h
  exact hN.1.isUnipotent

/-- The actual canonical unipotent inclusion has trivial restriction of every
ambient rational character, using the geometric radical in the setup. -/
theorem IsSiegelAlgebraicSetup.charactersTrivialAlong_unipotent
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    CharactersTrivialAlong F (Standard.unipotentScheme i ν ∅) G
      (Standard.unipotentHom i ν ∅) :=
  charactersTrivialAlong_of_isUnipotent F _ _ _
    (h.isUnipotent_standard F G T i ν T₀ j)

/-- The actual positive-torus morphism has trivial restriction of every ambient
rational character, using its derived factorization in the setup. -/
theorem IsSiegelAlgebraicSetup.charactersTrivialAlong_torus
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    CharactersTrivialAlong F T₀.toGrp G (CommGroupScheme.groupHom j ≫ i) :=
  charactersTrivialAlong_of_range_le_derived F _ _ _
    (h.torus_range_le_derived F G T i ν T₀ j)

variable [NumberField F]

/-- Every actual positive-torus point in the algebraic setup lies in the ambient
norm-one adelic group. -/
theorem IsSiegelAlgebraicSetup.positiveMap_mem_normOne
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
    positiveMap F G T i T₀ j a ∈ normOneSubgroup F G :=
  positiveMap_mem_normOne_of_range_le_derived F G T i T₀ j
    (h.torus_range_le_derived F G T i ν T₀ j) a

/-- The actual positive-torus map with codomain in norm-one adelic points,
constructed from the algebraic Siegel setup. -/
def IsSiegelAlgebraicSetup.positiveNormOneMap
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    PositiveRealTorus.intrinsicSubgroup F T₀ →ₜ* normOneSubgroup F G :=
  positiveMapNormOneOfDerived F G T i T₀ j
    (h.torus_range_le_derived F G T i ν T₀ j)

@[simp] theorem IsSiegelAlgebraicSetup.positiveNormOneMap_val
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
    (h.positiveNormOneMap F G T i ν T₀ j a : AdelicGroupPoints F G) =
      positiveMap F G T i T₀ j a := rfl

variable (C : CompactFactors F G
  (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))

/-- The actual ordered canonical product lies in the ambient norm-one adelic
group for every subset of the positive torus, from the algebraic setup alone. -/
theorem IsSiegelAlgebraicSetup.productSet_subset_normOne
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (A : Set (PositiveRealTorus.intrinsicSubgroup F T₀)) :
    productSet F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j A ⊆
      normOneSubgroup F G :=
  Langlands.Global.AdelicSiegelFactors.productSet_subset_normOne F G T i ν
    (canonicalStandardFactors F G T i ν) C T₀ j
    (h.charactersTrivialAlong_unipotent F G T i ν T₀ j)
    (h.charactersTrivialAlong_torus F G T i ν T₀ j) A

/-- In particular, the existing weak chamber product lies in the norm-one group. -/
theorem IsSiegelAlgebraicSetup.weakSiegelProduct_subset_normOne
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j) (t : ℝ≥0ˣ) :
    weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t ⊆
      normOneSubgroup F G :=
  h.productSet_subset_normOne F G T i ν T₀ j C _

/-- Rational left saturation of the actual weak Siegel product still lies in
norm-one points; the converse inclusion is the remaining reduction theorem. -/
theorem IsSiegelAlgebraicSetup.rational_mul_weakSiegelProduct_subset_normOne
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j) (t : ℝ≥0ˣ) :
    (rationalSubgroup F G : Set (AdelicGroupPoints F G)) *
        weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t ⊆
      normOneSubgroup F G := by
  apply Subgroup.mul_subset
  · exact rationalSubgroup_le_normOneSubgroup F G
  · exact h.weakSiegelProduct_subset_normOne F G T i ν T₀ j C t

end AdelicSiegelFactors

end Langlands.Global
