import Langlands.Global.AdelicSiegelChamberReduction
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof

/-! # The empty-root case of actual adelic chamber reduction -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- The exact weak-chamber factorization for fixed actual algebraic data and
one specified compact subgroup. -/
def HasWeakChamberReduction (K : Subgroup (AdelicGroupPoints F G)) : Prop :=
  ∃ t : ℝ≥0ˣ, ∀ g : normOneSubgroup F G, ∃ q : RationalGroupPoints F G,
    ∃ (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
      (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (a : PositiveRealTorus.intrinsicSubgroup F T₀),
      a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t ∧
        ∃ k ∈ K,
          map F _ G (Standard.unipotentHom i ν ∅) n *
              map F _ G (Standard.leviHom i ν ∅) m *
              positiveMap F G T i T₀ j a * k = rational F G q * g

/-- With no simple relative roots, the canonical minimal Levi represents the
whole ambient group functor. -/
def emptyRootStandardLeviIso (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hΔ : simpleRelativeRoots i ν = ∅) : Standard.leviScheme i ν ∅ ≅ G := by
  have hL : standardLevi i ν ∅ = ⊤ := by
    simpa only [hΔ] using (standardParabolicEndpoints F G hG T i hi ν hν).2.2.2.1
  have hrep : (⊤ : SubgroupFunctor G).IsRepresentedBy (Standard.leviHom i ν ∅) := by
    rw [← hL]
    exact Standard.isRepresentedBy_leviHom i ν ∅
  exact hrep.isoOfIsRepresentedBy ⟨inferInstance, SubgroupFunctor.range_id G⟩

omit [NumberField F] in
@[simp] theorem emptyRootStandardLeviIso_hom (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hΔ : simpleRelativeRoots i ν = ∅) :
    (emptyRootStandardLeviIso F G T i ν hG hi hν hΔ).hom =
      Standard.leviHom i ν ∅ := by
  have hL : standardLevi i ν ∅ = ⊤ := by
    simpa only [hΔ] using (standardParabolicEndpoints F G hG T i hi ν hν).2.2.2.1
  have hrep : (⊤ : SubgroupFunctor G).IsRepresentedBy (Standard.leviHom i ν ∅) := by
    rw [← hL]
    exact Standard.isRepresentedBy_leviHom i ν ∅
  have hid : (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) :=
    ⟨inferInstance, SubgroupFunctor.range_id G⟩
  change (hrep.isoOfIsRepresentedBy hid).hom = Standard.leviHom i ν ∅
  simpa only [Category.comp_id] using hrep.isoOfIsRepresentedBy_hom_comp hid

/-- Every norm-one point lifts to the actual canonical minimal Levi in the
empty-root case; norm-one is preserved by the inverse group-scheme morphism. -/
theorem exists_normOne_standardLevi_lift_of_simpleRoots_empty
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hΔ : simpleRelativeRoots i ν = ∅)
    (g : normOneSubgroup F G) :
    ∃ m : normOneSubgroup F (Standard.leviScheme i ν ∅),
      map F _ G (Standard.leviHom i ν ∅) m = (g : AdelicGroupPoints F G) := by
  let e := emptyRootStandardLeviIso F G T i ν hG hi hν hΔ
  refine ⟨mapNormOne F G _ e.inv g, ?_⟩
  have he : e.inv ≫ Standard.leviHom i ν ∅ = 𝟙 G := by
    rw [← emptyRootStandardLeviIso_hom F G T i ν hG hi hν hΔ]
    exact e.inv_hom_id
  change (g.val ≫ e.inv.hom.hom) ≫ (Standard.leviHom i ν ∅).hom.hom = g.val
  rw [Category.assoc, ← Grp.comp_hom_hom, he]
  simp

/-- The actual chamber reduction holds with threshold one when the simple
relative-root set is empty, for every subgroup K. No compactness input is used. -/
theorem hasWeakChamberReduction_of_simpleRoots_empty
    (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (hΔ : simpleRelativeRoots i ν = ∅)
    (K : Subgroup (AdelicGroupPoints F G)) :
    HasWeakChamberReduction F G T i ν T₀ j K := by
  refine ⟨1, fun g => ?_⟩
  obtain ⟨m, hm⟩ := exists_normOne_standardLevi_lift_of_simpleRoots_empty
    F G T i ν hG hS.1 hS.2.1 hΔ g
  refine ⟨1, 1, m, 1, ?_, 1, K.one_mem, ?_⟩
  · change ∀ α ∈ simpleRelativeRoots i ν,
      (1 : ℝ≥0ˣ) ≤ PositiveRealTorus.normCharacter F T₀ (j ≫ α) 1
    rw [hΔ]
    simp
  · simp only [map_one, one_mul, mul_one]
    exact hm

end Langlands.Global.AdelicSiegelFactors
