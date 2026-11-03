import Langlands.Global.AdelicSiegelFactors
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Canonical standard subgroup schemes in actual adelic factor products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Opposite
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Concrete closed standard unipotent and Levi models for the existing adelic
factor products. No representability witness remains to be supplied. -/
def canonicalStandardFactors : StandardFactorData F G T i ν where
  unipotent := Standard.unipotentScheme i ν ∅
  levi := Standard.leviScheme i ν ∅
  unipotentInclusion := Standard.unipotentHom i ν ∅
  leviInclusion := Standard.leviHom i ν ∅
  unipotent_closed := Standard.isClosedSubgroup_unipotentHom i ν ∅
  levi_closed := Standard.isClosedSubgroup_leviHom i ν ∅
  unipotent_represents := Standard.isRepresentedBy_unipotentHom i ν ∅
  levi_represents := Standard.isRepresentedBy_leviHom i ν ∅

/-- The actual ambient commutative group factors through the represented
standard Levi, since its image centralizes itself on every test scheme. -/
def torusToStandardLevi : T.toGrp ⟶ Standard.leviScheme i ν ∅ :=
  (Standard.isRepresentedBy_leviHom i ν ∅).factorHom i
    ((range_le_torusCentralizer i).trans (torusCentralizer_le_standardLevi i ν ∅))

omit [NumberField F] in
@[simp] theorem torusToStandardLevi_comp :
    torusToStandardLevi F G T i ν ≫ Standard.leviHom i ν ∅ = i :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The same actual commutative group consequently maps to the represented
standard parabolic. -/
def torusToStandardParabolic : T.toGrp ⟶ Standard.parabolicScheme i ν ∅ :=
  torusToStandardLevi F G T i ν ≫ Standard.leviToParabolic i ν ∅

omit [NumberField F] in
@[simp] theorem torusToStandardParabolic_comp :
    torusToStandardParabolic F G T i ν ≫ Standard.parabolicHom i ν ∅ = i := by
  simp only [torusToStandardParabolic, Category.assoc, Standard.leviToParabolic_comp,
    torusToStandardLevi_comp]

/-- The actual adelic image of the represented standard parabolic is exactly
the shared standard subgroup evaluated on the adelic test algebra. -/
theorem standardParabolic_adelic_range :
    (map F (Standard.parabolicScheme i ν ∅) G
      (Standard.parabolicHom i ν ∅)).toMonoidHom.range =
      (standardParabolic i ν ∅).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) :=
  congrArg (fun H : SubgroupFunctor G =>
    H.carrier ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))))
    (Standard.isRepresentedBy_parabolicHom i ν ∅).2

variable (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- Every positive point of a commutative subgroup mapping through T lies in
the actual standard Levi functor. -/
theorem positiveMap_mem_standardLevi
    (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
    positiveMap F G T i T₀ j a ∈
      (standardLevi i ν ∅).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) := by
  apply torusCentralizer_le_standardLevi i ν ∅ _
  apply range_le_torusCentralizer i _
  refine ⟨a.val ≫ (CommGroupScheme.groupHom j).hom.hom, ?_⟩
  change ((a.val ≫ (CommGroupScheme.groupHom j).hom.hom) ≫ i.hom.hom) =
    a.val ≫ (CommGroupScheme.groupHom j ≫ i).hom.hom
  simp only [Grp.comp_hom_hom, Category.assoc]

variable (D : StandardFactorData F G T i ν)
  (C : CompactFactors F G D.unipotent D.levi)

/-- Every existing ordered factor product lies in the actual represented
standard parabolic image times the supplied compact subgroup. -/
theorem productSet_subset_standardParabolic_mul_compact
    (A : Set (PositiveRealTorus.intrinsicSubgroup F T₀)) :
    productSet F G T i ν D C T₀ j A ⊆
      Set.range (map F (Standard.parabolicScheme i ν ∅) G
        (Standard.parabolicHom i ν ∅)) *
        (C.compactSubgroup : Set (AdelicGroupPoints F G)) := by
  intro g hg
  obtain ⟨n, hn, m, hm, a, ha, k, hk, h⟩ :=
    (mem_productSet_iff F G T i ν D C T₀ j A g).mp hg
  have hN := standardUnipotent_le_standardParabolic i ν ∅ _
    (unipotent_mem_standard F G T i ν D n)
  have hM := standardLevi_le_standardParabolic i ν ∅ _
    (levi_mem_standard F G T i ν D m)
  have hA := standardLevi_le_standardParabolic i ν ∅ _
    (positiveMap_mem_standardLevi F G T i ν T₀ j a)
  have hp := ((standardParabolic i ν ∅).carrier
    ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F))))).mul_mem
      (((standardParabolic i ν ∅).carrier _).mul_mem hN hM) hA
  rw [← standardParabolic_adelic_range F G T i ν] at hp
  obtain ⟨p, hp⟩ := hp
  exact ⟨_, ⟨p, hp⟩, k, hk, h⟩

end Langlands.Global.AdelicSiegelFactors
