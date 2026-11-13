import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.Representation.Exponents.JacquetNontrivialityTransfer
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorReduction
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Induction.OpenNormalSubgroupInduction

/-! # Compact induction from the norm kernel preserves supercuspidality -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance summandSupercuspidalPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

omit [T2Space k] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The literal point image of the unipotent radical of an actual rational parabolic lies in
the common norm kernel `⁰G(F)`. -/
theorem pointImage_radical_le_rationalCommonNormKernel
    {P U : GroupScheme (Spec (CommRingCat.of k))} (p : P ⟶ G) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    pointImage (r ≫ p) ≤ Plancherel.rationalCommonNormKernel G := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro n hn
  obtain ⟨K, hK, hnK⟩ := isLimitOfCompactSubgroups_pointImage_radical p r
    hp.isClosedSubgroup hr.1 {⟨n, hn⟩} isCompact_singleton
  have hKc : IsCompact ((K.map (pointImage (r ≫ p)).subtype : Subgroup (rationalPoints G)) :
      Set (rationalPoints G)) := by
    rw [Subgroup.coe_map]
    exact hK.image continuous_subtype_val
  exact Plancherel.compactSubgroup_le_rationalCommonNormKernel G _ hKc
    ⟨⟨n, hn⟩, hnK rfl, rfl⟩

/-- Renard VI.10.4, used in the second Lemma: if `π` is supercuspidal and `ρ₀` embeds in the
restriction of `π` to `⁰G(F)`, then `Π_D = ind_{⁰G(F)}^{G(F)} ρ₀` is supercuspidal. -/
theorem isSupercuspidal_rationalNormKernelSummandInduction
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (hπ : IsSupercuspidal π)
    (ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel G))
    (j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) π)
    (hj : Function.Injective (SmoothRep.hom j)) :
    IsSupercuspidal (CuspidalSupport.rationalNormKernelSummandInduction G ρ₀) := by
  intro P M U p l r hp hl hr hmul hnot
  have hπU := hπ P M U p l r hp hl hr hmul hnot
  have hrel : ∀ w : π, w ∈ Jacquet.Localization.relations π.representation
      (pointImage (r ≫ p)) 1 := by
    intro w
    rw [← Jacquet.Localization.mk_eq_zero]
    exact Subsingleton.elim (α := (jacquetFunctor p l r hp hr hl hmul).obj π) _ 0
  let H := Plancherel.rationalCommonNormKernel G
  have hH : IsOpen (H : Set (rationalPoints G)) :=
    Plancherel.isOpen_rationalCommonNormKernel G
  have hPi : Subsingleton ((jacquetFunctor p l r hp hr hl hmul).obj
      (CuspidalSupport.rationalNormKernelCompactInduction G π)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨f, rfl⟩ := Jacquet.Localization.mk_surjective _ (pointImage (r ≫ p)) 1 a
    obtain ⟨g, rfl⟩ := Jacquet.Localization.mk_surjective _ (pointImage (r ≫ p)) 1 b
    have hf := Induction.compactInduced_restrict_mem_relations H hH π.representation
      (SmoothRep.restrictSubgroup H π).isSmooth (pointImage (r ≫ p))
      (pointImage_radical_le_rationalCommonNormKernel p r hp hr) hrel f
    have hg := Induction.compactInduced_restrict_mem_relations H hH π.representation
      (SmoothRep.restrictSubgroup H π).isSmooth (pointImage (r ≫ p))
      (pointImage_radical_le_rationalCommonNormKernel p r hp hr) hrel g
    have hf0 : Jacquet.Localization.mk
        (CuspidalSupport.rationalNormKernelCompactInduction G π).representation
        (pointImage (r ≫ p)) 1 f = 0 := (Jacquet.Localization.mk_eq_zero _ _ _ _).mpr hf
    have hg0 : Jacquet.Localization.mk
        (CuspidalSupport.rationalNormKernelCompactInduction G π).representation
        (pointImage (r ≫ p)) 1 g = 0 := (Jacquet.Localization.mk_eq_zero _ _ _ _).mpr hg
    exact hf0.trans hg0.symm
  have hinj := normalizedJacquetFunctor_map_injective (pointImage (r ≫ p))
    (pointImage (l ≫ p))
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr)
    (isLimitOfCompactSubgroups_pointImage_radical p r hp.isClosedSubgroup hr.1)
    (CuspidalSupport.rationalSummandInductionToUniversal G π ρ₀ j)
    (CuspidalSupport.rationalSummandInductionToUniversal_injective G π ρ₀ j hj)
  exact hinj.subsingleton

end Langlands.Aubert.General.RepresentedParabolic
