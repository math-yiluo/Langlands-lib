import Langlands.Representation.Plancherel.ActualCommonLeviUnitaryIrreducibilityStatement
import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericLocus
import Langlands.Representation.Plancherel.DynamicCommonLeviPresentations
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LeftHaarQuotientUnitarity
import Langlands.Representation.Aubert.General.RationalSameLeviGenericIrreducibilityReduction
import Langlands.Representation.Families.InducedTwistUnitaryGenericIrreducibility
import Langlands.Representation.Families.UnramifiedPolynomialWitness
import Langlands.Representation.Unitary.Restriction

/-! # Dense unitary irreducibility of actual common-Levi normalized induction -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Aubert.General.RepresentedParabolic HarishChandraSchwartz
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition ActualCommonLeviTensor
open DynamicCommonLeviPresentationComparison
open Renard.AlgebraicFamily Renard.AlgebraicFamily.UnramifiedPolynomialWitness

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure]

/-- For each parabolic with the given common Levi, irreducible inductions occur densely
among the unitary unramified twists of the square-integrable inducing representation. -/
theorem denseUnitaryIrreducibility : DenseUnitaryIrreducibilityStatement χ A C hC qMeasure := by
  classical
  intro hG hsq hA hsplit ψ hψ
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨T, a, ha, -⟩ := hsplit
  let d := DynamicCommonLeviPresentations.parabolicData χ ψ hG hψ T a ha
  have hp := d.r.isCompatible.parabolic
  have hl := d.r.isCompatible.levi
  have hmul := d.r.isIso_subgroupMultiplication_of_radical d.radical
  let ρ := SmoothRep.pullback (parameterHomeomorph χ) A
  have hρ : ρ.IsIrreducible :=
    (SmoothRep.isIrreducible_pullbackFunctor_obj_iff _ A).mpr hA
  have hρadm : ρ.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv A.representation (parameterHomeomorph χ) hsq.1
  have hAunit := isUnitarizable_of_irreducible_quotient_memLp C hC qMeasure
    (dynamicCentralizer_compactOpenCofinal F G χ) hsq hA
  have hρunit : IsUnitarizable ρ.representation := hAunit.comp (parameterHomeomorph χ).toMonoidHom
  obtain ⟨f, hf, hirr⟩ := exists_generic_leviInduction_isIrreducible_of_unitary.{u, uV} F G hG
    d.P (parameterScheme χ) d.U d.p d.l d.n hp hl d.radical hmul T a ha ρ hρ hρadm hρunit
  have hM := hl.isConnectedReductive
  let b : unramifiedRegularFunctions (normCharacters χ) :=
    rationalCanonicalUnramifiedLaurentAlgebraEquiv (parameterScheme χ) hM (polynomialToLaurent _ f)
  have hmem (z : unramifiedCharacters (normCharacters χ)) :
      z ∈ rationalUnramifiedPrincipalOpen (parameterScheme χ) hM f ↔ b.val z ≠ 0 := by
    rw [mem_rationalUnramifiedPrincipalOpen]
    dsimp only [b]
    rw [canonicalLaurent_eval, polynomialToLaurent_eval]
  obtain ⟨z₀, hz₀⟩ := (dense_rationalUnramifiedPrincipalOpen (parameterScheme χ) hM f hf).nonempty
  have hb : b ≠ 0 := by
    intro he
    have hn := (hmem z₀).mp hz₀
    rw [he] at hn
    exact hn rfl
  refine (dense_unitary_regular_nonzero χ hG b hb).mono ?_
  intro z hz
  let ζ := unitaryParameter χ z
  have hζ := (hmem ζ).mpr hz
  have hζunit : ∀ m, ‖(ζ.val m : ℂ)‖ = 1 := z.property.2
  refine (leviInduction_isIrreducible_iff_of_pointImage d.p d.l d.n hp d.radical hl hmul
    (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (parabolicPoints_eq χ ψ d.realizes) (leviPoints_eq χ ψ d.realizes)
    (radicalPoints_eq χ ψ d.realizes)
    (ρ.twist ζ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ζ))
    (twistObject χ ζ A) (LinearEquiv.refl ℂ A) (parameterHomeomorph χ) ?_ ?_).mp
    (hirr ζ hζ hζunit)
  · intro m
    rw [d.levi_comp]
    rfl
  · intro m x
    change (ζ.val m : ℂ) • A.representation (parameterHomeomorph χ m) x =
      (ζ.val ((parameterHomeomorph χ).symm (parameterHomeomorph χ m)) : ℂ) •
        A.representation (parameterHomeomorph χ m) x
    rw [ContinuousMulEquiv.symm_apply_apply]

end Langlands.Plancherel.ActualCommonLeviV3
