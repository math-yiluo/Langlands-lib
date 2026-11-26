import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicHarishChandraRankZero
import Langlands.Global.AdelicInducedHarishChandraStatement
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality

/-! # Reduction of the uniform Harish-Chandra equations to standard parabolic families -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Global

open AdelicGroupPoints Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

/-- The positive-size branch of the uniform equations on an actual standard parabolic family.
The parameter can depend complex-linearly on a finite complex coordinate space. -/
def StandardInducedHarishChandraEquationsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
    [IsClosedImmersion (fam.p J).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p J) K),
    IsMaximalCompactSubgroup F G K →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N → IsClosedSubgroup rho →
      ∀ (hsmooth : SmoothOfRelativeDimension d G.X.hom) (φ : AdelicGroupPoints F G → ℂ),
        fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J φ →
        ∀ {n : ℕ} (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F (fam.P J))
          (s₀ : Fin n → ℂ),
          HasConvolutionEquationAt (K.comap (ofInfinite F G).toMonoidHom)
            (fun s => hK.parameterTwist φ (e s)) s₀

/-- The exact uniform equation for the original root presentation follows from the standard
family case at positive matrix size. -/
theorem inducedHarishChandraEquations_of_standard
    (hstandard : StandardInducedHarishChandraEquationsStatement.{u}) :
    InducedHarishChandraEquationsStatement.{u} := by
  intro F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d
    rho hsmooth hcalc φ hmax hrho hφ n e s₀
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact harishChandraRankZero F G rho hrho hsmooth (K.comap (ofInfinite F G).toMonoidHom)
      (fun s => hK.parameterTwist φ (e s)) s₀
  let fam := StandardParabolicFamily.ofMaximalSplitTorus hG r.data.i r.isCompatible.maximalSplit
    r.data.ν r.isCompatible.generic
  let J : StandardIndex F G fam.i fam.ν :=
    ⟨r.data.J, r.isCompatible.subset_simpleRoots⟩
  have hP : SubgroupFunctor.range p = SubgroupFunctor.range (fam.p J) :=
    r.isCompatible.parabolic_eq.trans (fam.isCompatible J).parabolic_eq.symm
  have hM : SubgroupFunctor.range (l ≫ p) = SubgroupFunctor.range (fam.l J ≫ fam.p J) :=
    r.isCompatible.levi_eq.trans (fam.isCompatible J).levi_eq.symm
  have hRad : SubgroupFunctor.range (iU ≫ p) = SubgroupFunctor.range (fam.iU J ≫ fam.p J) := by
    let : Smooth G.X.hom := hG.smooth
    let := r.isCompatible.parabolic.isClosedSubgroup.mono
    let := (r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup).mono
    obtain ⟨z, hz, hp, hm⟩ := r.isCompatible.realization
    have hdyn := Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer
      (CommGroupScheme.groupHom z ≫ r.data.i) (p := p) (z := l ≫ p)
      ⟨Over.mono_of_mono_left _, hp⟩ ⟨Over.mono_of_mono_left _, hm⟩
      r.isCompatible.levi.isConnectedReductive hU
    have hstd := (standardCocharacter F G hG r.data.T r.data.i r.isCompatible.maximalSplit
      r.data.ν r.isCompatible.generic r.data.J r.isCompatible.subset_simpleRoots).2 z hz
    exact hdyn.trans (hstd.2.2.symm.trans (fam.range_radical_eq_standardUnipotent J).symm)
  let : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
  let f := SubgroupFunctor.rangeFactor (fam.p J) p hP.ge
  have hf : f ≫ p = fam.p J := SubgroupFunctor.rangeFactor_comp _ _ hP.ge
  let hK' := hK.of_range_eq hP
  have hφ' : fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J φ := by
    change IsAutomorphicFunctionOn F G hsmooth hcalc
      (parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J))
      (K.comap (ofInfinite F G).toMonoidHom) rho φ
    rwa [← parabolicQuotientSubgroup_eq_of_range_eq hRad hM]
  have heq := hstandard F G fam J K hK' hmax rho hN hrho hsmooth φ hφ'
    ((parameterRestrict f).comp e.toLinearMap) s₀
  change HasConvolutionEquationAt (K.comap (ofInfinite F G).toMonoidHom)
    (fun s => hK.parameterTwist φ (e s)) s₀
  have hTwist : (fun s => hK.parameterTwist φ (e s)) =
      fun s => hK'.parameterTwist φ (parameterRestrict f (e s)) :=
    funext fun s => hK.parameterTwist_restrict_of_comp_eq hK' f hf φ (e s)
  simpa only [hTwist, LinearMap.comp_apply, LinearEquiv.coe_coe] using heq

end Langlands.Global
