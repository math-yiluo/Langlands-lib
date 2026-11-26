import Langlands.Global.AdelicTemperedVanishingReduction
import Langlands.Global.AdelicLocalFinitenessProductBridge
import Langlands.Global.AdelicRelativeAmbientParameterProduct
import Langlands.Global.AdelicEisensteinImaginaryContinuation
import Langlands.Global.AdelicNestedSplitComponents
import Langlands.GroupScheme.Lie.AdjointDeterminantReductiveProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof

/-! # The weak constant term along the whole group -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

omit [NumberField F] in
private theorem topRanges :
    SubgroupFunctor.range (fam.p fam.top) = ⊤ ∧
    SubgroupFunctor.range (fam.l fam.top ≫ fam.p fam.top) = ⊤ := by
  have h := standardParabolicEndpoints F G fam.connectedReductive fam.T fam.i fam.maximalSplit
    fam.ν fam.generic
  exact ⟨(fam.isCompatible fam.top).parabolic_eq.trans h.2.2.1,
    (fam.isCompatible fam.top).levi_eq.trans h.2.2.2.1⟩

omit [NumberField F] in
private theorem topParabolicRepresented :
    (⊤ : SubgroupFunctor G).IsRepresentedBy (fam.p fam.top) := by
  rw [← (fam.topRanges).1]
  exact (fam.isCompatible fam.top).parabolic.isClosedSubgroup.isRepresentedBy_range

omit [NumberField F] in
private theorem topLeviRepresented :
    (⊤ : SubgroupFunctor G).IsRepresentedBy (fam.l fam.top ≫ fam.p fam.top) := by
  rw [← (fam.topRanges).2]
  exact ((fam.isCompatible fam.top).levi.isClosedSubgroup.comp
    (fam.isCompatible fam.top).parabolic.isClosedSubgroup).isRepresentedBy_range

private theorem top_positive_map_mem_canonical {x : AdelicGroupPoints F (fam.P fam.top)}
    (hx : x ∈ fam.positiveSplitComponent fam.top) :
    map F (fam.P fam.top) G (fam.p fam.top) x ∈ RestrictionSplitCentre.canonicalSubgroup F G := by
  let a := fam.a fam.top
  let e := fam.topLeviRepresented.topIso
  have he : e.hom = fam.l fam.top ≫ fam.p fam.top := fam.topLeviRepresented.topIso_hom
  have ha : IsSplitComponent a := (fam.isCompatible fam.top).splitComponent
  have hc : IsSplitComponent (a ≫ e.hom) := by
    refine ⟨⟨(IsSplitSubtorus.comp_iso_iff a e).mpr ha.1.1, ha.1.2.comp_iso e⟩, ?_⟩
    intro B b hb f hf
    apply ha.2 B (b ≫ e.inv)
      ⟨(IsSplitSubtorus.comp_iso_iff b e.symm).mpr hb.1, hb.2.comp_iso e.symm⟩ f
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun z => z ≫ e.inv) hf
  rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup hc, he]
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨b, hb, ?_⟩
  change map F _ G (a ≫ fam.l fam.top ≫ fam.p fam.top) b =
    map F _ G (fam.p fam.top) (map F _ _ (a ≫ fam.l fam.top) b)
  rw [← map_comp_apply_of_hom, Category.assoc]

private theorem topParabolicQuotient_le_rational :
    parabolicQuotientSubgroup F (fam.p fam.top) (fam.iU fam.top) (fam.l fam.top) ≤
      rationalSubgroup F G := by
  apply sup_le
  · rintro _ ⟨x, rfl⟩
    have hr := (fam.range_radical_eq_standardUnipotent fam.top).trans
      (standardUnipotent_simple_eq_bot fam.i fam.ν)
    have hx := (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩ :
      (map F (fam.U fam.top) G (fam.iU fam.top ≫ fam.p fam.top) x) ∈
        (SubgroupFunctor.range (fam.iU fam.top ≫ fam.p fam.top)).carrier _)
    rw [hr] at hx
    change map F _ G (fam.iU fam.top ≫ fam.p fam.top) x ∈ rationalSubgroup F G
    rw [Subgroup.mem_bot.mp hx]
    exact (rationalSubgroup F G).one_mem
  · rintro _ ⟨x, rfl⟩
    exact ⟨(fam.M fam.top).affinePointsTarget (fam.l fam.top ≫ fam.p fam.top) (CommAlgCat.of F F) x,
      DFunLike.congr_fun (rational_naturality F (fam.M fam.top) (fam.l fam.top ≫ fam.p fam.top)) x⟩

/-- At the full-group index, a form with the specified unitary split-centre character is its
own weak constant term. The weighted norm is unnecessary for this identification. -/
theorem isWeakConstantTerm_top_of_unitary {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
    {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    (ν : RealCharacterParameter F G)
    (hν : ∀ a ∈ RestrictionSplitCentre.canonicalSubgroup F G, ∀ g : AdelicGroupPoints F G,
      φ (a * g) = parameterPower F G (imaginaryParameter F G ν) a * φ g) :
    fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho fam.top φ φ := by
  classical
  let p := fam.p fam.top
  let v := realCharacterParameterPullback p ν
  let lam := imaginaryParameter F (fam.P fam.top) v
  have hReal : parameterRealPart F (fam.P fam.top) lam = 0 :=
    parameterRealPart_imaginaryParameter v
  refine ⟨{lam}, fun _ => φ, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [fam.constantTerm_top, Finset.sum_singleton]
  · intro _ _
    exact ⟨fun x hx => hφ.1 x (fam.topParabolicQuotient_le_rational hx), hφ.2⟩
  · intro z hz
    rw [Finset.mem_singleton.mp hz]
    have hred : IsConnectedReductive (fam.P fam.top) :=
      fam.connectedReductive.of_iso fam.topParabolicRepresented.topIso
    have hδ : halfModulusParameter F (fam.P fam.top) = 0 := by
      rw [halfModulusParameter, Lie.connectedReductiveAdjointDeterminant F _ hred,
        TensorProduct.tmul_zero]
    apply (fam.hasExponent_iff fam.top lam φ).mpr
    rw [hδ, add_zero]
    refine ⟨0, fun g => ⟨fun _ => φ g, ?_, ?_⟩⟩
    · have hOne : (1 : RealCharacterDual F (fam.P fam.top) → ℂ) ∈ polynomialFunctions _ 0 := by
        apply Submodule.subset_span
        exact ⟨0, le_rfl, Fin.elim0, by funext y; simp⟩
      simpa only [Pi.smul_def, Pi.one_def, smul_eq_mul, mul_one] using
        Submodule.smul_mem (polynomialFunctions _ 0) (φ g) hOne
    · intro x hx
      have hval := hν _ (fam.top_positive_map_mem_canonical hx) g
      rw [unnormalizedAction, hval, ← parameterPower_parameterRestrict p,
        ← imaginaryParameter_pullback (F := F) (p := p)]
      change (parameterPower F _ lam x * φ g) * parameterPower F _ (-lam) x = φ g
      rw [mul_right_comm, ← parameterPower_add, add_neg_cancel]
      simp [parameterPower]
  · unfold unitaryExponentSum
    rw [show ({lam} : Finset _).filter (fun z => parameterRealPart F (fam.P fam.top) z = 0) =
      {lam} from Finset.filter_eq_self.mpr fun z hz => (Finset.mem_singleton.mp hz).symm ▸ hReal,
      Finset.sum_singleton]

/-- The full-group weak constant term of a logarithmically square-integrable form is the form
itself. -/
theorem isWeakConstantTerm_top {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
    {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc φ) :
    fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho fam.top φ φ := by
  obtain ⟨ν, hν⟩ := hφ.2.1
  exact fam.isWeakConstantTerm_top_of_unitary hφ.1 ν hν

end Langlands.Global.StandardParabolicFamily
