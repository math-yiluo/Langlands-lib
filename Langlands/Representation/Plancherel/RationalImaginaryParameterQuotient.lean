import Langlands.Representation.Plancherel.RationalImaginaryParameterQuotientStatement
import Langlands.Representation.Plancherel.RationalComplexParameterQuotient
import Mathlib.Topology.LocalAtTarget

/-! # Actual period discreteness and the compact imaginary quotient -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

private theorem original_complex_period_ne_zero :
    rationalImageComplexPeriod (F := F) ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  · exact_mod_cast (Real.log_pos (by
      exact_mod_cast LocalField.residueCardinality_gt_one F)).ne'

section ParameterTopology

local instance : TopologicalSpace (rationalImageComplexFunctionals G) :=
  rationalImageComplexParameterTopology G

/-- Finite coordinates place the actual periods in a finite product of
scaled complex integer subgroups. -/
theorem rationalImagePeriodLattice_discrete_closed
    (hG : GroupScheme.IsConnectedReductive G) :
    DiscreteTopology (rationalImagePeriodLattice G) ∧
      IsClosed (rationalImagePeriodLattice G : Set (rationalImageComplexFunctionals G)) := by
  let b := rationalReductiveValuationBasis G hG
  let e := (rationalImageComplexParameterContinuousCoordinates G hG).toHomeomorph
  let f : (Fin (rationalImageRank G) → ℤ) → rationalImageComplexFunctionals G :=
    fun n => e.symm (fun i => rationalImageComplexPeriod (F := F) * (n i : ℂ))
  have hf : IsClosedEmbedding f :=
    e.symm.isClosedEmbedding.comp (IsClosedEmbedding.piMap fun _ =>
      (Homeomorph.mulLeft₀ _ (original_complex_period_ne_zero (F := F))).isClosedEmbedding.comp
        Complex.isClosedEmbedding_intCast)
  have hrange : Set.range f =
      (rationalImagePeriodLattice G : Set (rationalImageComplexFunctionals G)) := by
    ext lam
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨((b.constr ℤ) n).toAddMonoidHom, ?_⟩
      apply e.injective
      rw [e.apply_symm_apply]
      funext i
      change rationalImageComplexPeriod (F := F) *
        ((((b.constr ℤ) n) (b i)) : ℂ) = _
      rw [Module.Basis.constr_basis]
    · rintro ⟨n, rfl⟩
      refine ⟨fun i => n (b i), ?_⟩
      apply e.injective
      change e (e.symm _) = _
      rw [e.apply_symm_apply]
      rfl
  have : DiscreteTopology (Set.range f) := hf.isEmbedding.toHomeomorph.discreteTopology
  exact ⟨(Homeomorph.setCongr hrange).discreteTopology, hrange ▸ hf.isClosed_range⟩

/-- Inherited topology preserves discreteness and closedness of the same
original periods inside the imaginary group. -/
theorem rationalImageImaginaryPeriodLattice_discrete_closed
    (hG : GroupScheme.IsConnectedReductive G) :
    DiscreteTopology (rationalImageImaginaryPeriodLattice G) ∧
      IsClosed (rationalImageImaginaryPeriodLattice G :
        Set (rationalImageImaginaryParameters G)) := by
  obtain ⟨hd, hc⟩ := rationalImagePeriodLattice_discrete_closed G hG
  let inc : rationalImageImaginaryPeriodLattice G → rationalImagePeriodLattice G :=
    fun lam => ⟨lam.val.val, lam.property⟩
  have hval : IsEmbedding (Subtype.val : rationalImagePeriodLattice G →
      rationalImageComplexFunctionals G) := IsEmbedding.subtypeVal
  have hcomp : IsEmbedding ((Subtype.val : rationalImagePeriodLattice G →
      rationalImageComplexFunctionals G) ∘ inc) := by
    change IsEmbedding ((Subtype.val : rationalImageImaginaryParameters G →
      rationalImageComplexFunctionals G) ∘
        (Subtype.val : rationalImageImaginaryPeriodLattice G →
          rationalImageImaginaryParameters G))
    exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hinc : IsEmbedding inc :=
    hval.of_comp_iff.mp hcomp
  exact ⟨hinc.discreteTopology, hc.preimage continuous_subtype_val⟩

/-- The imaginary exponential is the restriction of the complex open quotient
map to the preimage of the unitary subgroup. -/
theorem rationalImageImaginaryCharacter_isOpenQuotientMap
    (hG : GroupScheme.IsConnectedReductive G) :
    IsOpenQuotientMap (rationalImageImaginaryCharacter G) := by
  have hpre :
      (rationalImageComplexCharacter G) ⁻¹'
          (unitaryCharacters (rationalDiscreteValuationImage G) :
            Set (rationalImageCharacters G)) =
        (rationalImageImaginaryParameters G : Set (rationalImageComplexFunctionals G)) := by
    ext lam
    exact (rationalImageComplexCharacter_unitary_iff G lam).trans
      (mem_rationalImageImaginaryParameters_iff G lam).symm
  let e := (Homeomorph.setCongr hpre).symm
  have hopen := (rationalImageComplexCharacter_isOpenQuotientMap G hG).restrictPreimage
    (unitaryCharacters (rationalDiscreteValuationImage G) : Set (rationalImageCharacters G))
  convert hopen.comp e.isOpenQuotientMap using 1
  funext lam
  apply Subtype.ext
  rfl

/-- The restricted exponential has exactly the same original period fibers. -/
theorem rationalImageImaginaryCharacter_eq_iff
    (lam mu : rationalImageImaginaryParameters G) :
    rationalImageImaginaryCharacter G lam = rationalImageImaginaryCharacter G mu ↔
      lam - mu ∈ rationalImageImaginaryPeriodLattice G := by
  rw [Subtype.ext_iff]
  exact rationalImageComplexCharacter_eq_iff G lam.val mu.val

/-- Exact period fibers and openness give the prescribed quotient
homeomorphism. -/
theorem rationalImageImaginaryParameterQuotient_exists
    (hG : GroupScheme.IsConnectedReductive G) :
    ∃ e : (rationalImageImaginaryParameters G ⧸
        rationalImageImaginaryPeriodLattice G) ≃ₜ
          unitaryCharacters (rationalDiscreteValuationImage G),
      ∀ lam : rationalImageImaginaryParameters G,
        e (QuotientAddGroup.mk lam) = rationalImageImaginaryCharacter G lam := by
  let f : (rationalImageImaginaryParameters G ⧸ rationalImageImaginaryPeriodLattice G) →
      unitaryCharacters (rationalDiscreteValuationImage G) :=
    Quotient.lift (rationalImageImaginaryCharacter G) (by
      intro lam mu h
      exact (rationalImageImaginaryCharacter_eq_iff G lam mu).mpr
        (QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.sound h)))
  have hopen := rationalImageImaginaryCharacter_isOpenQuotientMap G hG
  have hbij : Function.Bijective f := by
    constructor
    · intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro lam mu h
      exact QuotientAddGroup.eq_iff_sub_mem.mpr
        ((rationalImageImaginaryCharacter_eq_iff G lam mu).mp h)
    · intro chi
      obtain ⟨lam, h⟩ := hopen.surjective chi
      exact ⟨QuotientAddGroup.mk lam, h⟩
  let e := Equiv.ofBijective f hbij
  have hc : Continuous e := by
    apply (QuotientAddGroup.isQuotientMap_mk
      (rationalImageImaginaryPeriodLattice G)).continuous_iff.mpr
    exact hopen.continuous
  have ho : IsOpenMap e :=
    IsOpenMap.of_comp QuotientAddGroup.continuous_mk
      QuotientAddGroup.mk_surjective hopen.isOpenMap
  exact ⟨e.toHomeomorphOfContinuousOpen hc ho, fun _ => rfl⟩

/-- Compactness of the actual unitary character group transfers to its
imaginary-parameter quotient. -/
theorem compactSpace_rationalImageImaginaryParameterQuotient
    (hG : GroupScheme.IsConnectedReductive G) :
    CompactSpace (rationalImageImaginaryParameters G ⧸
      rationalImageImaginaryPeriodLattice G) := by
  obtain ⟨e, _⟩ := rationalImageImaginaryParameterQuotient_exists G hG
  have : CompactSpace (unitaryCharacters (rationalDiscreteValuationImage G)) :=
    compactSpace_unitaryRationalImageCharacters G
  exact e.symm.compactSpace

end ParameterTopology

/-- The original periods are discrete and closed, and their compact imaginary
quotient is identified by the actual exponential with unitary characters,
both on the valuation image and on canonical rational points. -/
theorem rationalImaginaryParameterQuotient :
    RationalImaginaryParameterQuotientStatement.{u} := by
  intro F _ _ _ _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  let := rationalImageComplexParameterTopology G
  obtain ⟨hpd, hpc⟩ := rationalImagePeriodLattice_discrete_closed G hG
  obtain ⟨hid, hic⟩ := rationalImageImaginaryPeriodLattice_discrete_closed G hG
  have hcompact := compactSpace_rationalImageImaginaryParameterQuotient G hG
  have hopen := rationalImageImaginaryCharacter_isOpenQuotientMap G hG
  obtain ⟨e, he⟩ := rationalImageImaginaryParameterQuotient_exists G hG
  let c := rationalUnitaryUnramifiedContinuousEquiv G
    (continuous_rationalValuationImageProjection G)
  refine ⟨hpd, hpc, hid, hic, hcompact, hopen, ⟨e, he⟩, ?_, ?_⟩
  · change IsOpenQuotientMap (c ∘ rationalImageImaginaryCharacter G)
    exact c.toHomeomorph.isOpenQuotientMap.comp hopen
  · refine ⟨e.trans c.toHomeomorph, ?_⟩
    intro lam
    change c (e (QuotientAddGroup.mk lam)) = c (rationalImageImaginaryCharacter G lam)
    rw [he]

end Langlands.Plancherel
