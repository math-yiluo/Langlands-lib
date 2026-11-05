import Langlands.Representation.Plancherel.RationalComplexParameterQuotientStatement
import Langlands.Representation.Plancherel.RationalComplexParameter
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # The quotient topology of actual complex exponential parameters -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

private theorem complexExpUnits_isOpenQuotientMap :
    IsOpenQuotientMap (fun z : ℂ => Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)) := by
  have h : IsOpenQuotientMap
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w
      exact ⟨Complex.log w.val, Subtype.ext (Complex.exp_log w.property)⟩
    · exact Complex.continuous_exp.subtype_mk _
    · exact (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr
        Complex.isOpenMap_exp
  convert (unitsHomeomorphNeZero (G₀ := ℂ)).symm.isOpenQuotientMap.comp h using 1
  funext z
  apply (unitsHomeomorphNeZero (G₀ := ℂ)).injective
  exact ((unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply _).symm

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

private def scaledComplexExp (z : ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp (-z * (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)))
    (Complex.exp_ne_zero _)

private theorem scaledComplexExp_isOpenQuotientMap :
    IsOpenQuotientMap (scaledComplexExp (F := F)) := by
  have hL : (Real.log (LocalField.residueCardinality F : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by
      exact_mod_cast LocalField.residueCardinality_gt_one F)).ne'
  exact complexExpUnits_isOpenQuotientMap.comp
    ((Homeomorph.neg ℂ).trans (Homeomorph.mulRight₀ _ hL)).isOpenQuotientMap

section ParameterTopology

local instance : TopologicalSpace (rationalImageComplexFunctionals G) :=
  rationalImageComplexParameterTopology G

/-- In the published finite coordinates, the actual exponential is a product
of scalar open quotient maps. -/
theorem rationalImageComplexCharacter_isOpenQuotientMap
    (hG : GroupScheme.IsConnectedReductive G) :
    IsOpenQuotientMap (rationalImageComplexCharacter G) := by
  let p := (rationalImageComplexParameterContinuousCoordinates G hG).toHomeomorph
  let c := (rationalReductiveImageCharacterCoordinates G hG).toHomeomorph
  have heq : rationalImageComplexCharacter G =
      c.symm ∘ Pi.map (fun _ : Fin (rationalImageRank G) => scaledComplexExp (F := F)) ∘ p := by
    funext lam
    apply c.injective
    change c (rationalImageComplexCharacter G lam) = c (c.symm _)
    rw [c.apply_symm_apply]
    rfl
  rw [heq]
  exact c.symm.isOpenQuotientMap.comp
    ((IsOpenQuotientMap.piMap (fun _ : Fin (rationalImageRank G) =>
      scaledComplexExp_isOpenQuotientMap (F := F))).comp p.isOpenQuotientMap)

/-- The exact period fibers induce the prescribed quotient homeomorphism. -/
theorem rationalImageComplexParameterQuotient_exists
    (hG : GroupScheme.IsConnectedReductive G) :
    ∃ e : (rationalImageComplexFunctionals G ⧸ rationalImagePeriodLattice G) ≃ₜ
        rationalImageCharacters G,
      ∀ lam : rationalImageComplexFunctionals G,
        e (QuotientAddGroup.mk lam) = rationalImageComplexCharacter G lam := by
  let f : (rationalImageComplexFunctionals G ⧸ rationalImagePeriodLattice G) →
      rationalImageCharacters G :=
    Quotient.lift (rationalImageComplexCharacter G) (by
      intro lam mu h
      exact (rationalImageComplexCharacter_eq_iff G lam mu).mpr
        (QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.sound h)))
  have hbij : Function.Bijective f := by
    constructor
    · intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro lam mu h
      exact QuotientAddGroup.eq_iff_sub_mem.mpr
        ((rationalImageComplexCharacter_eq_iff G lam mu).mp h)
    · intro chi
      obtain ⟨lam, h⟩ := rationalImageComplexCharacter_surjective G hG chi
      exact ⟨QuotientAddGroup.mk lam, h⟩
  let e := Equiv.ofBijective f hbij
  have hopen := rationalImageComplexCharacter_isOpenQuotientMap G hG
  have hc : Continuous e := by
    apply (QuotientAddGroup.isQuotientMap_mk (rationalImagePeriodLattice G)).continuous_iff.mpr
    exact hopen.continuous
  have ho : IsOpenMap e :=
    IsOpenMap.of_comp QuotientAddGroup.continuous_mk
      QuotientAddGroup.mk_surjective hopen.isOpenMap
  exact ⟨e.toHomeomorphOfContinuousOpen hc ho, fun _ => rfl⟩

end ParameterTopology

/-- All four topological quotient assertions, including the canonical map on
actual rational points. -/
theorem rationalComplexParameterQuotient : RationalComplexParameterQuotientStatement.{u} := by
  intro F _ _ _ _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  let := rationalImageComplexParameterTopology G
  have hopen := rationalImageComplexCharacter_isOpenQuotientMap G hG
  obtain ⟨e, he⟩ := rationalImageComplexParameterQuotient_exists G hG
  refine ⟨hopen, ⟨e, he⟩, ?_, ?_⟩
  · change IsOpenQuotientMap
      ((rationalCanonicalImageUnramifiedContinuousEquiv G) ∘ rationalImageComplexCharacter G)
    exact (rationalCanonicalImageUnramifiedContinuousEquiv G).toHomeomorph.isOpenQuotientMap.comp
      hopen
  · refine ⟨e.trans (rationalCanonicalImageUnramifiedContinuousEquiv G).toHomeomorph, ?_⟩
    intro lam
    change rationalCanonicalImageUnramifiedContinuousEquiv G (e (QuotientAddGroup.mk lam)) =
      rationalCanonicalImageUnramifiedContinuousEquiv G (rationalImageComplexCharacter G lam)
    rw [he]

end Langlands.Plancherel
