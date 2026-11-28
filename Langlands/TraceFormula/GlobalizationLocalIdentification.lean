import Langlands.Automorphic.PresentedLocalComponentHilbertOccurrence
import Langlands.Automorphic.RealizationSummandClassMap
import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Automorphic.OperatorScalarCentralCharacter
import Langlands.Global.IdeleClosedSubgroupDensity
import Langlands.Automorphic.CuspidalUnitaryLocalGenericity
import Langlands.Automorphic.CuspidalUnitaryLocalUnitarityProof
import Langlands.BaseChange.TwistedLocalGroupTransport
import Langlands.TraceFormula.IsotypicTrace.CuspidalOccurrenceReduction

/-!
# Local components of a cuspidal summand detected by compressed traces

See `GlobalizationLocalIdentification.md`.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula.GlobalizationIdentification

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions Langlands.Global
open Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.HarmonicAnalysis Langlands.Analysis.OperatorIdeals

local instance identificationGLAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance identificationGLSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance identificationRationalGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance identificationContinuousGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance identificationSmoothGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance identificationFormsGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.AutomorphicForms F n) := Submodule.addCommGroup _
local instance identificationStableGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance identificationLocalGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    {v : Langlands.Global.FinitePlace F} (D : LocalRealization F n v) : AddCommGroup D.Space :=
  Submodule.addCommGroup _
local instance identificationRealizationGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (R : OperatorRealization F n) : AddCommGroup R.Space :=
  Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
  (hPD : ParabolicDynamicStatement.{u})
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "G" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "hG" => GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "πc" => fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc

set_option maxHeartbeats 1600000 in
/-- **Unitarity of the central character.** A cuspidal realization whose vectors have
`L²` classes in the cuspidal spectrum has a unitary central character: right translation is
isometric on `L²`, and the class map is injective and intertwines the finite adelic action. -/
theorem hasUnitaryCentralCharacter_of_formClass (R : CuspidalOperatorRealization F r)
    (Φ : R.Space →ₗ[ℂ] S)
    (hΦ : ∀ f, IsGeneralLinearFormClass F r T i (Φ f) (R.realization.toContinuous f)) :
    ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter R := by
  let hdesc : RealizationSummand.HasPositiveDescent F r T i R := fun f =>
    ⟨(hΦ f).choose, (hΦ f).choose_spec.1⟩
  let c := RealizationSummand.classMap F r T i R hdesc hi I e hc hPD
  have hinj : Function.Injective c :=
    RealizationSummand.classMap_injective F r T i R hdesc hi I e hc hPD
  obtain ⟨χ, hχ⟩ : ∃ χ : HeckeCharacter F, R.HasCentralCharacter χ :=
    (R.realization.existsUnique_hasCentralCharacter R.irreducible).exists
  obtain ⟨f, hf⟩ := exists_ne (0 : R.Space)
  have hcf : c f ≠ 0 := fun h => hf (hinj (h.trans (map_zero c).symm))
  have local_norm (v : Langlands.Global.FinitePlace F) (a : (FiniteCompletion F v)ˣ) :
      ‖(χ.finiteComponent v a : ℂ)‖ = 1 := by
    let g := Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) a
    let z : ℂ := χ.finiteComponent v a
    have hmem : finiteIdeleInclusion F v a ∈ R.realization.centralCharacterSubgroup χ :=
      (R.realization.mem_centralCharacterSubgroup χ _).mpr fun w x =>
        R.realization.centralCharacter_evaluate χ hχ w _ x
    have hscalar : R.realization.localRepresentation v g f = z • f :=
      (R.realization.finiteIdeleInclusion_mem_centralCharacterSubgroup_iff χ v a).mp hmem f
    have hfin := RealizationSummand.classMap_finite F r T i R hdesc hi I e hc hPD
      (FiniteAdelicGL.localInclusion F (r + 1) v g) f
    have hnorm : ‖c (R.realization.localRepresentation v g f)‖ = ‖c f‖ := by
      change ‖c (R.realization.finiteRepresentation
        (FiniteAdelicGL.localInclusion F (r + 1) v g) f)‖ = _
      rw [hfin]
      exact norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc _ _
    rw [hscalar, map_smul, norm_smul] at hnorm
    exact (mul_eq_right₀ (norm_ne_zero_iff.mpr hcf)).mp hnorm
  let modulus : Ideles F →* ℝ :=
    normHom.toMonoidHom.comp ((Units.coeHom ℂ).comp χ.onIdeles.toMonoidHom)
  have hclosed : IsClosed (modulus.ker : Set (Ideles F)) := by
    change IsClosed {a : Ideles F | ‖(χ.onIdeles a : ℂ)‖ = 1}
    exact isClosed_eq (Units.continuous_val.comp χ.onIdeles.continuous).norm continuous_const
  have htop : modulus.ker = ⊤ := by
    apply IdeleDensity.eq_top_of_isClosed modulus.ker ∅ hclosed
    · intro a
      change ‖(χ.onIdeles (diagonalUnits F a) : ℂ)‖ = 1
      simp
    · intro v _ a
      exact local_norm v a
  refine ⟨χ, ?_, hχ⟩
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  have ha : a ∈ modulus.ker := htop.symm ▸ Subgroup.mem_top a
  exact ha

set_option maxHeartbeats 2400000 in
/-- **Local distribution nonvanishing.** Let `P` be an irreducible closed invariant summand of
the cuspidal spectrum, realized by `R` and `Φ`, and let `D` be a spectral presentation of `R`
whose component at `v` is irreducible and admissible. If the compression to `P` of the
operator of `g ↦ φ(g_v) · f^v(g)`, with `f^v` invariant at `v`, is trace class with nonzero
trace, then the character of the local component at `v` does not vanish at `φ`. -/
theorem exists_distribution_ne_zero_of_compressedTrace
    (P : Submodule ℂ S) [CompleteSpace P]
    (hPinv : ∀ a, ∀ x ∈ P, πc a x ∈ P)
    (hPirr : ∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
      (∀ a, ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P)
    (R : CuspidalOperatorRealization F r) (Φ : R.Space →ₗ[ℂ] S)
    (hΦ : ∀ f, IsGeneralLinearFormClass F r T i (Φ f) (R.realization.toContinuous f))
    (hP : LinearMap.range Φ ≤ P)
    (D : CuspidalSpectralPresentation.{u, uQ} R) (v : Langlands.Global.FinitePlace F)
    (hI : (D.localComponent v).IsIrreducible) (hA : (D.localComponent v).IsAdmissible)
    [MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion F))]
    [BorelSpace (GeneralLinear (r + 1) (v.adicCompletion F))]
    [T2Space (GeneralLinear (r + 1) (v.adicCompletion F))]
    [LocallyCompactSpace (GeneralLinear (r + 1) (v.adicCompletion F))]
    [TotallyDisconnectedSpace (GeneralLinear (r + 1) (v.adicCompletion F))]
    (φ : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion F)))
    (fw : AdelicGroupPoints F G → ℂ) (hfw : ∀ g x, fw (g * ofPlace F G (.inr v) x) = fw g)
    (hf : Integrable (fun g => φ (localGLHomeomorph F (r + 1) (.inr v)
      (atPlace F G (.inr v) g)) * fw g) (Measure.haar : Measure (AdelicGroupPoints F G)))
    (htc : IsTraceClass (E := (P : Submodule ℂ S)) (P.orthogonalProjectionOnto ∘L
      fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc Measure.haar _ hf ∘L
        P.subtypeL : P →L[ℂ] P))
    (hne : operatorTrace (E := (P : Submodule ℂ S)) (P.orthogonalProjectionOnto ∘L
      fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc Measure.haar _ hf ∘L
        P.subtypeL : P →L[ℂ] P) ≠ 0) :
    ∃ (μF : Measure (GeneralLinear (r + 1) (v.adicCompletion F))) (_ : μF.IsHaarMeasure),
      Character.distribution μF (D.localComponent v).representation hA φ ≠ 0 := by
  let A := D.localComponent v
  let a : PlaceGroupPoints F G (.inr v) ≃ₜ* GeneralLinear (r + 1) (v.adicCompletion F) :=
    localGLHomeomorph F (r + 1) (.inr v)
  let τ := localRealizationPlaceRepresentation A
  let : MeasurableSpace (PlaceGroupPoints F G (.inr v)) := borel _
  have : BorelSpace (PlaceGroupPoints F G (.inr v)) := ⟨rfl⟩
  have : LocallyCompactSpace (PlaceGroupPoints F G (.inr v)) :=
    a.toHomeomorph.locallyCompactSpace_iff.mpr inferInstance
  have : TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v)) :=
    a.toHomeomorph.symm.totallyDisconnectedSpace
  have : T2Space (PlaceGroupPoints F G (.inr v)) := a.toHomeomorph.isEmbedding.t2Space
  have hτI : τ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff A.representation a).2 hI
  have hτA : IsAdmissible τ := (isAdmissible_comp_continuousMulEquiv_iff A.representation a).2 hA
  obtain ⟨j, hj, hjP, hjE⟩ :=
    presentedLocalComponentHilbertOccurrence F r hPD T i hi I e hc P R Φ hΦ hP D v hI
  let μv : Measure (PlaceGroupPoints F G (.inr v)) := Measure.haar
  obtain ⟨-, ⟨C, hC⟩, -⟩ := IsotypicTrace.cuspidalIsotypicTraceFactorization_of_occurrence F G v
    hPD hG T i hi I e hc μv Measure.haar P hPinv hPirr τ hτA hτI j hj hjP hjE
  let fv : SchwartzBruhat (PlaceGroupPoints F G (.inr v)) :=
    Hecke.TestFunction.pullback a.toHomeomorph φ
  have htr : operatorTrace (E := (P : Submodule ℂ S)) (P.orthogonalProjectionOnto ∘L
      fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc Measure.haar _ hf ∘L
        P.subtypeL : P →L[ℂ] P) = Character.distribution μv τ hτA fv * C fw :=
    hC fv fw hfw hf htc
  have hdist : Character.distribution μv τ hτA fv ≠ 0 := fun h0 =>
    hne (by rw [htr, h0, zero_mul])
  have htransport := BaseChange.distribution_comp_equiv a μv A.representation hA hτA fv
  have hback : Hecke.TestFunction.pullback a.symm.toHomeomorph fv = φ := by
    ext x
    change φ (a (a.symm x)) = φ x
    rw [a.apply_symm_apply]
  rw [hback] at htransport
  exact ⟨μv.map a, a.isHaarMeasure_map μv, htransport ▸ hdist⟩

end Langlands.TraceFormula.GlobalizationIdentification
