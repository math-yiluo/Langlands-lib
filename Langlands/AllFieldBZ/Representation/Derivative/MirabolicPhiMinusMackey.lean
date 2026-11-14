import Langlands.AllFieldBZ.Representation.Derivative.MirabolicMinusExactnessProof
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicPlus
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductRestrictionMackey
import Langlands.Representation.Derivative.MirabolicPhiMinusMackey

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicPhiMinusMackey`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicPhiMinusMackey` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding MinusExactnessStatement character_dotProduct_eq_one character_mul_eq_one coe_latticeBox coordinateCharacter coordinateCharacter_apply coordinateCharacter_eq_of_sub_mem coordinateCharacter_eq_one coordinateCharacter_zero eq_zero_of_forall_characterAverage_eq_zero exists_exact_phiMinusUnnormalized_compactInduction exists_exact_plusPhiLocalization exists_forall_characterAverage_eq_zero exists_latticeBox_subset exists_mem_latticeBox exists_ne_zero_mem_additiveLattice finite_latticeBox_quotient inv_mem_additiveLattice_of_notMem isCompact_latticeBox isCompact_radicalBox isOpen_ker_coordinateCharacter isOpen_ker_phiMinusCharacter isOpen_ker_psiMinusCharacter isOpen_ker_thetaPlus isOpen_latticeBox ker_psiMinusQuotient latticeBox latticeBox_mono levi_inv_mem_relations mem_latticeBox mem_latticeBox_of_forall_character_eq_one mem_radicalBox minusExactness phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient plusPhiLocalizationEquiv plusPhiLocalizationIso plusPhiLocalization_exact plusTwistFunctor psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient psiPlusUnnormalized radicalBox radicalBox_mono radical_isLimitOfCompactSubgroups subsingleton_of_psiMinus_phiMinus
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV uR uG uC vC

/-! ## Transport of pointwise short exactness along isomorphisms -/

section Exact
variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C]

end Exact
/-! ## The radical of the plus subgroup -/

section Kernel
variable (t : ℕ) (R : Type uR) [CommRing R]

variable {t R}

section Topology
variable [TopologicalSpace R]

end Topology
end Kernel
section Character
variable {R : Type uR} [CommRing R] [TopologicalSpace R] (ψ : UnitaryAdditiveCharacter R) (t : ℕ)

end Character
/-! ## Comparison with `Φ⁻` and exactness -/

section Padic
variable {F : LocalFieldPackage.{uF}}

/-- Restricting to `Q` and localizing gives the actual unnormalized `Φ⁻` carrier: the
two relation spans agree through `plusKernelEquiv`, classes go to classes. -/
def plusPhiLocalizationEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (t + 1) F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      ((SmoothRep.toRep ⋙ Rep.resFunctor (plusSubgroup t F.Carrier).subtype ⋙
        plusPhiLocalization ψ t).obj A).ρ
      ((phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep).obj A).ρ :=
  letI := T.topology
  Representation.Equiv.mk
    (Jacquet.Localization.transportEquiv (A.representation.comp (plusSubgroup t F.Carrier).subtype)
      A.representation (plusKernel t F.Carrier) (radical (t + 1) F.Carrier)
      (plusKernelTheta ψ t) (T.mirabolicTheta ψ t) plusKernelEquiv (LinearEquiv.refl ℂ A)
      (fun _ _ => rfl) (fun _ => rfl))
    (fun _ => LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun _ => rfl)

/-- Unnormalized `Φ⁻` factors naturally through restriction to `Q`. -/
def plusPhiLocalizationIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ) :
    letI := T.topology
    SmoothRep.toRep ⋙ Rep.resFunctor (plusSubgroup t F.Carrier).subtype ⋙
        plusPhiLocalization.{uV, uF} ψ t ≅
      phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep :=
  letI := T.topology
  NatIso.ofComponents (fun A => Rep.mkIso (plusPhiLocalizationEquiv T ψ t A)) (by
    intro A B f
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact Submodule.Quotient.induction_on _ x fun _ => rfl)

private theorem _root_.Langlands.Derivative.Mirabolic.isLocallyConstant_of_isOpen_ker {G : Type uG} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) :
    IsLocallyConstant (fun g => (χ g : ℂ)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun y : G => y * x⁻¹) ⁻¹' (χ.ker : Set G),
    hχ.preimage (continuous_id.mul continuous_const), ?_, ?_⟩
  · simp
  · intro y hy
    change χ (y * x⁻¹) = 1 at hy
    have heq : χ y = χ x := mul_inv_eq_one.mp (by
      simpa only [map_mul, map_inv] using hy)
    exact congrArg (fun z : ℂˣ => (z : ℂ)) heq

/-- The localization on `Q` preserves short exact sequences with smooth middle term. -/
theorem plusPhiLocalization_exact (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ)
    {A B C : Rep.{uV} ℂ (plusSubgroup t F.Carrier)} (i : A ⟶ B) (q : B ⟶ C)
    (hi : Function.Injective i.hom) (hq : Function.Surjective q.hom)
    (hex : LinearMap.range i.hom.toLinearMap = LinearMap.ker q.hom.toLinearMap)
    (hB : letI := T.topology; IsSmooth B.ρ) :
    letI := T.topology
    Function.Injective ((plusPhiLocalization ψ t).map i).hom ∧
      LinearMap.range ((plusPhiLocalization ψ t).map i).hom.toLinearMap =
        LinearMap.ker ((plusPhiLocalization ψ t).map q).hom.toLinearMap ∧
      Function.Surjective ((plusPhiLocalization ψ t).map q).hom := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (t + 1 + 1)
  have hU : Jacquet.Localization.IsLimitOfCompactSubgroups (plusKernel t F.Carrier) := by
    intro K hK
    obtain ⟨L, hL, hKL⟩ := radical_isLimitOfCompactSubgroups F T (t + 1)
      (plusKernelEquiv '' K) (hK.image continuous_plusKernelEquiv)
    refine ⟨L.map plusKernelEquiv.symm.toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_map]
      exact hL.image continuous_plusKernelEquiv_symm
    · intro c hc
      exact ⟨plusKernelEquiv c, hKL ⟨c, hc, rfl⟩, plusKernelEquiv.symm_apply_apply c⟩
  have hθ : IsLocallyConstant (fun u : plusKernel t F.Carrier => (plusKernelTheta ψ t u : ℂ)) :=
    (isLocallyConstant_of_isOpen_ker _ (T.mirabolicTheta_isOpen_ker ψ t)).comp_continuous
      continuous_plusKernelEquiv
  exact (Jacquet.Localization.characterLocalizationExactness
    (G := plusSubgroup t F.Carrier) (V := A) (W := B) (X := C)).2
      (plusKernel t F.Carrier) hU (plusKernelTheta ψ t) hθ (plusSuccessorRange t F.Carrier)
      (plusSuccessorRange_le_normalizer t F.Carrier) (plusKernelTheta_isInvariant ψ t)
      A.ρ B.ρ C.ρ i.hom q.hom hi hq hex hB

/-! ## The two-orbit sequence -/

set_option maxHeartbeats 800000 in
/-- Localizing the published two-step Mackey sequence of a compact induction
from a closed subgroup `H` of `P_(t+2)`, restricted to `Q`, with two ordered
orbits. -/
theorem exists_exact_plusPhiLocalization (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ)
    (H : Subgroup (mirabolic (t + 1) F.Carrier))
    (hH : letI := T.topology; IsClosed (H : Set (mirabolic (t + 1) F.Carrier)))
    (s : letI := T.topology; letI := T.generalLinearTopologicalGroup (t + 1 + 1)
      Geometric.OrderedDoubleCosets H (plusSubgroup t F.Carrier) 2) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (t + 1 + 1)
    ∃ (i : Geometric.orbitPiece.{0, uF, uV} (R := ℂ) H (plusSubgroup t F.Carrier)
          (s.representative 0) ⋙ plusPhiLocalization ψ t ⟶
        Geometric.restrictedCompactInduction H (plusSubgroup t F.Carrier) ⋙
          plusPhiLocalization ψ t)
      (q : Geometric.restrictedCompactInduction.{0, uF, uV} (R := ℂ) H
          (plusSubgroup t F.Carrier) ⋙ plusPhiLocalization ψ t ⟶
        Geometric.orbitPiece H (plusSubgroup t F.Carrier) (s.representative 1) ⋙
          plusPhiLocalization ψ t),
      ∀ X, Function.Injective (i.app X).hom ∧
        LinearMap.range (i.app X).hom.toLinearMap = LinearMap.ker (q.app X).hom.toLinearMap ∧
        Function.Surjective (q.app X).hom := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (t + 1 + 1)
  let := T.fieldT2
  let := T.generalLinearNonarchimedean (t + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1 + 1)
  let := T.generalLinearT2Space (t + 1 + 1)
  let := T.generalLinearSigmaCompactSpace (t + 1 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := t + 1) (F := F.Carrier)
  have : NonarchimedeanGroup (mirabolic (t + 1) F.Carrier) :=
    { is_nonarchimedean := fun U hU => by
        rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hU
        obtain ⟨V, hV, hVU⟩ := hU
        obtain ⟨L, hL⟩ := NonarchimedeanGroup.is_nonarchimedean V (by simpa using hV)
        exact ⟨OpenSubgroup.comap (mirabolic (t + 1) F.Carrier).subtype
          continuous_subtype_val L, fun x hx => hVU (hL hx)⟩ }
  have : SigmaCompactSpace (mirabolic (t + 1) F.Carrier) :=
    (GeneralLinear.Mirabolic.isClosed (n := t + 1) (F := F.Carrier)).sigmaCompactSpace
  have hQ : IsClosed (plusSubgroup t F.Carrier : Set (mirabolic (t + 1) F.Carrier)) :=
    plusSubgroup_isClosed
  have hM := Geometric.closedSubgroupMackeyFiltration.{uF, uV}
    (mirabolic (t + 1) F.Carrier) H (plusSubgroup t F.Carrier) hH hQ 2 s
  obtain ⟨e₀⟩ := hM 0
  obtain ⟨e₁⟩ := hM 1
  obtain ⟨i, q, h⟩ := RepFunctorFiltration.exists_exact_of_two _ e₀ e₁
  refine ⟨Functor.whiskerRight i (plusPhiLocalization ψ t),
    Functor.whiskerRight q (plusPhiLocalization ψ t), fun X => ?_⟩
  obtain ⟨hi, hex, hq⟩ := h X
  exact plusPhiLocalization_exact T ψ t (i.app X) (q.app X) hi hq hex
    (isSmooth_comp (plusSubgroup t F.Carrier).subtype continuous_subtype_val
      (Induction.compactInduced_smooth H X.obj.ρ))

set_option maxHeartbeats 800000 in
/-- The same sequence with the middle term written as unnormalized `Φ⁻` of the
compact induction. -/
theorem exists_exact_phiMinusUnnormalized_compactInduction (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ)
    (H : Subgroup (mirabolic (t + 1) F.Carrier))
    (hH : letI := T.topology; IsClosed (H : Set (mirabolic (t + 1) F.Carrier)))
    (s : letI := T.topology; letI := T.generalLinearTopologicalGroup (t + 1 + 1)
      Geometric.OrderedDoubleCosets H (plusSubgroup t F.Carrier) 2) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (t + 1 + 1)
    ∃ (i : Geometric.orbitPiece.{0, uF, uV} (R := ℂ) H (plusSubgroup t F.Carrier)
          (s.representative 0) ⋙ plusPhiLocalization ψ t ⟶
        (SmoothRep.toRep ⋙ Induction.compactInductionFunctor H) ⋙
          phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep)
      (q : (SmoothRep.toRep ⋙ Induction.compactInductionFunctor.{0, uF, uV} (R := ℂ) H) ⋙
          phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep ⟶
        Geometric.orbitPiece H (plusSubgroup t F.Carrier) (s.representative 1) ⋙
          plusPhiLocalization ψ t),
      ∀ X, Function.Injective (i.app X).hom ∧
        LinearMap.range (i.app X).hom.toLinearMap = LinearMap.ker (q.app X).hom.toLinearMap ∧
        Function.Surjective (q.app X).hom := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (t + 1 + 1)
  obtain ⟨i, q, h⟩ := exists_exact_plusPhiLocalization.{uF, uV} T ψ t H hH s
  let eB : Geometric.restrictedCompactInduction.{0, uF, uV} (R := ℂ) H
        (plusSubgroup t F.Carrier) ⋙ plusPhiLocalization ψ t ≅
      (SmoothRep.toRep ⋙ Induction.compactInductionFunctor.{0, uF, uV} (R := ℂ) H) ⋙
        phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep :=
    Functor.isoWhiskerLeft (SmoothRep.toRep ⋙ Induction.compactInductionFunctor H)
      (plusPhiLocalizationIso.{uF, max uF uV} T ψ t)
  refine ⟨(Iso.refl _).hom ≫ i ≫ eB.hom, eB.inv ≫ q ≫ (Iso.refl _).hom, ?_⟩
  exact exact_comp_isos i q (Iso.refl _) eB (Iso.refl _) h

end Padic
end Langlands.AllFieldBZ.Derivative.Mirabolic
