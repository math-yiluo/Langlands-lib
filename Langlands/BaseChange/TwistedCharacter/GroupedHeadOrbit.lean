import Langlands.BaseChange.TwistedCharacter.EssentiallyTemperedDatum
import Langlands.BaseChange.TwistedCharacter.StandardTraceComparison
import Langlands.BaseChange.TwistedCharacter.InducedTraceTransport
import Langlands.BaseChange.TwistedCharacter.StandardTraceMembership
import Langlands.BaseChange.TwistedPseudoCoefficientOrbitNoninduction
import Langlands.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.Representation.Smooth.SmallRealizationProof

/-! # Heads of grouped standard data lie outside the orbit of a σ-discrete series -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory GeneralLinear HarmonicAnalysis MeasureTheory PadicField.TopologicalData

universe u v w

theorem determinant_reindex_symm_eq {E : Type v} [Field E] {m n : ℕ} (e : Fin m ≃ Fin n)
    (g : GeneralLinear n E) :
    determinant ((GeneralLinear.reindex (R := E) e).symm g) = determinant g := by
  apply Units.ext
  change (g.val.submatrix e e).det = g.val.det
  exact Matrix.det_submatrix_equiv_self e g.val

section Padic

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The standard module of a one-block datum whose unitary specializations match a flat block
family is the normalized induction of the flat blocks twisted by the common exponent. -/
theorem nonempty_standardModule_equiv_of_singleBlock {n : ℕ} (L : BlockShape n)
    (δ : letI := T.topology; ∀ k, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (L.size k) E.Carrier))
    (t : T.TemperedLanglandsDatum.{max v w} n) (h1 : t.shape.length = 1)
    (q : Fin L.length → Fin t.shape.length)
    (hunit : ∀ z : Fin t.shape.length → ℂˣ, (∀ j, ‖(z j : ℂ)‖ = 1) →
      letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      letI := T.generalLinearTopologicalGroup n
      Nonempty ((T.normalizedProductInduced L (fun k =>
          twist (determinantUnramified E.Carrier (L.size k) (z (q k))) (δ k).representation)).Equiv
        (T.normalizedProductInduced t.shape (fun j =>
          twist (determinantUnramified E.Carrier (t.shape.size j) (z j))
            (t.blocks j).representation)))) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Nonempty (t.standardModule.representation.Equiv
      (T.normalizedProductInduced L (fun k =>
        twist (T.determinantPowerCharacter (L.size k) (t.exponent ⟨0, by omega⟩))
          (δ k).representation))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  let i0 : Fin t.shape.length := ⟨0, by omega⟩
  let s := t.exponent i0
  have e1 := (hunit (fun _ => 1) (fun _ => by simp)).some
  have hone (m : ℕ) {V : Type (max v w)} [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear m E.Carrier) V) :
      twist (determinantUnramified E.Carrier m 1) ρ = ρ := by
    rw [determinantUnramified_one T m, twist_one]
  let eL := T.normalizedProductInducedEquiv L (σ := fun k => (δ k).representation)
    (τ := fun k => twist (determinantUnramified E.Carrier (L.size k) 1) (δ k).representation)
    (fun k => equivOfRepresentationEq (hone _ _).symm)
  let eT := T.normalizedProductInducedEquiv t.shape
    (σ := fun j => twist (determinantUnramified E.Carrier (t.shape.size j) 1)
      (t.blocks j).representation)
    (τ := fun j => (t.blocks j).representation)
    (fun j => equivOfRepresentationEq (hone _ _))
  let e2 := eL.trans (e1.trans eT)
  let r := (GeneralLinear.reindex (R := E.Carrier)
    (finCongr (t.shape.singleBlock_size h1 i0))).symm.toMonoidHom
  let e3 := T.singleBlockNormalizedProductEquiv t.shape h1 (fun j => (t.blocks j).representation)
    (fun j => (t.blocks j).isSmooth) i0
  let e4 := T.singleBlockNormalizedProductEquiv t.shape h1
    (fun j => (T.twistedBlocks t.shape t.blocks t.exponent j).representation)
    (fun j => (T.twistedBlocks t.shape t.blocks t.exponent j).isSmooth) i0
  have hdet : (T.determinantPowerCharacter (t.shape.size i0) s).comp r =
      T.determinantPowerCharacter n s := by
    apply MonoidHom.ext
    intro g
    change realPowerCharacter (T.normalizedAbsUnits.comp determinant) s (r g) =
      realPowerCharacter (T.normalizedAbsUnits.comp determinant) s g
    change (realPowerCharacter T.normalizedAbsUnits s) (determinant (r g)) =
      (realPowerCharacter T.normalizedAbsUnits s) (determinant g)
    exact congrArg (realPowerCharacter T.normalizedAbsUnits s)
      (determinant_reindex_symm_eq (finCongr (t.shape.singleBlock_size h1 i0)) g)
  have hcomp : ((T.twistedBlocks t.shape t.blocks t.exponent i0).representation).comp r =
      twist (T.determinantPowerCharacter n s) ((t.blocks i0).representation.comp r) := by
    change (twist (T.determinantPowerCharacter (t.shape.size i0) s)
      (t.blocks i0).representation).comp r = _
    rw [← hdet]
    rfl
  let χ : Induction.SmoothCharacter ℂ E.Carrierˣ :=
    ⟨realPowerCharacter T.normalizedAbsUnits s,
      isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits s⟩
  let e5 := T.normalizedProductDeterminantTwistEquiv L χ (fun k => (δ k).representation)
  exact ⟨((e4.trans (equivOfRepresentationEq hcomp)).trans
    (twistEquiv _ (e3.symm.trans e2.symm))).trans e5⟩

variable (hModule : letI := T.topology; IsModuleTopology F E.Carrier)
  (σ : E.Carrier ≃ₐ[F] E.Carrier)

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency.types false in
include hModule in
/-- The Langlands head of the datum grouping a flat family of irreducible tempered σ-stable
blocks on at least two blocks lies outside the invariant unramified orbit of a σ-discrete
series. With several groups the head is not essentially tempered; with a single group it is a
proper σ-stable induction. -/
theorem not_isUnramifiedTwistOf_groupedHead {n : ℕ} (hn : 0 < n) (L : BlockShape n)
    (hL : 2 ≤ L.length)
    (δ : letI := T.topology; ∀ k, SmoothRep.{0,v,max v w} ℂ (GeneralLinear (L.size k) E.Carrier))
    (hirr : letI := T.topology; ∀ k, (δ k).representation.IsIrreducible)
    (htemp : letI := T.topology; ∀ k, T.IsTempered (δ k).representation)
    (A : letI := T.topology; ∀ k, SigmaIntertwiner σ (L.size k) (δ k).representation)
    (t : T.TemperedLanglandsDatum.{max v w} n) (q : Fin L.length → Fin t.shape.length)
    (hunit : ∀ z : Fin t.shape.length → ℂˣ, (∀ j, ‖(z j : ℂ)‖ = 1) →
      letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      letI := T.generalLinearTopologicalGroup n
      Nonempty ((T.normalizedProductInduced L (fun k =>
          twist (determinantUnramified E.Carrier (L.size k) (z (q k))) (δ k).representation)).Equiv
        (T.normalizedProductInduced t.shape (fun j =>
          twist (determinantUnramified E.Carrier (t.shape.size j) (z j))
            (t.blocks j).representation))))
    (π : letI := T.topology; SmoothRep.{0,v,max v w} ℂ (GeneralLinear n E.Carrier))
    (hπ : t.IsLanglandsHead π)
    {W : Type w} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GeneralLinear n E.Carrier) W)
    (hτ : letI := T.topology; letI := T.valuativeRel; letI := T.localField;
      IsSigmaDiscreteSeries σ n τ) :
    letI := T.topology
    ¬ IsUnramifiedTwistOf (entrywiseAut σ n) τ π.representation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  let := T.generalLinearTopologicalGroup n
  rintro ⟨ψ, hψ, hψθ, ⟨e⟩⟩
  by_cases h1 : t.shape.length = 1
  · obtain ⟨hπirr, qπ, hqπ, -⟩ := hπ
    have hMirr := (singleBlockStandard_irreducible_essentiallyTempered T hModule σ t h1).1
    have hinj : Function.Injective qπ := by
      let := hMirr
      rcases Representation.IsIrreducible.injective_or_eq_zero qπ with h | h
      · exact h
      · exfalso
        let := hπirr
        let : Nontrivial π := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n E.Carrier))
          π.representation.asModule
        obtain ⟨w', hw'⟩ := exists_ne (0 : π)
        obtain ⟨v', rfl⟩ := hqπ w'
        exact hw' (by rw [h]; rfl)
    let eMπ : t.standardModule.representation.Equiv π.representation :=
      Representation.Equiv.mk (LinearEquiv.ofBijective qπ.toLinearMap ⟨hinj, hqπ⟩)
        (fun g => qπ.isIntertwining' g)
    obtain ⟨eMW⟩ := nonempty_standardModule_equiv_of_singleBlock T L δ t h1 q hunit
    let s := t.exponent ⟨0, by omega⟩
    let R (k : Fin L.length) := twist (T.determinantPowerCharacter (L.size k) s) (δ k).representation
    have hR (k : Fin L.length) : IsAdmissible (R k) :=
      (isAdmissible_twist_iff _ _ (T.isOpen_ker_determinantPowerCharacter _ s)).mpr
        (htemp k).isAdmissible
    let (k : Fin L.length) : (R k).IsIrreducible := (isIrreducible_twist_iff _ _).mpr (hirr k)
    let κ := T.leviHalfModulus L
    let Ξ := twist κ (L.blockTensor R)
    have hΞadm : IsAdmissible Ξ :=
      (isAdmissible_twist_iff κ _ (T.isOpen_ker_leviHalfModulus L)).mpr
        (FiniteTensor.isAdmissible_external R hR)
    have hΞirr : Ξ.IsIrreducible := (isIrreducible_twist_iff κ _).mpr
      (FiniteTensor.isIrreducible_external R
        (fun k f => (admissibleSchur_scalarEndomorphism _ (hR k) inferInstance f).exists))
    let (k : Fin L.length) : SecondCountableTopology (GeneralLinear (L.size k) E.Carrier) :=
      T.generalLinearSecondCountableTopology _
    let (k : Fin L.length) : IsTopologicalGroup (GeneralLinear (L.size k) E.Carrier) :=
      T.generalLinearTopologicalGroup _
    let : SecondCountableTopology (L.Levi E.Carrier) := inferInstanceAs
      (SecondCountableTopology (∀ k : Fin L.length, GeneralLinear (L.size k) E.Carrier))
    obtain ⟨Rz, -, ⟨eR⟩⟩ := exists_irreducible_smoothRep_equiv_of_separable.{v, max v w, w}
      (SmoothRep.of Ξ hΞadm.1) hΞirr
    let AR (k : Fin L.length) : SigmaIntertwiner σ (L.size k) (R k) :=
      twistTwistedIntertwiner (entrywiseAut σ (L.size k))
        (T.determinantPowerCharacter (L.size k) s)
        (determinantPowerCharacter_entrywiseAut T hModule σ _ _) (A k)
    let AΞ := twistTwistedIntertwiner (leviAut σ L) κ (leviHalfModulus_leviAut_padic T hModule σ L)
      (leviTensorIntertwiner σ L AR)
    have hRzσ : IsLeviSigmaStable σ L Rz.representation :=
      ⟨leviIntertwinerTransport σ L AΞ eR⟩
    let eP : Representation.Equiv (Ξ.comp (L.leviProjection E.Carrier))
        (Rz.representation.comp (L.leviProjection E.Carrier)) :=
      Representation.Equiv.mk eR.toLinearEquiv
        (fun x => eR.toIntertwiningMap.isIntertwining' (L.leviProjection E.Carrier x))
    let eI := Induction.smoothInducedEquiv (L.parabolic E.Carrier) eP
    have hne := sigmaDiscreteOrbitNoninduction σ τ hτ W (twist ψ τ)
      ⟨ψ, hψ, hψθ, ⟨Representation.Equiv.refl _⟩⟩ L hL Rz Rz.representation Rz.isSmooth hRzσ
    exact hne.false ((e.symm.trans (eMπ.symm.trans eMW)).trans eI)
  · have htτ : T.IsTempered τ := (isTemperedRep_iff_isTempered T τ).mp hτ.2.2.1
    have e' : (twist ψ⁻¹ π.representation).Equiv τ :=
      (twistEquiv ψ⁻¹ e).trans (equivOfRepresentationEq (twist_inv_twist ψ τ))
    have hψτ : T.IsTempered (twist ψ⁻¹ π.representation) :=
      (T.isTempered_iff_of_equiv e').mpr htτ
    exact h1 (shape_length_eq_one_of_twist_tempered.{v,w} T hn t π hπ.isLanglandsQuotient ψ⁻¹
      hψ.inv hψτ)

end Padic

end Langlands.BaseChange
