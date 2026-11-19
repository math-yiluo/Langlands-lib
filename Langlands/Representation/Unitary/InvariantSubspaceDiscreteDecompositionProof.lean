import Langlands.Representation.Unitary.InvariantSubspaceDiscreteDecompositionStatement
import Langlands.Representation.Unitary.RightHaarHermitianApproximationProof
import Langlands.Representation.Unitary.CompactApproximationOrthogonalProof
import Langlands.Representation.Unitary.CompactApproximationMultiplicityProof
import Langlands.Analysis.Local.HaarInversionDensityProof
import Langlands.Analysis.Local.ModularCharacterContinuity

noncomputable section

universe uG uE

namespace Langlands.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped CompactlySupported ENNReal NNReal Topology

section SubspaceTransport

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (V : Submodule ℂ E)

/-- A subspace of `V` is isometric to its image in the ambient space. -/
def invariantSubspaceMapEquiv (P : Submodule ℂ V) : P ≃ₗᵢ[ℂ] (P.map V.subtype) :=
  { Submodule.equivMapOfInjective V.subtype Subtype.val_injective P with
    norm_map' := fun _ => rfl }

theorem invariantSubspaceMapEquiv_apply (P : Submodule ℂ V) (x : P) :
    ((invariantSubspaceMapEquiv V P x : P.map V.subtype) : E) = ((x : V) : E) := rfl

theorem invariantSubspaceMapEquiv_symm_apply (P : Submodule ℂ V) (y : P.map V.subtype) :
    (((invariantSubspaceMapEquiv V P).symm y : P) : V).1 = (y : E) := by
  have h := invariantSubspaceMapEquiv_apply V P ((invariantSubspaceMapEquiv V P).symm y)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

end SubspaceTransport

/-- Discrete decomposition of a closed invariant subspace with compact
convolution restrictions. -/
theorem invariantSubspaceDiscreteDecomposition :
    InvariantSubspaceDiscreteDecompositionStatement.{uG, uE} := by
  intro G _ _ _ _ _ _ _ _ E _ _ _ μ _ π hπinner hπcont hπnorm hπmeas V hVc hVi hcompact
  -- Hermitian approximate identities for the right Haar measure.
  obtain ⟨f, hf, hfprop, -, hA⟩ := rightHaarHermitianApproximation μ π hπinner hπcont
  obtain ⟨hsymm, htend, hpresAll⟩ := hA
  have hπmeasinv : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ.inv :=
    fun x => (hπcont x).stronglyMeasurable.aestronglyMeasurable
  set T : ℕ → (E →L[ℂ] E) := fun n =>
    integratedIsometricAction μ.inv π hπnorm hπmeasinv
      (fun g => (f n g : ℂ)) (hf n).ofReal with hTdef
  -- Each approximant is a left-Haar integrated operator of a compact weight.
  have hΔc : Continuous (fun g : G => ((modularCharacter g : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp Langlands.Haar.continuous_modularCharacter_of_locallyCompact
  have hinv : μ.inv = μ.withDensity (fun g => (modularCharacter g : ℝ≥0∞)) :=
    (Langlands.Haar.haarInversionDensity G μ).1
  let Fw : ℕ → C_c(G, ℂ) := fun n =>
    { toFun := fun g => (((modularCharacter g : ℝ≥0) : ℝ) : ℂ) * (f n g : ℂ)
      continuous_toFun :=
        (Complex.continuous_ofReal.comp hΔc).mul
          (Complex.continuous_ofReal.comp (hfprop n).1)
      hasCompactSupport' :=
        ((hfprop n).2.1.comp_left Complex.ofReal_zero).mul_left }
  have hFint : ∀ n, Integrable (Fw n) μ := fun n =>
    (Fw n).continuous.integrable_of_hasCompactSupport (Fw n).hasCompactSupport
  have hTeq : ∀ n, T n = integratedIsometricAction μ π hπnorm hπmeas (Fw n) (hFint n) := by
    intro n
    ext1 φ
    rw [hTdef]
    simp only [integratedIsometricAction_apply]
    rw [hinv, integral_withDensity_eq_integral_smul
      Langlands.Haar.continuous_modularCharacter_of_locallyCompact.measurable]
    congr 1
    funext g
    change ((modularCharacter g : ℝ≥0) : ℝ) • ((f n g : ℂ) • π g φ) =
      ((((modularCharacter g : ℝ≥0) : ℝ) : ℂ) * (f n g : ℂ)) • π g φ
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    rfl
  have hTV : ∀ n, ∀ x ∈ V, T n x ∈ V := (hpresAll V hVc hVi).choose
  -- The restricted representation and operators.
  have hVcomplete : CompleteSpace V := hVc.isComplete.completeSpace_coe
  let π' : G →* (V →L[ℂ] V) :=
    { toFun := fun g => ((π g).comp V.subtypeL).codRestrict V (fun x => hVi g x x.2)
      map_one' := by
        apply ContinuousLinearMap.ext
        intro x
        apply Subtype.ext
        simp
      map_mul' := by
        intro g h
        apply ContinuousLinearMap.ext
        intro x
        apply Subtype.ext
        change π (g * h) (x : E) = π g (π h x)
        rw [map_mul]
        rfl }
  have hπ' : ∀ g (x : V), ((π' g x : V) : E) = π g x := fun _ _ => rfl
  let T' : ℕ → (V →L[ℂ] V) := fun n =>
    ((T n).comp V.subtypeL).codRestrict V (fun x => hTV n x x.2)
  have hT' : ∀ n (x : V), ((T' n x : V) : E) = T n x := fun _ _ => rfl
  have hπ'inner : ∀ g (x y : V), inner ℂ (π' g x) (π' g y) = inner ℂ x y := by
    intro g x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hπ', hπ', hπinner]
  have hT'comp : ∀ n, IsCompactOperator (T' n) := by
    intro n
    have h := hcompact (Fw n) (hFint n)
    rw [← hTeq n] at h
    exact h.codRestrict (fun x => hTV n x x.2) hVc
  have hT'symm : ∀ n, (T' n).IsSymmetric := by
    intro n x y
    change inner ℂ (T' n x) y = inner ℂ x (T' n y)
    rw [Submodule.coe_inner, Submodule.coe_inner, hT', hT']
    exact (hsymm n).1 x y
  have hT'lim : ∀ x : V, Tendsto (fun n => T' n x) atTop (𝓝 x) := by
    intro x
    rw [tendsto_subtype_rng]
    exact htend x
  -- Closed invariant subspaces of `V` and their images.
  have hmapClosed : ∀ S : Submodule ℂ V, IsClosed (S : Set V) →
      IsClosed ((S.map V.subtype : Submodule ℂ E) : Set E) := by
    intro S hS
    have := (V.isClosedEmbedding_subtypeL hVc).isClosedMap _ hS
    simpa [Submodule.map_coe] using this
  have hmapInv : ∀ S : Submodule ℂ V, (∀ (g : G), ∀ x ∈ S, π' g x ∈ S) →
      ∀ (g : G), ∀ x ∈ S.map V.subtype, π g x ∈ S.map V.subtype := by
    intro S hS g x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨π' g y, hS g y hy, rfl⟩
  have hT'pres : ∀ (n : ℕ) (S : Submodule ℂ V), IsClosed (S : Set V) →
      (∀ (g : G), ∀ x ∈ S, π' g x ∈ S) → ∀ x ∈ S, T' n x ∈ S := by
    intro n S hSc hSi x hx
    have hmem : T n x ∈ S.map V.subtype :=
      (hpresAll _ (hmapClosed S hSc) (hmapInv S hSi)).choose n x ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = T' n x := Subtype.ext hyx
    rw [← this]
    exact hy
  -- Intertwiners transfer between `V` and the ambient space.
  have hT'inter : ∀ (P Q : Submodule ℂ V) (hPc : IsClosed (P : Set V))
      (hPi : ∀ (g : G), ∀ x ∈ P, π' g x ∈ P) (U : P ≃ₗᵢ[ℂ] Q),
      (∀ (g : G) (x : P), (U ⟨π' g x, hPi g x x.2⟩ : V) = π' g (U x)) →
      ∀ (n : ℕ) (x : P), (U ⟨T' n x, hT'pres n P hPc hPi x x.2⟩ : V) = T' n (U x) := by
    intro P Q hPc hPi U hU n x
    let eP := invariantSubspaceMapEquiv V P
    let eQ := invariantSubspaceMapEquiv V Q
    let W : P.map V.subtype ≃ₗᵢ[ℂ] Q.map V.subtype := eP.symm.trans (U.trans eQ)
    have hW : ∀ y : P.map V.subtype, (W y : E) = ((U (eP.symm y) : V) : E) := fun y =>
      invariantSubspaceMapEquiv_apply V Q (U (eP.symm y))
    have hPiE := hmapInv P hPi
    have hWπ : ∀ (g : G) (y : P.map V.subtype),
        (W ⟨π g y, hPiE g y y.2⟩ : E) = π g (W y) := by
      intro g y
      have hsymm' : eP.symm ⟨π g y, hPiE g y y.2⟩ =
          ⟨π' g (eP.symm y), hPi g _ (eP.symm y).2⟩ := by
        apply eP.injective
        rw [LinearIsometryEquiv.apply_symm_apply]
        apply Subtype.ext
        rw [invariantSubspaceMapEquiv_apply]
        change π g (y : E) = π g (((eP.symm y : P) : V) : E)
        rw [invariantSubspaceMapEquiv_symm_apply]
      rw [hW, hsymm', hU, hπ', hW]
    obtain ⟨hAP, hAPU⟩ := hpresAll _ (hmapClosed P hPc) hPiE
    have key := hAPU (Q.map V.subtype) W hWπ n (eP x)
    have hsymmT : eP.symm ⟨T n (eP x), hAP n (eP x) (eP x).2⟩ =
        ⟨T' n x, hT'pres n P hPc hPi x x.2⟩ := by
      apply eP.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      apply Subtype.ext
      rfl
    rw [hW, hsymmT, hW, LinearIsometryEquiv.symm_apply_apply] at key
    apply Subtype.ext
    rw [hT']
    exact key
  -- Decompose `V`.
  obtain ⟨A', hgood', hpair', htotal'⟩ :=
    compactApproximationOrthogonal G V π' hπ'inner T' hT'comp hT'symm hT'lim hT'pres
      ⊤ isClosed_univ (fun _ _ _ => Submodule.mem_top)
  let A : Set (Submodule ℂ E) := (fun P => P.map V.subtype) '' A'
  have hmapInj : Function.Injective (fun P : Submodule ℂ V => P.map V.subtype) :=
    Submodule.map_injective_of_injective Subtype.val_injective
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨P, hP, rfl⟩
    obtain ⟨-, hP0, hPc, hPi, hPirr⟩ := hgood' P hP
    refine ⟨Submodule.map_subtype_le V P, ?_, hmapClosed P hPc, hmapInv P hPi, ?_⟩
    · intro h
      apply hP0
      apply hmapInj
      simpa using h
    · intro Q hQ hQc hQi
      have hQV : Q ≤ V := hQ.trans (Submodule.map_subtype_le V P)
      have hQ'c : IsClosed ((Q.comap V.subtype : Submodule ℂ V) : Set V) :=
        hQc.preimage continuous_subtype_val
      have hQ'i : ∀ (g : G), ∀ x ∈ Q.comap V.subtype, π' g x ∈ Q.comap V.subtype :=
        fun g x hx => hQi g x hx
      have hQ'le : Q.comap V.subtype ≤ P := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := hQ hx
        have : y = x := Subtype.ext hyx
        rw [← this]
        exact hy
      have hQmap : (Q.comap V.subtype).map V.subtype = Q := by
        rw [Submodule.map_comap_subtype]
        exact inf_eq_right.2 hQV
      rcases hPirr _ hQ'le hQ'c hQ'i with h | h
      · left
        rw [← hQmap, h, Submodule.map_bot]
      · right
        rw [← hQmap, h]
  · rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ hne
    have hPQ : P ≠ Q := fun h => hne (by rw [h])
    have horth : P ⟂ Q := hpair' hP hQ hPQ
    show P.map V.subtype ⟂ Q.map V.subtype
    rw [Submodule.isOrtho_iff_inner_eq] at horth ⊢
    rintro _ ⟨x', hx', rfl⟩ _ ⟨y', hy', rfl⟩
    have := horth x' hx' y' hy'
    rwa [Submodule.coe_inner] at this
  · apply le_antisymm
    · apply Submodule.topologicalClosure_minimal _ _ hVc
      apply sSup_le
      rintro _ ⟨P, -, rfl⟩
      exact Submodule.map_subtype_le V P
    · intro v hv
      have hle : sSup A' ≤ (sSup A).comap V.subtype := by
        apply sSup_le
        intro P hP x hx
        exact (le_sSup (show P.map V.subtype ∈ A from ⟨P, hP, rfl⟩))
          (Submodule.mem_map_of_mem hx)
      have hmemV : (⟨v, hv⟩ : V) ∈ (sSup A').topologicalClosure := by
        rw [htotal']
        exact Submodule.mem_top
      have hcl : (⟨v, hv⟩ : V) ∈ closure ((sSup A' : Submodule ℂ V) : Set V) := hmemV
      have himg := map_mem_closure (t := ((sSup A : Submodule ℂ E) : Set E))
        continuous_subtype_val hcl (fun x hx => hle hx)
      exact himg
  · rintro _ ⟨P, hP, rfl⟩ hPi
    obtain ⟨-, -, hPc, hPi', -⟩ := hgood' P hP
    have hfin := compactApproximationMultiplicity G V π' hπ'inner T' hT'comp hT'symm hT'lim
      hT'pres hT'inter A' (fun Q hQ => ⟨(hgood' Q hQ).2.1, (hgood' Q hQ).2.2.1,
        (hgood' Q hQ).2.2.2.1⟩) hpair' P hP
    apply (hfin.image (fun P => P.map V.subtype)).subset
    rintro _ ⟨⟨Q, hQ, rfl⟩, U, hU⟩
    refine ⟨Q, ⟨hQ, ?_⟩, rfl⟩
    let eP := invariantSubspaceMapEquiv V P
    let eQ := invariantSubspaceMapEquiv V Q
    refine ⟨eP.trans (U.trans eQ.symm), ?_⟩
    intro g x
    apply Subtype.ext
    rw [hπ']
    simp only [LinearIsometryEquiv.trans_apply]
    rw [invariantSubspaceMapEquiv_symm_apply, invariantSubspaceMapEquiv_symm_apply]
    have hx : eP ⟨π' g x, hPi' g x x.2⟩ = ⟨π g (eP x), hPi g (eP x) (eP x).2⟩ :=
      Subtype.ext rfl
    rw [hx, hU]

end Langlands.Analysis
