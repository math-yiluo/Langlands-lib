import Langlands.Representation.Classification.TadicComplementarySeriesOpenIntervalStatement
import Langlands.Representation.Classification.JuxtaposedSwapFromLibrary
import Langlands.Representation.Classification.ExponentFamily
import Langlands.Representation.Unitary.UnitarizabilityContinuationProof
import Langlands.Representation.Induction.CompactScalarProof
import Langlands.Representation.Tensor.UnitaryProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof

/-!
# Unitarity of the actual complementary family

The open-interval argument uses the published exponent-height family, its
compact integral pairing, irreducible factor swap, and unitarizability
continuation. The all-constituent endpoint argument is not yet included.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory MeasureTheory

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem complementaryProduct_eq {n : ℕ} (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (s : ℝ) :
    letI := T.topology
    complementaryProduct F T hn A s =
      (T.normalizedProductInductionFunctor (BlockShape.uniform 2 n hn)).obj
        ![T.segmentFactor A s, T.segmentFactor A (-s)] := by
  letI := T.topology
  unfold complementaryProduct PadicField.TopologicalData.twistedProductInduced
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem complementaryProduct_swap {n : ℕ} (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hA : letI := T.topology; A.IsIrreducible) (s : ℝ)
    (h : letI := T.topology
      (complementaryProduct F T hn A s).IsIrreducible) :
    letI := T.topology
    Nonempty (complementaryProduct F T hn A s ≅ complementaryProduct F T hn A (-s)) := by
  letI := T.topology
  have hfac (a : ℝ) : (T.segmentFactor A a).IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff _ _ A).mpr hA
  rw [complementaryProduct_eq F T hn] at h
  rw [complementaryProduct_eq F T hn, complementaryProduct_eq F T hn, neg_neg]
  exact JuxtaposedShuffle.uniform_two_swap_of_isIrreducible' hn _ _ (hfac s) (hfac (-s)) h

private theorem complementaryProduct_isAdmissible {n : ℕ} (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hA : letI := T.topology; IsAdmissible A.representation) (s : ℝ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (2 * n)
    IsAdmissible (complementaryProduct F T hn A s).representation := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (2 * n)
  let B := BlockShape.uniform 2 n hn
  have hf : ∀ i, IsAdmissible (T.twistedBlocks B (fun _ => A)
      (fun i => if (i : ℕ) = 0 then s else -s) i).representation := by
    intro i
    exact (isAdmissible_twist_iff _ _
      (T.isOpen_ker_determinantPowerCharacter _ _)).mpr hA
  exact Parabolic.normalizedInductionAdmissibility F T _ _ _
    (FiniteTensor.isAdmissible_external _ hf)

private theorem complementaryFamilyEquiv {n : ℕ} (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (2 * n)
    ∀ (K : OpenSubgroup (GeneralLinear (2 * n) F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear (2 * n) F.Carrier)))
      (hPK : ∀ g : GeneralLinear (2 * n) F.Carrier,
        ∃ (q : (BlockShape.uniform 2 n hn).parabolic F.Carrier) (x : K),
          g = (q : GeneralLinear (2 * n) F.Carrier) * (x : GeneralLinear (2 * n) F.Carrier))
      (s : ℝ),
      Nonempty (((T.exponentHeight (BlockShape.uniform 2 n hn)
        (fun i => if (i : ℕ) = 0 then 1 else -1) K hK hPK).family
          (twist (T.parabolicHalfModulus (BlockShape.uniform 2 n hn))
            (((BlockShape.uniform 2 n hn).blockTensor
              (fun _ => A.representation)).comp
              ((BlockShape.uniform 2 n hn).leviProjection F.Carrier))) s).Equiv
        (complementaryProduct F T hn A s).representation) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (2 * n)
  intro K hK hPK s
  have hu : (fun i : Fin 2 => s * (if (i : ℕ) = 0 then 1 else -1)) =
      (fun i : Fin 2 => if (i : ℕ) = 0 then s else -s) := by
    funext i
    fin_cases i <;> simp
  have he :
      T.twistedProductInduced (BlockShape.uniform 2 n hn) (fun _ => A)
          (fun i => s * (if (i : ℕ) = 0 then 1 else -1)) =
        complementaryProduct F T hn A s :=
    congrArg (T.twistedProductInduced (BlockShape.uniform 2 n hn) (fun _ => A)) hu
  exact ⟨(T.exponentFamilyEquiv (BlockShape.uniform 2 n hn) (fun _ => A)
      (fun i => if (i : ℕ) = 0 then 1 else -1) K hK hPK s).trans
    (SmoothRep.equivOfIso (eqToIso he))⟩

private theorem complementary_nontrivial_of_irreducible {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) : Nontrivial V := by
  have := hρ
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have : Subsingleton (Submodule ℂ V) := (Submodule.subsingleton_iff ℂ).mpr hV
  exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

set_option maxHeartbeats 1000000 in
/-- The open-interval clause of Tadic 1986 Proposition 2.9. -/
theorem complementaryProduct_unitarizableOnInterval {n : ℕ} (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (a : ℝ) (hAi : letI := T.topology; A.IsIrreducible)
    (hAu : letI := T.topology; IsUnitarizable A.representation)
    (ha : 0 < a)
    (hirr : letI := T.topology
      ∀ s ∈ Set.Ioo (-a) a, (complementaryProduct F T hn A s).IsIrreducible) :
    letI := T.topology
    ∀ s ∈ Set.Ioo (-a) a,
      IsUnitarizable (complementaryProduct F T hn A s).representation := by
  letI := T.topology
  let B := BlockShape.uniform 2 n hn
  have hAa : IsAdmissible A.representation :=
    (CuspidalSupport.cuspidalEmbedding F T n A hAi).1
  obtain ⟨K, hK, hPK, hμ⟩ := glParabolicCompactScalarIntegral p F T (2 * n) (by omega) B
  letI := T.generalLinearTopologicalGroup (2 * n)
  letI : MeasurableSpace K := borel K
  obtain ⟨μ, hHaar, _hprob, hscalar⟩ := hμ
  have := hHaar
  obtain ⟨bT, -⟩ := FiniteTensor.invariantPositiveForm.{0, uF, max uF uV}
    (Fin B.length) (fun i => GeneralLinear (B.size i) F.Carrier)
    (fun _ => (A : Type (max uF uV))) (fun _ => A.representation)
    (fun _ => Classical.choice hAu)
  let σL := B.blockTensor (fun _ => A.representation)
  let H := T.exponentHeight B (fun i => if (i : ℕ) = 0 then 1 else -1) K hK hPK
  let σ := twist (T.parabolicHalfModulus B) (σL.comp (B.leviProjection F.Carrier))
  let π : ℝ → Representation ℂ (GeneralLinear (2 * n) F.Carrier)
      (Induction.SmoothFunctions (B.parabolic F.Carrier) σ) := fun s => H.family σ s
  have E : ∀ s, Nonempty ((π s).Equiv (complementaryProduct F T hn A s).representation) :=
    complementaryFamilyEquiv F T hn A K hK hPK
  let c := (T.normalizedIntegralForm B σL bT K.toSubgroup μ hPK hscalar).toInnerProductCore
  have hc : ∀ (s : ℝ) (g : GeneralLinear (2 * n) F.Carrier)
      (v w : Induction.SmoothFunctions (B.parabolic F.Carrier) σ),
      c.inner (π s g v) (π (-s) g w) = c.inner v w := fun s g v w =>
    T.normalizedIntegralForm_family_neg B σL bT K.toSubgroup μ hPK hscalar H s g v w
  have hforms : ∀ s ∈ Set.Ioo (-a) a,
      ∃ b : Induction.SmoothFunctions (B.parabolic F.Carrier) σ →ₗ⋆[ℂ]
          Induction.SmoothFunctions (B.parabolic F.Carrier) σ →ₗ[ℂ] ℂ, b ≠ 0 ∧
        ∀ (g : GeneralLinear (2 * n) F.Carrier) (v w : _),
          b (π s g v) (π s g w) = b v w := by
    intro s hs
    let e : (π s).Equiv (π (-s)) :=
      (E s).some.trans ((SmoothRep.equivOfIso
        (complementaryProduct_swap F T hn A hAi s (hirr s hs)).some).trans
          (E (-s)).some.symm)
    have : Nontrivial (Induction.SmoothFunctions (B.parabolic F.Carrier) σ) :=
      complementary_nontrivial_of_irreducible
        ((isIrreducible_iff_of_equiv (E s).some).mpr (hirr s hs))
    exact ⟨pairingSesquilinear c e.toLinearMap,
      pairingSesquilinear_ne_zero c e.toLinearEquiv,
      pairingSesquilinear_invariant c (hc s) e⟩
  have hres := unitarizabilityContinuation.{uF, max uF uV} (GeneralLinear (2 * n) F.Carrier)
    (Induction.SmoothFunctions (B.parabolic F.Carrier) σ) π (Set.Ioo (-a) a) K hK
    isPreconnected_Ioo
    (fun s _ t _ g hg => H.family_apply_eq_of_mem σ s t hg)
    (fun s _ => isAdmissible_of_equiv (E s).some.symm
      (complementaryProduct_isAdmissible F T hn A hAa s))
    (fun s hs => (isIrreducible_iff_of_equiv (E s).some).mpr (hirr s hs))
    hforms
    (fun g v ℓ => (H.continuous_family_apply σ g v ℓ).continuousOn)
    0 (by constructor <;> linarith)
    ⟨T.familyZeroForm B σL bT K.toSubgroup μ hPK hscalar H⟩
  intro s hs
  exact (isUnitarizable_iff_of_equiv (E s).some).mp (hres s hs)

/-- The complete open-interval statement with independent field and carrier
universes. The endpoint clause belongs to the full complementary-series target. -/
theorem complementarySeriesOpenIntervalUnitarity :
    ComplementarySeriesOpenIntervalUnitarity.{uF, uV} F T := by
  letI := T.topology
  intro n hn A a hAi hAu ha hirr
  exact complementaryProduct_unitarizableOnInterval F T hn A a hAi hAu ha hirr

end Langlands.Classification
