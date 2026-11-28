import Langlands.BaseChange.CuspFormOrbitalVanishingStatement
import Langlands.BaseChange.RegularSemisimpleLevi
import Langlands.BaseChange.TwistedOrbitalConjugation
import Langlands.Group.GL.TwoBlockUnipotent
import Langlands.Group.GL.LocalFieldTopology
import Langlands.TraceFormula.UnipotentOrbitalVanishing

/-!
# Orbital integrals of cusp forms on `GL_n(F)` vanish off the elliptic set

Proof of `CuspFormOrbitalVanishingStatement` (`cuspFormOrbitalVanishing`). A regular
semisimple `γ` that is not regular elliptic is conjugate to a block diagonal `δ = diag(a, d)`
in a proper standard two-block Levi subgroup, with `a` and `d` of coprime characteristic
polynomials (`exists_twoBlock_of_regularSemisimple_of_not_regularElliptic`). For the unipotent
radical `U` of the corresponding parabolic subgroup:

* the centralizer of `δ` lies in the Levi subgroup (`glCentralizer_le_leviSubgroup`), so it
  normalizes `U`, and its elements in `U C` lie in the compact set obtained from `C ∩ P` by the
  Levi projection (`exists_isCompact_glCentralizer_mem_unipotent_mul`);
* `u ↦ δ⁻¹ u⁻¹ δ u` is a topological group automorphism of `U`
  (`BlockShape.twistContinuousMulEquiv`), so `u ↦ u⁻¹ δ u` is proper on `U`
  (`exists_isCompact_unipotent_conj_mem`) and, by invariance of Haar measures under this
  automorphism, `∫_U f(x⁻¹ u⁻¹ δ u x) du = ∫_U f(x⁻¹ δ v x) dv' = 0` for a cusp form `f`,
  where `dv' = Ψ_* du` is the pushforward of the Haar measure `du` under
  `Ψ(u) = δ⁻¹ u⁻¹ δ u`; it is again a Haar measure on `U`, in general not equal to `du`
  (`integral_unipotent_conj_eq_zero`).

The general vanishing criterion `TraceFormula.twistedOrbitalIntegral_eq_zero_of_unipotent`
then gives the vanishing of the orbital integral at `δ`
(`orbitalIntegral_eq_zero_of_twoBlock`), and conjugation invariance
(`twistedOrbitalIntegral_map_conj`, `isCompatible_map_twistedConj`) carries it back to `γ`.
See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure Set
open Langlands.QuotientIntegration Langlands.TraceFormula Langlands.GeneralLinear
open Langlands.JacquetLanglands Langlands.HarmonicAnalysis
open scoped Pointwise

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

/-- The image of a right-invariant measure under a topological group isomorphism is
right-invariant. -/
theorem isMulRightInvariant_map_continuousMulEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (μ : Measure G) [IsMulRightInvariant μ] : IsMulRightInvariant (μ.map e) := by
  constructor
  intro h
  have hem : Measurable (e : G → H) := e.continuous.measurable
  have hmul : ∀ a : H, Measurable (fun x : H => x * a) := fun a =>
    (continuous_id.mul continuous_const).measurable
  have hmulG : ∀ a : G, Measurable (fun x : G => x * a) := fun a =>
    (continuous_id.mul continuous_const).measurable
  rw [Measure.map_map (hmul h) hem]
  have hcomm : (fun x => x * h) ∘ e = e ∘ (fun x => x * e.symm h) := by
    funext x
    simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.apply_symm_apply]
  rw [hcomm, ← Measure.map_map hem (hmulG _),
    map_mul_right_eq_self]

section TwoBlock

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] {n : ℕ}

/-- Elements of the centralizer of a block diagonal element with pairwise coprime
characteristic polynomials that lie in `U C`, for `U` the unipotent radical and `C` compact,
lie in a compact set: they are block diagonal, so they are the Levi projections of elements
of `C ∩ P`. -/
theorem exists_isCompact_glCentralizer_mem_unipotent_mul (B : BlockShape n) (m : B.Levi F)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly)
    (C : Set (GeneralLinear n F)) (hC : IsCompact C) :
    ∃ D : Set (GeneralLinear n F), IsCompact D ∧
      ∀ t ∈ glCentralizer (B.leviEmbedding F m),
        t ∈ (B.unipotentSubgroup F : Set (GeneralLinear n F)) * C → t ∈ D := by
  refine ⟨(fun p : B.parabolic F => B.leviEmbedding F (B.leviProjection F p)) ''
      ((fun p : B.parabolic F => (p : GeneralLinear n F)) ⁻¹' C), ?_, ?_⟩
  · exact ((B.isClosed_parabolic F).isClosedEmbedding_subtypeVal.isCompact_preimage hC).image
      ((B.leviEmbeddingContinuous F).continuous.comp (B.leviProjectionContinuous F).continuous)
  · intro t ht htUC
    obtain ⟨u, hu, c, hc, rfl⟩ := Set.mem_mul.mp htUC
    obtain ⟨mt, hmt⟩ := glCentralizer_le_leviSubgroup B m hm ht
    have huP : u ∈ B.parabolic F := ((B.mem_unipotentSubgroup_iff F u).1 hu).1
    have hc' : c = u⁻¹ * B.leviEmbedding F mt := by
      rw [hmt, inv_mul_cancel_left]
    have hcP : c ∈ B.parabolic F := by
      rw [hc']
      exact (B.parabolic F).mul_mem ((B.parabolic F).inv_mem huP) (B.leviInParabolic F mt).2
    refine ⟨⟨c, hcP⟩, hc, ?_⟩
    have hsplit : (⟨c, hcP⟩ : B.parabolic F) =
        ⟨u⁻¹, (B.parabolic F).inv_mem huP⟩ * B.leviInParabolic F mt := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, B.leviInParabolic_val]
      exact hc'
    obtain ⟨w, hw, hwu⟩ := (B.unipotentSubgroup F).inv_mem hu
    have hu1 : B.leviProjection F ⟨u⁻¹, (B.parabolic F).inv_mem huP⟩ = 1 := by
      have hw' : (⟨u⁻¹, (B.parabolic F).inv_mem huP⟩ : B.parabolic F) = w :=
        Subtype.ext hwu.symm
      rw [hw']
      exact hw
    change B.leviEmbedding F (B.leviProjection F ⟨c, hcP⟩) = u * c
    rw [hsplit, map_mul, hu1, one_mul, B.leviProjection_section, hmt]

variable [LocallyCompactSpace (GeneralLinear n F)] [SigmaCompactSpace (GeneralLinear n F)]

/-- For a two-block shape and a block diagonal `δ` with coprime block characteristic
polynomials, `u ↦ u⁻¹ δ u` is proper on the unipotent radical. -/
theorem exists_isCompact_unipotent_conj_mem {B : BlockShape n} (hB : B.length = 2)
    (m : B.Levi F) (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly)
    (C : Set (GeneralLinear n F)) (hC : IsCompact C) :
    ∃ D : Set (GeneralLinear n F), IsCompact D ∧
      ∀ u ∈ B.unipotentSubgroup F, u⁻¹ * B.leviEmbedding F m * u ∈ C → u ∈ D := by
  set Ψ := BlockShape.twistContinuousMulEquiv hB m hm
  refine ⟨(fun v : B.unipotentSubgroup F => (v : GeneralLinear n F)) ''
      (Ψ.symm '' ((fun v : B.unipotentSubgroup F => (v : GeneralLinear n F)) ⁻¹'
        ((fun y => (B.leviEmbedding F m)⁻¹ * y) '' C))), ?_, ?_⟩
  · refine ((((B.isClosed_unipotentSubgroup F).isClosedEmbedding_subtypeVal.isCompact_preimage
      (hC.image (continuous_const.mul continuous_id))).image Ψ.symm.continuous).image
      continuous_subtype_val)
  · intro u hu huC
    refine ⟨Ψ.symm (Ψ ⟨u, hu⟩), ⟨Ψ ⟨u, hu⟩, ⟨u⁻¹ * B.leviEmbedding F m * u, huC, ?_⟩, rfl⟩, by
      rw [ContinuousMulEquiv.symm_apply_apply]⟩
    change (B.leviEmbedding F m)⁻¹ * (u⁻¹ * B.leviEmbedding F m * u) =
      ((BlockShape.twistHom hB m ⟨u, hu⟩ : B.unipotentSubgroup F) : GeneralLinear n F)
    rw [BlockShape.twistHom_apply_coe]
    group

variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]

/-- For a two-block shape, a block diagonal `δ` with coprime block characteristic polynomials
and a function `f` whose integrals over all two-sided translates of the unipotent radical `U`
vanish for every Haar measure on `U`, `∫_U f(x⁻¹ u⁻¹ δ u x) du = 0`. -/
theorem integral_unipotent_conj_eq_zero {B : BlockShape n} (hB : B.length = 2)
    (m : B.Levi F) (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly)
    (μU : Measure (B.unipotentSubgroup F)) [μU.IsHaarMeasure] {f : GeneralLinear n F → ℂ}
    (hcusp : ∀ μ : Measure (B.unipotentSubgroup F), μ.IsHaarMeasure →
      ∀ x y : GeneralLinear n F, ∫ u : B.unipotentSubgroup F, f (x * u * y) ∂μ = 0)
    (x : GeneralLinear n F) :
    ∫ u : B.unipotentSubgroup F,
      f (x⁻¹ * ((u : GeneralLinear n F)⁻¹ * B.leviEmbedding F m * u) * x) ∂μU = 0 := by
  set Ψ := BlockShape.twistContinuousMulEquiv hB m hm
  have e : ∀ u : B.unipotentSubgroup F,
      x⁻¹ * ((u : GeneralLinear n F)⁻¹ * B.leviEmbedding F m * u) * x =
        x⁻¹ * B.leviEmbedding F m * ((Ψ u : B.unipotentSubgroup F) : GeneralLinear n F) * x := by
    intro u
    change _ = x⁻¹ * B.leviEmbedding F m * ((BlockShape.twistHom hB m u :
      B.unipotentSubgroup F) : GeneralLinear n F) * x
    rw [BlockShape.twistHom_apply_coe]
    group
  simp_rw [e]
  refine (integral_map_equiv Ψ.toHomeomorph.toMeasurableEquiv (fun v : B.unipotentSubgroup F =>
    f (x⁻¹ * B.leviEmbedding F m * (v : GeneralLinear n F) * x))).symm.trans ?_
  have : (μU.map Ψ).IsHaarMeasure := Ψ.isHaarMeasure_map μU
  exact hcusp _ this _ _

/-- **Orbital integrals vanish at two-block Levi elements.** Let `F` be a Hausdorff
topological field whose general linear group is locally compact and σ-compact, and let `K` be a
compact open subgroup of `GL_n(F)`. For a two-block shape and a block diagonal `δ` with
coprime block characteristic polynomials, the orbital integral at `δ` of a continuous compactly
supported `f` with vanishing integrals over all two-sided translates of the unipotent radical
(for every Haar measure on it) vanishes, for every compatible quotient measure. -/
theorem orbitalIntegral_eq_zero_of_twoBlock
    (K : OpenSubgroup (GeneralLinear n F)) (hK : IsCompact (K : Set (GeneralLinear n F)))
    {B : BlockShape n} (hB : B.length = 2) (m : B.Levi F)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly)
    (δ : GeneralLinear n F) (hδ : δ = B.leviEmbedding F m)
    (μG : Measure (GeneralLinear n F)) [μG.IsHaarMeasure]
    (μH : Measure (glCentralizer δ)) [IsMulRightInvariant μH] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure]
    (ν : Measure (LeftQuotient (glCentralizer δ))) (hν : IsCompatible (glCentralizer δ) μG μH ν)
    {f : GeneralLinear n F → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hcusp : ∀ μ : Measure (B.unipotentSubgroup F), μ.IsHaarMeasure →
      ∀ x y : GeneralLinear n F, ∫ u : B.unipotentSubgroup F, f (x * u * y) ∂μ = 0) :
    orbitalIntegral δ ν f = 0 := by
  subst hδ
  have : LocallyCompactSpace (B.unipotentSubgroup F) :=
    (B.isClosed_unipotentSubgroup F).locallyCompactSpace
  let μU : Measure (B.unipotentSubgroup F) := Measure.haar
  refine twistedOrbitalIntegral_eq_zero_of_unipotent (MonoidHom.id (GeneralLinear n F))
    continuous_id _ μG μH ν hν K hK (B.unipotentSubgroup F) (B.isClosed_unipotentSubgroup F) μU
    ?_ ?_ ?_ hf hfs ?_
  · intro t ht u hu
    have hN := B.leviSubgroup_le_normalizer_unipotentSubgroup F
      (glCentralizer_le_leviSubgroup B m hm ht)
    exact (Subgroup.mem_normalizer_iff.1 hN u).1 hu
  · exact exists_isCompact_glCentralizer_mem_unipotent_mul B m hm
  · exact exists_isCompact_unipotent_conj_mem hB m hm
  · exact integral_unipotent_conj_eq_zero hB m hm μU hcusp

end TwoBlock

/-- **Orbital integrals of cusp forms vanish off the elliptic set** (Henniart–Lemaire 2011,
II.4.5, the ordinary case `E = F`): proof of `CuspFormOrbitalVanishingStatement`. -/
theorem cuspFormOrbitalVanishing : CuspFormOrbitalVanishingStatement.{u} := by
  intro F _ _ _ _ _ n hn
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let : MeasurableSpace (GeneralLinear n F) := borel _
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  intro μF _ f hf γ hreg hell μγ _ _ νγ hν
  have := LocalFieldTopology.t2Space F
  have := LocalFieldTopology.generalLinear_sigmaCompactSpace F n
  obtain ⟨K, hK, -⟩ := LocalFieldTopology.generalLinear_compactOpen F n Set.univ Filter.univ_mem
  obtain ⟨k, hk, hkn, g, m, hg, -, -, hm⟩ :=
    exists_twoBlock_of_regularSemisimple_of_not_regularElliptic hn γ hreg hell
  let θ := MonoidHom.id (GeneralLinear n F)
  let μK := Measure.map (twistedCentralizerConj θ γ g) μγ
  have : IsMulRightInvariant μK :=
    isMulRightInvariant_map_continuousMulEquiv (twistedCentralizerConj θ γ g) μγ
  have : μK.IsHaarMeasure := (twistedCentralizerConj θ γ g).isHaarMeasure_map μγ
  have hν' := isCompatible_map_twistedConj θ γ g μγ μK μF rfl νγ hν
  have heq := (twistedOrbitalIntegral_map_conj θ γ g νγ (f : GeneralLinear n F → ℂ)).2
  change twistedOrbitalIntegral θ γ νγ (f : GeneralLinear n F → ℂ) = 0
  rw [← heq]
  exact orbitalIntegral_eq_zero_of_twoBlock K hK (B := ProductLeviChamber.twoBlock n k hk hkn)
    rfl m hm (twistedConj θ g γ) hg μF μK _ hν' (SchwartzBruhat.continuous f)
    (SchwartzBruhat.hasCompactSupport f) (fun μ hμ x y => (hf _ le_rfl μ hμ).2 x y)

end Langlands.BaseChange
