import Langlands.BaseChange.CyclicProductFiberIntegral
import Langlands.BaseChange.CyclicProductNormCoordinates
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.RegularCyclicTwistedOrbit
import Langlands.BaseChange.NearIdentityConcordance
import Langlands.BaseChange.GeneralLinearFiniteAlgebra
import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Representation.Hecke.CommonInvarianceProof
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Concordance through the coordinates of a cyclic algebra

Let `E` be a cyclic `F`-algebra with generator `σ` of order `(m + 1) d`, written through an
`F`-algebra isomorphism `c : E ≃ₐ[F] (Fin (m + 1) → L)` onto `m + 1` copies of a field `L` with
`IsCyclicAlgebra τ d`, `σ` shifting the coordinates and acting by `τ` at the wrap, and let
`κ : GL_n(E) ≃ₜ* GL_n(L)^{m+1}` be the coordinates on `GL_n` (`cyclicProductGLCoordinates`). For
a Haar measure `μ` of `GL_n(L)` and the Haar measure `μE` of `GL_n(E)` carried by `κ` to the
product of `μ`, if the fibre integral `splitFiberIntegral μ Φ` of a continuous compactly
supported `Φ` on `GL_n(L)^{m+1}` is concordant with `f` for `(τ, d, μF, μ)`, then `Φ ∘ κ` is
concordant with `f` for `(σ, (m + 1) d, μF, μE)` (`areConcordant_cyclicProduct_of_splitFiberIntegral`;
for tensors, `areConcordant_cyclicProduct_of_splitFiberConvolution`). See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory _root_.Topology
open Langlands.QuotientIntegration Langlands.TraceFormula Langlands.JacquetLanglands
open Langlands.HarmonicAnalysis

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v w

section Coordinates

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]

/-- **Field coordinates of a cyclic algebra.** A cyclic `F`-algebra `E` of group `⟨σ⟩` of order
`l` is isomorphic to `m + 1` copies of a field `L` (in the universe of `E`) with a generator `τ`
of `L / F` of order `d`, `l = (m + 1) d`, `σ` shifting the coordinates and acting by `τ` at the
wrap. -/
theorem exists_cyclicAlgebraFieldCoordinates {σ : E ≃ₐ[F] E} {l : ℕ}
    (hσ : IsCyclicAlgebra σ l) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra F L) (m d : ℕ) (τ : L ≃ₐ[F] L)
      (c : E ≃ₐ[F] (Fin (m + 1) → L)),
      l = (m + 1) * d ∧ IsCyclicAlgebra τ d ∧
        (∀ (x : E) (i : Fin m), c (σ x) i.castSucc = c x i.succ) ∧
        ∀ x : E, c (σ x) (Fin.last m) = τ (c x 0) := by
  obtain ⟨data⟩ := CyclicAlgebraStructure.exists_coordinates hσ
  let : data.m.asIdeal.IsMaximal := data.m.isMaximal
  let : Field (E ⧸ data.m.asIdeal) := Ideal.Quotient.field _
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero data.r_pos.ne'
  let reindex : Fin (m + 1) ≃ Fin data.r := finCongr hm.symm
  let c : E ≃ₐ[F] (Fin (m + 1) → E ⧸ data.m.asIdeal) :=
    data.coords.trans (AlgEquiv.piCongrLeft F (fun _ : Fin data.r => E ⧸ data.m.asIdeal)
      reindex).symm
  have hcoord (x : E) (j : Fin (m + 1)) :
      c x j = Ideal.Quotient.mk data.m.asIdeal ((σ ^ j.val) x) := by
    change data.coords x (reindex j) = _
    rw [data.coords_apply]
    rfl
  refine ⟨E ⧸ data.m.asIdeal, inferInstance, inferInstance, m, data.d, data.τ, c,
    data.degree_eq.trans (by rw [hm]), data.cyclic, ?_, ?_⟩
  · intro x j
    rw [hcoord, hcoord, Fin.val_castSucc, Fin.val_succ, pow_succ, AlgEquiv.mul_apply]
  · intro x
    rw [hcoord, hcoord, Fin.val_last, Fin.val_zero, pow_zero, AlgEquiv.one_apply]
    have h := data.wrap x
    rw [hm, pow_succ, AlgEquiv.mul_apply] at h
    exact h

end Coordinates

section Measures

open scoped NNReal

/-- **Product Haar measures through a topological isomorphism `H ≃ₜ* G^{m+1}`.** Every Haar
measure `μH` of `H` is carried by `κ` to the product of `m + 1` copies of one Haar measure `μ` of
`G`: `μH = s • κ⁻¹_*(μ₀^{⊗(m+1)})` for a Haar measure `μ₀` of `G` and some `s > 0`, and
`μ = s^{1/(m+1)} • μ₀`. -/
theorem exists_isHaarMeasure_measurePreserving_pi {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] {m : ℕ}
    (κ : H ≃ₜ* (Fin (m + 1) → G)) (μH : Measure H) [μH.IsHaarMeasure] :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧
      MeasurePreserving κ μH (Measure.pi fun _ : Fin (m + 1) => μ) := by
  let : LocallyCompactSpace H := κ.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology H := κ.toHomeomorph.isEmbedding.secondCountableTopology
  let μ₀ : Measure G := Measure.haar
  let ν₀ : Measure H := Measure.map κ.symm (Measure.pi fun _ : Fin (m + 1) => μ₀)
  have : ν₀.IsHaarMeasure := κ.symm.isHaarMeasure_map _
  let s : ℝ≥0 := Measure.haarScalarFactor μH ν₀
  have hs : μH = s • ν₀ := Measure.isMulLeftInvariant_eq_smul μH ν₀
  have hspos : 0 < s := Measure.haarScalarFactor_pos_of_isHaarMeasure μH ν₀
  let t : ℝ≥0 := s ^ ((m + 1 : ℕ) : ℝ)⁻¹
  have ht : t ^ (m + 1) = s := NNReal.rpow_inv_natCast_pow s (Nat.succ_ne_zero m)
  have htpos : t ≠ 0 := (NNReal.rpow_pos hspos).ne'
  have hμ : (t • μ₀).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul μ₀ htpos
  refine ⟨t • μ₀, hμ, κ.continuous.measurable, ?_⟩
  have hpi : Measure.pi (fun _ : Fin (m + 1) => t • μ₀) =
      s • Measure.pi (fun _ : Fin (m + 1) => μ₀) := by
    refine Measure.pi_eq fun S hS => ?_
    rw [Measure.smul_apply, Measure.pi_pi, ← ht]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.coe_pow]
  rw [hpi, hs, Measure.map_smul]
  · congr 1
    change Measure.map κ (Measure.map κ.symm (Measure.pi fun _ : Fin (m + 1) => μ₀)) = _
    rw [Measure.map_map (map_continuous κ).measurable (map_continuous κ.symm).measurable]
    simp [Function.comp_def]
  · exact (map_continuous κ).measurable.aemeasurable

end Measures

section Transport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E]
variable {L : Type w} [Field L] [Algebra F L] [TopologicalSpace L] [IsTopologicalRing L]
  [IsModuleTopology F L]
variable {m d n : ℕ} {σ : E ≃ₐ[F] E} {τ : L ≃ₐ[F] L}
variable (c : E ≃ₐ[F] (Fin (m + 1) → L)) (hc : Continuous c) (hc' : Continuous c.symm)
  (hshift : ∀ (x : E) (i : Fin m), c (σ x) i.castSucc = c x i.succ)
  (hwrap : ∀ x : E, c (σ x) (Fin.last m) = τ (c x 0))
/-- The topological facts on `GL_n(L)` used by the transport. -/
private theorem generalLinear_topology_of_cyclic (hτ : IsCyclicAlgebra τ d) :
    T2Space (GeneralLinear n L) ∧ LocallyCompactSpace (GeneralLinear n L) ∧
      SecondCountableTopology (GeneralLinear n L) ∧ T2Space L ∧
        TotallyDisconnectedSpace (GeneralLinear n L) := by
  let : Module.Finite F L := hτ.1
  let := LocalFieldTopology.t2Space F
  let := LocalFieldTopology.secondCountableTopology F
  let := LocalFieldTopology.totallyDisconnectedSpace F
  have hp := generalLinear_isLocallyProfinite_of_finiteAlgebra (F := F) (E := L) n
  exact ⟨hp.t2Space, hp.locallyCompactSpace,
    generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := L) n,
    (finiteAlgebraTopology F L).1, hp.totallyDisconnectedSpace⟩

omit [IsTopologicalRing E] [IsModuleTopology F E] in
/-- **Closed twisted orbits over a cyclic field extension.** If `y ∈ GL_n(L)` is associated for
`(τ, d)` with a regular semisimple `γ ∈ GL_n(F)`, the τ-twisted orbit map
`G^τ_y \ GL_n(L) → GL_n(L)` is a closed embedding. -/
theorem isClosedEmbedding_twistedOrbitFunction_of_isNormAssociated (hτ : IsCyclicAlgebra τ d)
    {y : GeneralLinear n L} {γ : GeneralLinear n F} (hassoc : IsNormAssociated τ d y γ)
    (hreg : IsRegularSemisimple γ) :
    IsClosedEmbedding (twistedOrbitFunction (entrywiseAut τ n) y id) := by
  obtain ⟨hT2, hLC, hSC, hT2L, -⟩ := generalLinear_topology_of_cyclic (n := n) hτ
  have hnormReg : IsRegularSemisimple (cyclicNorm τ d y) := by
    obtain ⟨g, hg⟩ := hassoc
    have h := hreg.baseChange (E := L)
    rw [← hg, isRegularSemisimple_conj_iff] at h
    exact h
  exact isClosedEmbedding_twistedOrbitFunction_id (entrywiseAut τ n) (continuous_entrywiseAut τ n)
    y (isClosed_range_twistedConj_of_regularNorm hτ y hnormReg)

variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [MeasurableSpace (GeneralLinear n L)] [BorelSpace (GeneralLinear n L)]

local notation "κ" => cyclicProductGLCoordinates (n := n) c hc hc'

include hshift hwrap in
/-- **Transport of concordance at one pair through the coordinates.** -/
private theorem concordAt_cyclicProduct (hτ : IsCyclicAlgebra τ d)
    (μF : Measure (GeneralLinear n F)) (μ : Measure (GeneralLinear n L)) [μ.IsHaarMeasure]
    (μE : Measure (GeneralLinear n E))
    (hκ : MeasurePreserving κ μE (Measure.pi fun _ : Fin (m + 1) => μ))
    (Φ : (Fin (m + 1) → GeneralLinear n L) → ℂ) (hΦc : Continuous Φ)
    (hΦs : HasCompactSupport Φ) (f : GeneralLinear n F → ℂ)
    (δ : GeneralLinear n E) (γ : GeneralLinear n F)
    (hassoc : IsNormAssociated τ d (List.ofFn (κ δ)).prod γ) (hreg : IsRegularSemisimple γ)
    (hL : ConcordAt τ d μF μ (splitFiberIntegral μ Φ) f (List.ofFn (κ δ)).prod γ) :
    ConcordAt σ ((m + 1) * d) μF μE (fun x => Φ (κ x)) f δ γ := by
  intro μδ _ _ μγ _ _ νδ νγ hνδ hνγ hmeas
  obtain ⟨hT2, hLC, hSC, hT2L, -⟩ := generalLinear_topology_of_cyclic (n := n) hτ
  let G := GeneralLinear n L
  let H := GeneralLinear n E
  let σG := (entrywiseAut σ n).toMonoidHom
  let τG := (entrywiseAut τ n).toMonoidHom
  have hshiftG (x : H) (i : Fin m) : κ (σG x) i.castSucc = κ x i.succ :=
    cyclicProductGLCoordinates_shift c hc hc' hshift x i
  have hwrapG (x : H) : κ (σG x) (Fin.last m) = τG (κ x 0) :=
    cyclicProductGLCoordinates_wrap c hc hc' hwrap x
  let y := (List.ofFn (κ δ)).prod
  let C := sigmaCentralizer σ n δ
  let Z := sigmaCentralizer τ n y
  let e : C ≃ₜ* Z := cyclicProductCentralizerEquiv κ σG τG hshiftG hwrapG δ
  let μZ : Measure Z := Measure.map e μδ
  let : μZ.IsHaarMeasure := e.isHaarMeasure_map μδ
  let : μZ.IsMulRightInvariant := isMulRightInvariant_map e μδ
  have heZ : MeasurePreserving e μδ μZ := ⟨e.continuous.measurable, rfl⟩
  have hτG : Continuous τG := continuous_entrywiseAut τ n
  have hσG : Continuous σG := continuous_entrywiseAut σ n
  let : SigmaCompactSpace G := inferInstance
  let : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let : μ.InnerRegular := inferInstance
  let : μ.IsMulRightInvariant := generalLinear_haar_rightInvariant L n μ
  have hclosed : IsClosed (Z : Set G) :=
    isClosed_eq ((continuous_inv.mul continuous_const).mul hτG) continuous_const
  let : LocallyCompactSpace Z := hclosed.locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace G := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace Z :=
    hclosed.isClosedEmbedding_subtypeVal.isEmbedding.isInducing.pseudoMetrizableSpace
  let : μZ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μZ
  obtain ⟨νZ, hνZ⟩ := compatibleMeasureExists Z hclosed μ μZ
  have hZ : Measure.map Subtype.val μZ =
      Measure.map (fun z : sigmaCentralizer σ n δ => κ z.val 0) μδ := by
    change Measure.map Subtype.val (Measure.map e μδ) = _
    rw [Measure.map_map measurable_subtype_coe (map_continuous e).measurable]
    rfl
  have hassocZ : IsAssociatedMeasure τ d y γ μZ μγ :=
    IsAssociatedMeasure.cyclicProduct c hc hc' hshift hwrap hZ hmeas
  have hOrbit : IsClosedEmbedding (twistedOrbitFunction τG y id) :=
    isClosedEmbedding_twistedOrbitFunction_of_isNormAssociated hτ hassoc hreg
  have htransfer :=
    @cyclicProductOrbitalIntegral_eq_splitFiberIntegral H _ _ _ _ _ G _ _ _ _ _ _ _ _ m κ σG τG
      hshiftG hwrapG δ hσG hτG μ _ μE hκ μδ
      (inferInstanceAs μδ.IsHaarMeasure) (inferInstanceAs μδ.IsMulRightInvariant)
      μZ (inferInstanceAs μZ.IsHaarMeasure) (inferInstanceAs μZ.IsMulRightInvariant)
      νδ νZ hνδ hνZ heZ hOrbit Φ hΦc hΦs
  exact htransfer.trans (hL μZ μγ νZ νγ hνZ hνγ hassocZ)

include hshift hwrap in
/-- **Transport of concordance through the coordinates of a cyclic algebra.** If the fibre
integral of a continuous compactly supported `Φ` on `GL_n(L)^{m+1}` is concordant with `f` for
`(τ, d, μF, μ)`, then `Φ ∘ κ` is concordant with `f` for `(σ, (m + 1) d, μF, μE)`, where `κ`
carries `μE` to the product of `μ`. -/
theorem areConcordant_cyclicProduct_of_splitFiberIntegral (hσ : σ ^ ((m + 1) * d) = 1)
    (hτ : IsCyclicAlgebra τ d)
    (μF : Measure (GeneralLinear n F)) (μ : Measure (GeneralLinear n L)) [μ.IsHaarMeasure]
    (μE : Measure (GeneralLinear n E))
    (hκ : MeasurePreserving κ μE (Measure.pi fun _ : Fin (m + 1) => μ))
    (Φ : (Fin (m + 1) → GeneralLinear n L) → ℂ) (hΦc : Continuous Φ)
    (hΦs : HasCompactSupport Φ) (f : GeneralLinear n F → ℂ)
    (h : AreConcordant τ d μF μ (splitFiberIntegral μ Φ) f) :
    AreConcordant σ ((m + 1) * d) μF μE (fun x => Φ (κ x)) f := by
  refine ⟨(vanishesOffNorms_cyclicProduct_iff c hc hc' hshift hwrap hσ μF f).mpr h.1, ?_⟩
  intro δ γ hassoc hreg
  have hassoc' := (cyclicProductGLCoordinates_normAssociated_iff c hc hc' hshift hwrap d hσ
    δ γ).mp hassoc
  exact concordAt_cyclicProduct c hc hc' hshift hwrap hτ μF μ μE hκ Φ hΦc hΦs f δ γ hassoc' hreg
    (h.2 _ γ hassoc' hreg)

include hshift hwrap in
/-- **Transport of concordance for one tensor.** If the ordered convolution
`splitFiberConvolution μ ψ` of continuous compactly supported `ψ i` is concordant with `f` for
`(τ, d, μF, μ)`, then the tensor `x ↦ ∏ i, ψ i (κ x i)` is concordant with `f` for
`(σ, (m + 1) d, μF, μE)`. -/
theorem areConcordant_cyclicProduct_of_splitFiberConvolution (hσ : σ ^ ((m + 1) * d) = 1)
    (hτ : IsCyclicAlgebra τ d)
    (μF : Measure (GeneralLinear n F)) (μ : Measure (GeneralLinear n L)) [μ.IsHaarMeasure]
    (μE : Measure (GeneralLinear n E))
    (hκ : MeasurePreserving κ μE (Measure.pi fun _ : Fin (m + 1) => μ))
    (ψ : Fin (m + 1) → GeneralLinear n L → ℂ) (hψc : ∀ i, Continuous (ψ i))
    (hψs : ∀ i, HasCompactSupport (ψ i)) (f : GeneralLinear n F → ℂ)
    (h : AreConcordant τ d μF μ (splitFiberConvolution μ ψ) f) :
    AreConcordant σ ((m + 1) * d) μF μE (fun x => ∏ i, ψ i (κ x i)) f := by
  have hΦc : Continuous (fun x : Fin (m + 1) → GeneralLinear n L => ∏ i, ψ i (x i)) :=
    continuous_finsetProd _ fun i _ => (hψc i).comp (continuous_apply i)
  have hΦs : HasCompactSupport (fun x : Fin (m + 1) → GeneralLinear n L => ∏ i, ψ i (x i)) := by
    exact (splitTensor_continuous_hasCompactSupport ψ hψc hψs).2
  exact areConcordant_cyclicProduct_of_splitFiberIntegral c hc hc' hshift hwrap hσ hτ μF μ μE hκ
    (fun x => ∏ i, ψ i (x i)) hΦc hΦs f (by rwa [splitFiberIntegral_tensor])

include hshift hwrap in
/-- **From `GL_n(E)` to `GL_n(L)`.** For a Schwartz–Bruhat `φ` on `GL_n(E)`, the fibre integral
`φL` of `φ ∘ κ⁻¹` is a Schwartz–Bruhat function on `GL_n(L)`, with support in a subgroup `K₀`
when `φ` has support in `κ⁻¹(K₀^{m+1})`, and every `f` concordant with `φL` for
`(τ, d, μF, μ)` is concordant with `φ` for `(σ, (m + 1) d, μF, μE)`. -/
theorem exists_concordant_ordinary_cyclicProduct (hσ : σ ^ ((m + 1) * d) = 1)
    (hτ : IsCyclicAlgebra τ d)
    (μF : Measure (GeneralLinear n F)) (μ : Measure (GeneralLinear n L)) [μ.IsHaarMeasure]
    (μE : Measure (GeneralLinear n E))
    (hκ : MeasurePreserving κ μE (Measure.pi fun _ : Fin (m + 1) => μ))
    (φ : SchwartzBruhat (GeneralLinear n E)) :
    ∃ φL : SchwartzBruhat (GeneralLinear n L),
      (∀ K₀ : Subgroup (GeneralLinear n L),
        Function.support φ ⊆ κ ⁻¹' Set.pi Set.univ (fun _ => (K₀ : Set (GeneralLinear n L))) →
          Function.support φL ⊆ K₀) ∧
      ∀ f : GeneralLinear n F → ℂ, AreConcordant τ d μF μ φL f →
        AreConcordant σ ((m + 1) * d) μF μE φ f := by
  obtain ⟨hT2, -, -, -, -⟩ := generalLinear_topology_of_cyclic (n := n) hτ
  let Φ : SchwartzBruhat (Fin (m + 1) → GeneralLinear n L) :=
    ⟨fun x => φ ((κ).symm x), φ.locallyConstant.comp_continuous (κ).symm.continuous,
      φ.hasCompactSupport.comp_homeomorph (κ).symm.toHomeomorph⟩
  let φL : SchwartzBruhat (GeneralLinear n L) :=
    ⟨splitFiberIntegral μ Φ, splitFiberIntegral_mem_schwartzBruhat μ Φ⟩
  refine ⟨φL, ?_, ?_⟩
  · intro K₀ hφ
    refine support_splitFiberIntegral_subset μ K₀ Φ fun x hx => ?_
    have h := hφ (show (κ).symm x ∈ Function.support φ from hx)
    rwa [Set.mem_preimage, ContinuousMulEquiv.apply_symm_apply] at h
  · intro f hf
    have h := areConcordant_cyclicProduct_of_splitFiberIntegral c hc hc' hshift hwrap hσ hτ μF μ
      μE hκ Φ Φ.continuous Φ.hasCompactSupport f hf
    have heq : (fun x => Φ (κ x)) = φ := funext fun x => by
      change φ ((κ).symm (κ x)) = φ x
      rw [ContinuousMulEquiv.symm_apply_apply]
    rwa [heq] at h

include hshift hwrap in
/-- **From `GL_n(L)` to `GL_n(E)`.** For a Schwartz–Bruhat `φL` on `GL_n(L)`, left invariant under
a compact open subgroup `K`, the function `φ = (e_K ⊗ ⋯ ⊗ e_K ⊗ φL) ∘ κ` (`m` normalized
indicators `μ(K)⁻¹ 1_K`, then `φL`) is a Schwartz–Bruhat function on `GL_n(E)` whose fibre integral
is `φL`, so every `f` concordant with `φL` for `(τ, d, μF, μ)` is concordant with `φ` for
`(σ, (m + 1) d, μF, μE)`. -/
theorem exists_concordant_twisted_cyclicProduct (hσ : σ ^ ((m + 1) * d) = 1)
    (hτ : IsCyclicAlgebra τ d)
    (μF : Measure (GeneralLinear n F)) (μ : Measure (GeneralLinear n L)) [μ.IsHaarMeasure]
    (μE : Measure (GeneralLinear n E))
    (hκ : MeasurePreserving κ μE (Measure.pi fun _ : Fin (m + 1) => μ))
    (φL : SchwartzBruhat (GeneralLinear n L)) :
    ∃ φ : SchwartzBruhat (GeneralLinear n E),
      ∀ f : GeneralLinear n F → ℂ, AreConcordant τ d μF μ φL f →
        AreConcordant σ ((m + 1) * d) μF μE φ f := by
  obtain ⟨hT2, hLC, hSC, -, hTD⟩ := generalLinear_topology_of_cyclic (n := n) hτ
  obtain ⟨K, -, hKc, hK⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance (GeneralLinear n L) {φL} ⊤
  have hφK := (hK φL (Finset.mem_singleton_self φL)).1
  let Φ : SchwartzBruhat (Fin (m + 1) → GeneralLinear n L) :=
    ⟨splitUnitTensor μ (K : Set (GeneralLinear n L)) φL,
      splitUnitTensor_mem_schwartzBruhat μ K.toSubgroup K.isOpen hKc φL⟩
  let φ : SchwartzBruhat (GeneralLinear n E) :=
    ⟨fun x => Φ (κ x), Φ.locallyConstant.comp_continuous (κ).continuous,
      Φ.hasCompactSupport.comp_homeomorph (κ).toHomeomorph⟩
  refine ⟨φ, fun f hf => ?_⟩
  have hfib : splitFiberIntegral μ Φ = φL :=
    splitFiberIntegral_splitUnitTensor μ K.toSubgroup K.isOpen.measurableSet
      (K.isOpen.measure_ne_zero μ ⟨1, K.one_mem⟩) hKc.measure_lt_top.ne φL
      (fun k hk x => hφK ⟨k, hk⟩ x)
  exact areConcordant_cyclicProduct_of_splitFiberIntegral c hc hc' hshift hwrap hσ hτ μF μ μE hκ
    Φ Φ.continuous Φ.hasCompactSupport f (by rw [hfib]; exact hf)

end Transport

end Langlands.BaseChange
