import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Global.AdelicWavePacketRationalInvariance
import Langlands.Global.AdelicSiegelConjugationBound
import Langlands.Global.AdelicPositiveTorusCompatibility
import Langlands.Global.AdelicRepresentationHeightExhaustion

/-! # Siegel-set decay of wave packets from joint continuity and the chamber estimate

`WavePacketSiegelDecayStatement` has three conclusions for a wave packet `Θ`: continuity,
left `G(F)`-invariance and the Siegel-set estimate `‖Θ x‖ ≤ B δ(a)^{1/2} σ(x)^{-n}`. This
module proves the second one outright and derives the other two from two propositions:

* `EisensteinImaginaryJointContinuityStatement`: every pointwise continuation of the Eisenstein
  series `E(φ, λ)` of `φ ∈ A^2_P` with a domain of holomorphy containing `i𝔞_P^*` is jointly
  continuous in `(λ, g) ∈ i𝔞_P^* × G(𝔸)`;
* `WavePacketChamberDecayStatement` (Delorme 2023, (5.2) in the proof of Proposition 5.4): the
  Siegel-set estimate at the points `z · a · ω`, with `z ∈ A_G`, `a` in the weak simple-root
  chamber and `ω` in a compact set.

The theorem `wavePacketSiegelDecay_of_reduction` derives `WavePacketSiegelDecayStatement` from
the two. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj NNReal ENNReal TensorProduct Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors Langlands.Analysis.Meromorphic

/-- **Joint continuity of Eisenstein series on the imaginary axis** (derived from
Bernstein–Lapid 2024, Theorem 2.3 (1) in the Fréchet form of Corollary 8.6, and Lapid 2011,
Proposition 6). Let `P = MU` be a parabolic with presentation `r`, `K` a maximal compact
subgroup with `P(𝔸)K = G(𝔸)`, and `φ ∈ A^2_P`. Let `E` be meromorphic in `λ ∈ X^*(P) ⊗ ℂ` at
each point `g`, with one domain of holomorphy `D` containing the imaginary parameters, and
equal to the Eisenstein series `E(φ, λ)` for `Re λ` sufficiently regular. Then, in every real
linear coordinate system `e : ℝⁿ ≃ X^*(P) ⊗ ℝ`, the map `(x, g) ↦ E(i e(x))(g)` is continuous on
`ℝⁿ × G(𝔸)`. -/
def EisensteinImaginaryJointContinuityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ →
      ∀ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        Set.range (imaginaryParameter F P) ⊆ D →
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
          E lam = hK.eisensteinSeries φ lam) →
        ∀ (n : ℕ) (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P),
          Continuous fun q : (Fin n → ℝ) × AdelicGroupPoints F G =>
            E (imaginaryParameter F P (e q.1)) q.2

/-- **Decay of wave packets on the positive chamber** (Delorme 2023, (5.2) in the proof of
Proposition 5.4, after covering the unit sphere of the chamber by finitely many cones). For the
data of `WavePacketSiegelDecayStatement`, every wave packet `Θ`, every algebraic Siegel setup
`(T, i, ν, T₀, j)`, every threshold `t`, every compact `Ω ⊆ G(𝔸)` and every `n : ℕ` there is `B`
with `‖Θ(z a ω)‖ ≤ B δ(a)^{1/2} / σ(z a ω)^n` for `z ∈ A_G`, `a` in the weak simple-root chamber
`|β(a)| ≥ t` of `A_{T₀}` and `ω ∈ Ω`. -/
def WavePacketChamberDecayStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      (∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
        (_ : IsClosedImmersion p₀.hom.hom.left),
        IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) →
    ∀ Θ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Θ →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
        (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j →
      ∀ (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
      ∀ n : ℕ, ∃ B : ℝ, ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
        ∀ a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t, ∀ ω ∈ Ω,
          ‖Θ (z * positiveMap F G T i T₀ j a * ω)‖ ≤
            B * Real.sqrt (siegelModulus F G T i ν T₀ j a) /
              adelicLogHeight F G rho (z * positiveMap F G T i T₀ j a * ω) ^ n

section Continuity

/-- A parametric integral over `ℝⁿ` of a jointly continuous function that vanishes outside a
fixed compact set is continuous in the parameter. No countability of the parameter space is
needed: the integrand converges uniformly on the compact set. -/
theorem continuous_integral_of_forall_notMem_eq_zero {X : Type*} [TopologicalSpace X] {n : ℕ}
    (mu : Measure (Fin n → ℝ)) [IsFiniteMeasureOnCompacts mu]
    {f : X → (Fin n → ℝ) → ℂ} (hf : Continuous (Function.uncurry f))
    {s : Set (Fin n → ℝ)} (hs : IsCompact s) (hzero : ∀ g, ∀ x ∉ s, f g x = 0) :
    Continuous fun g => ∫ x, f g x ∂mu := by
  have heq : (fun g => ∫ x, f g x ∂mu) = fun g => ∫ x in s, f g x ∂mu := by
    funext g
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero g)).symm
  rw [heq]
  have hint : ∀ g, IntegrableOn (f g) s mu := fun g =>
    ((hf.comp (Continuous.prodMk_right g)).continuousOn).integrableOn_compact hs
  refine continuous_iff_continuousAt.2 fun g₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  set m := mu.real s with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hδ : 0 < ε / (m + 1) := div_pos hε (by linarith)
  obtain ⟨v, hv, hvε⟩ := hs.mem_uniformity_of_prod (s := Set.univ) hf.continuousOn
    (Set.mem_univ g₀) (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with g hg
  rw [dist_eq_norm, ← integral_sub (hint g) (hint g₀)]
  have hbound : ∀ x ∈ s, ‖f g x - f g₀ x‖ ≤ ε / (m + 1) := fun x hx => by
    have := hvε g hg x hx
    rw [Set.mem_ofPred_eq, dist_eq_norm] at this
    exact this.le
  calc ‖∫ x in s, f g x - f g₀ x ∂mu‖ ≤ ε / (m + 1) * m :=
        norm_setIntegral_le_of_norm_le_const hs.measure_lt_top hbound
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- **Continuity of wave packets** from the joint continuity of the Eisenstein continuations
on the imaginary axis: the integrand of `Θ` is jointly continuous and vanishes outside the
compact union of the supports of the coefficients. -/
theorem IsWavePacket.continuous_of_jointContinuity
    (hcont : EisensteinImaginaryJointContinuityStatement)
    {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
    {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth} (hKmax : IsMaximalCompactSubgroup F G K)
    (hrho : IsClosedSubgroup rho) {Θ : AdelicGroupPoints F G → ℂ}
    (hΘ : IsWavePacket F G K rho hsmooth hcalc Θ) : Continuous Θ := by
  obtain ⟨P, M, U, A, _, _, _, _, p, _, iU, l, _, a, r, _, _, _, hA, hT, hU, hK, n, e, k, v, c,
    E, D, hv, hc, himag, hmero, hreg, rfl⟩ := hΘ
  have hE : ∀ j, Continuous fun q : (Fin n → ℝ) × AdelicGroupPoints F G =>
      E j (imaginaryParameter F P (e q.1)) q.2 := fun j =>
    hcont F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc (v j) hKmax hrho (hv j)
      (E j) D himag (hmero j) (hreg j) n e
  have hctop : (ENNReal.ofReal (2 * Real.pi))⁻¹ ^ n ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by positivity)).ne')
  have : IsFiniteMeasureOnCompacts (spectralMeasure n) :=
    IsFiniteMeasureOnCompacts.smul (volume : Measure (Fin n → ℝ)) hctop
  refine continuous_integral_of_forall_notMem_eq_zero (spectralMeasure n)
    (f := fun g x => ∑ j, c j x * E j (imaginaryParameter F P (e x)) g)
    (s := ⋃ j, tsupport (c j)) ?_ (isCompact_iUnion fun j => (hc j).2) ?_
  · refine continuous_finsetSum _ fun j _ => ?_
    exact ((hc j).1.continuous.comp continuous_snd).mul ((hE j).comp continuous_swap)
  · intro g x hx
    refine Finset.sum_eq_zero fun j _ => ?_
    have hxj : x ∉ tsupport (c j) := fun h => hx (Set.mem_iUnion.2 ⟨j, h⟩)
    rw [image_eq_zero_of_notMem_tsupport hxj, zero_mul]

end Continuity

section Invariance

/-- **Left `G(F)`-invariance of wave packets.** Each continuation `E j` is left
`G(F)`-invariant at every parameter of its domain of holomorphy
(`eisensteinContinuation_leftRationalInvariant`), and the coefficients are integrated against
parameters in that domain (`packetIntegral_leftRationalInvariant`). -/
theorem IsWavePacket.leftRationalInvariant
    {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
    {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth} {Θ : AdelicGroupPoints F G → ℂ}
    (hΘ : IsWavePacket F G K rho hsmooth hcalc Θ) :
    ∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G, Θ (q * g) = Θ g := by
  obtain ⟨P, M, U, A, _, _, _, _, p, _, iU, l, _, a, r, _, _, _, hA, hT, hU, hK, n, e, k, v, c,
    E, D, hv, -, himag, hmero, hreg, rfl⟩ := hΘ
  exact packetIntegral_leftRationalInvariant (spectralMeasure n)
    (fun x => imaginaryParameter F P (e x)) c E (fun _ x _ => himag ⟨e x, rfl⟩)
    (fun j _ hlam => eisensteinContinuation_leftRationalInvariant hK (hv j).1.1 hU r hA hT hG
      (hmero j) (hreg j) hlam)

end Invariance

section SiegelPoints

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  {ν : cocharacterLattice T} {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ T}

/-- For a closed matrix embedding, the conjugates `a⁻¹ n a` of a compact set of points `n` of the
standard unipotent subgroup by the points `a` of a weak simple-root chamber lie in one compact
set (Delorme 2023, (2.4)): their heights are bounded (`exists_adelicHeight_conj_unipotent_le`)
and height sublevels are compact (`isCompact_adelicHeightSublevel`). -/
theorem exists_isCompact_conj_unipotent (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hrho : IsClosedSubgroup rho)
    (Ω : Set (AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))) (hΩ : IsCompact Ω)
    (t : ℝ≥0ˣ) :
    ∃ S : Set (AdelicGroupPoints F G), IsCompact S ∧ ∀ n ∈ Ω,
      ∀ a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t,
        (positiveMap F G T i T₀ j a)⁻¹ *
          map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
          positiveMap F G T i T₀ j a ∈ S := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (AdelicGroupPoints F G) :=
      ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
        (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
    exact ⟨Set.univ, Set.subsingleton_univ.isCompact, fun _ _ _ _ => Set.mem_univ _⟩
  · obtain ⟨B, hB⟩ := exists_adelicHeight_conj_unipotent_le F G T i ν T₀ j hG hsetup rho hN Ω hΩ t
    exact ⟨RepresentationGrowth.adelicHeightSublevel F G rho B,
      RepresentationGrowth.isCompact_adelicHeightSublevel F G rho hN hrho B,
      fun n hn a ha => hB n hn a ha⟩

/-- **Siegel points from chamber points.** A point `x = z · (n m a k) · w` of the Siegel set
`A_G · Ω_N Ω_M A_{T₀}(t) K_C · Ω` equals `z · a · ω` with
`ω = (a⁻¹ n a) m k w` in the compact set `S · Ω_M · K_C · Ω`, where `S` contains the
conjugates `a⁻¹ Ω_N a` (`exists_isCompact_conj_unipotent`) and `m` commutes with `a` because
the standard Levi is the centralizer of the torus. Hence the chamber estimate for that compact
set gives the Siegel-set estimate. -/
theorem siegelPoint_bound_of_chamber_bound (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hrho : IsClosedSubgroup rho)
    {Θ : AdelicGroupPoints F G → ℂ}
    (hchamber : ∀ (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
      ∀ n : ℕ, ∃ B : ℝ, ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
        ∀ a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t, ∀ ω ∈ Ω,
          ‖Θ (z * positiveMap F G T i T₀ j a * ω)‖ ≤
            B * Real.sqrt (siegelModulus F G T i ν T₀ j a) /
              adelicLogHeight F G rho (z * positiveMap F G T i T₀ j a * ω) ^ n)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)) (hΩ : IsCompact Ω) (n : ℕ) :
    ∃ B : ℝ, ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G),
      IsSiegelPoint F G T i ν T₀ j C t Ω a x →
        ‖Θ x‖ ≤ B * Real.sqrt (siegelModulus F G T i ν T₀ j a) /
          adelicLogHeight F G rho x ^ n := by
  have hlevi : standardLevi i ν ∅ = torusCentralizer i := hsetup.2.2.2.2.2.1
  obtain ⟨S, hS, hSmem⟩ :=
    exists_isCompact_conj_unipotent hG hsetup rho hrho C.omegaN C.compact_omegaN t
  let ιN := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅)
  let ιM : normOneSubgroup F (Standard.leviScheme i ν ∅) → AdelicGroupPoints F G :=
    fun m => map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m
  have hιM : Continuous ιM :=
    (map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅)).continuous.comp
      continuous_subtype_val
  let Ω' : Set (AdelicGroupPoints F G) :=
    S * (ιM '' C.omegaM) * (C.compactSubgroup : Set (AdelicGroupPoints F G)) * Ω
  have hΩ' : IsCompact Ω' :=
    ((hS.mul (C.compact_omegaM.image hιM)).mul C.compact_compactSubgroup).mul hΩ
  obtain ⟨B, hB⟩ := hchamber t Ω' hΩ' n
  refine ⟨B, fun a x hx => ?_⟩
  obtain ⟨z, hz, n', hn', m, hm, ha, k, hk, w, hw, rfl⟩ := hx
  set A := positiveMap F G T i T₀ j a with hA
  have hcomm : Commute (ιM m) A :=
    commute_of_mem_standardLevi_image F G T i ν T₀ j hlevi (CommAlgCat.of F (Adeles F))
      (ιM m) ⟨m.val, rfl⟩ a.val
  have hx : z * (ιN n' * ιM m * A * k) * w = z * A * (A⁻¹ * ιN n' * A * ιM m * k * w) := by
    calc z * (ιN n' * ιM m * A * k) * w = z * (ιN n' * (ιM m * A) * k) * w := by
          simp only [mul_assoc]
      _ = z * (ιN n' * (A * ιM m) * k) * w := by rw [hcomm.eq]
      _ = z * A * (A⁻¹ * ιN n' * A * ιM m * k * w) := by group
  have hω : A⁻¹ * ιN n' * A * ιM m * k * w ∈ Ω' :=
    Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (hSmem n' hn' a ha) ⟨m, hm, rfl⟩) hk) hw
  change ‖Θ (z * (ιN n' * ιM m * A * k) * w)‖ ≤ _ / adelicLogHeight F G rho
    (z * (ιN n' * ιM m * A * k) * w) ^ n
  rw [hx]
  exact hB z hz a ha _ hω

end SiegelPoints

/-- **Reduction.** `EisensteinImaginaryJointContinuityStatement` and
`WavePacketChamberDecayStatement` imply `WavePacketSiegelDecayStatement`. -/
theorem wavePacketSiegelDecay_of_reduction
    (hcont : EisensteinImaginaryJointContinuityStatement)
    (hchamber : WavePacketChamberDecayStatement) : WavePacketSiegelDecayStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho hP₀ Θ hΘ
  refine ⟨hΘ.continuous_of_jointContinuity hcont hG hKmax hrho,
    hΘ.leftRationalInvariant hG, ?_⟩
  intro T i ν T₀ j hsetup C t Ω hΩ n
  exact siegelPoint_bound_of_chamber_bound hG hsetup rho hrho
    (hchamber F G hG K rho hsmooth hcalc hKmax hrho hP₀ Θ hΘ T i ν T₀ j hsetup) C t Ω hΩ n

end Langlands.Global
