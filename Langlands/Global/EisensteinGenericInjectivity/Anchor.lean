import Langlands.Global.EisensteinGenericInjectivity.AnchorBasics
import Langlands.Global.EisensteinGenericInjectivity.Separation
import Langlands.Global.EisensteinGenericInjectivity.Cesaro
import Langlands.Global.EisensteinGenericInjectivity.ProductTsum
import Langlands.Global.AdelicEisensteinRationalCosets
import Langlands.Analysis.Meromorphic.LocalScalarization
import Langlands.Analysis.HolomorphicFiniteRank
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # A regular parameter at which Eisenstein series of independent forms are independent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Filter Topology
open scoped CategoryTheory.MonObj TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Global.EisensteinGenericInjectivity

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- Height is unchanged by the chosen representative of the trivial coset. -/
theorem height_out_one_mul (hK : IsIwasawaCompact p K) (g : AdelicGroupPoints F G) :
    hK.height (((Quotient.out (Quotient.mk _ (1 : rationalSubgroup F G) :
      ParabolicRationalCosets F p) : rationalSubgroup F G) : AdelicGroupPoints F G) * g) =
      hK.height g := by
  set o := Quotient.out (Quotient.mk _ (1 : rationalSubgroup F G) : ParabolicRationalCosets F p)
  have h : (Quotient.mk _ o : ParabolicRationalCosets F p) = Quotient.mk _ 1 := Quotient.out_eq _
  have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
  rw [one_mul] at hr
  obtain ⟨_, ⟨q, rfl⟩, hq⟩ := Subgroup.mem_subgroupOf.mp hr
  have ho : (o : AdelicGroupPoints F G) = map F P G p (rational F P q⁻¹) := by
    rw [map_inv, map_inv]
    change map F P G p (rational F P q) = ((o⁻¹ : rationalSubgroup F G) : AdelicGroupPoints F G)
      at hq
    rw [hq]
    simp
  rw [ho, hK.height_rational_mul]

section Main

variable {M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

/-- **Anchor.** For linearly independent automorphic forms with compact-uniform summable
majorants on `R`-regular parameters, every nonempty open set of `R`-regular parameters (in
coordinates) contains a parameter and evaluation points at which the matrix of actual
Eisenstein series values is invertible. -/
theorem exists_regular_det_ne_zero (hG : IsConnectedReductive G)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hK : IsIwasawaCompact p K)
    {m : ℕ} (ψ : Fin m → AdelicGroupPoints F G → ℂ) (hcont : ∀ k, Continuous (ψ k))
    (hinv : ∀ k, IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) (ψ k))
    (hind : LinearIndependent ℂ ψ) (R : ℝ)
    (hconv : ∀ k, ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
        (Λ : Set (Fin n → ℂ)), IsCompact Λ →
        (∀ s ∈ Λ, r.IsRegularParameter hA hT R (e s)) →
        ∃ b : ParabolicRationalCosets F p → ℝ, Summable b ∧
          ∀ c, ∀ g ∈ C, ∀ s ∈ Λ, ‖hK.eisensteinTerm (ψ k) (e s) g c‖ ≤ b c)
    {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) {W : Set (Fin n → ℂ)}
    (hWo : IsOpen W) (hWne : W.Nonempty)
    (hWreg : ∀ s ∈ W, r.IsRegularParameter hA hT R (e s)) :
    ∃ s ∈ W, ∃ g : Fin m → AdelicGroupPoints F G,
      (Matrix.of fun i k => hK.eisensteinSeries (ψ k) (e s) (g i)).det ≠ 0 := by
  classical
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨g₀, hg₀⟩ := Langlands.Analysis.exists_profileMatrix_det_ne_zero ψ hind
  obtain ⟨χ, hsep⟩ := frequency_separation r hA hG hK
  set c := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p with hc_def
  have hray : Continuous (ray F c) := continuous_ray c
  let D0 : ℝ → ℂ := fun s => (Matrix.of fun i k => ψ k (ray F c s * g₀ i)).det
  have hD0 : Continuous D0 := by
    apply Continuous.matrix_det
    refine continuous_pi fun i => continuous_pi fun k => ?_
    exact (hcont k).comp (hray.mul continuous_const)
  have hD00 : D0 0 ≠ 0 := by simpa [D0, ray_zero, Langlands.Analysis.profileMatrix] using hg₀
  let c₀ : Fin m → ParabolicRationalCosets F p := fun _ => Quotient.mk _ 1
  let bad : Set ℝ := ⋃ cs : {cs : Fin m → ParabolicRationalCosets F p // cs ≠ c₀},
    {s : ℝ | ∑ k, hK.height (((Quotient.out (cs.1 k) : rationalSubgroup F G) :
        AdelicGroupPoints F G) * (ray F c s * g₀ k)) χ =
      ∑ k, hK.height (ray F c s * g₀ k) χ}
  have hbad : bad.Countable := Set.countable_iUnion fun cs => (hsep m g₀ cs.1 cs.2).countable
  obtain ⟨s₀, hs₀D, hs₀bad⟩ : ∃ s₀, D0 s₀ ≠ 0 ∧ s₀ ∉ bad := by
    have hopen : IsOpen {s : ℝ | D0 s ≠ 0} := isOpen_ne_fun hD0 continuous_const
    obtain ⟨s₀, hs₀, hs₀'⟩ := (hbad.dense_compl ℝ).inter_open_nonempty _ hopen ⟨0, hD00⟩
    exact ⟨s₀, hs₀, hs₀'⟩
  let g : Fin m → AdelicGroupPoints F G := fun i => ray F c s₀ * g₀ i
  obtain ⟨sW, hsW⟩ := hWne
  let lam0 := e sW
  let mu : ComplexCharacterParameter F P := (1 : ℂ) ⊗ₜ[ℤ] χ
  let v := e.symm mu
  have hline : ∀ z : ℂ, e (sW + z • v) = lam0 + z • mu := fun z => by
    simp [v, lam0, map_add, map_smul]
  have hcontL : Continuous fun t : ℝ => sW + (t : ℂ) • v :=
    continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  obtain ⟨ε, hε, hεW⟩ : ∃ ε > 0, ∀ t : ℝ, |t| < ε → sW + (t : ℂ) • v ∈ W := by
    have hmem : (fun t : ℝ => sW + (t : ℂ) • v) ⁻¹' W ∈ 𝓝 (0 : ℝ) :=
      hcontL.continuousAt.preimage_mem_nhds (by simpa using hWo.mem_nhds hsW)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨ε, hε, fun t ht => hball (by simpa [Real.dist_eq] using ht)⟩
  let S : Set ℂ := Complex.re ⁻¹' Set.Ioo (-ε) ε
  have hSo : IsOpen S := isOpen_Ioo.preimage Complex.continuous_re
  have hSc : IsPreconnected S :=
    ((convex_Ioo (-ε) ε).linear_preimage Complex.reLm).isPreconnected
  have hSreg : ∀ z ∈ S, r.IsRegularParameter hA hT R (e (sW + z • v)) := by
    intro z hz
    rw [hline, isRegularParameter_add_smul_iff r hA hT, ← hline]
    exact hWreg _ (hεW z.re (abs_lt.mpr hz))
  let f : ℂ → ℂ := fun z =>
    (Matrix.of fun i k => hK.eisensteinSeries (ψ k) (e (sW + z • v)) (g i)).det
  have hfd : DifferentiableOn ℂ f S := by
    refine mdifferentiableOn_iff_differentiableOn.mp
      (Langlands.Analysis.Meromorphic.mdifferentiableOn_det (A := fun z => Matrix.of fun i k =>
        hK.eisensteinSeries (ψ k) (e (sW + z • v)) (g i)) fun i k => ?_)
    exact mdifferentiableOn_iff_differentiableOn.mpr
      (differentiableOn_eisensteinSeries_line r hA hT hK R (ψ k) (hconv k) e sW v hSo hSreg (g i))
  let T : Fin m → Fin m → ParabolicRationalCosets F p → ℂ := fun i k c' =>
    hK.eisensteinTerm (ψ k) lam0 (g i) c'
  let H : Fin m → ParabolicRationalCosets F p → ℝ := fun i c' =>
    hK.height (((Quotient.out c' : rationalSubgroup F G) : AdelicGroupPoints F G) * g i) χ
  have hTsum : ∀ i k, Summable fun c' => ‖T i k c'‖ := by
    intro i k
    obtain ⟨b, hb, hbd⟩ := hconv k {g i} isCompact_singleton n e {sW} isCompact_singleton
      (by simpa using hWreg sW hsW)
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun c' => hbd c' (g i) rfl sW rfl) hb
  let θ : (Fin m → ParabolicRationalCosets F p) → ℝ := fun cs => ∑ i, H i (cs i)
  let Bc : (Fin m → ParabolicRationalCosets F p) → ℂ := fun cs =>
    (Matrix.of fun i k => T i k (cs i)).det
  have hnorm_exp : ∀ a b : ℝ, ‖Complex.exp (Complex.I * ((a : ℂ) * (b : ℂ)))‖ = 1 :=
    fun a b => by
      rw [Complex.norm_exp]
      simp
  have hfy : ∀ y : ℝ, f ((y : ℂ) * Complex.I) =
      ∑' cs, Bc cs * Complex.exp (Complex.I * ((y * θ cs : ℝ) : ℂ)) := by
    intro y
    have hser : ∀ i k, hK.eisensteinSeries (ψ k) (e (sW + ((y : ℂ) * Complex.I) • v)) (g i) =
        ∑' c', T i k c' * Complex.exp (Complex.I * ((y * H i c' : ℝ) : ℂ)) := by
      intro i k
      rw [hline]
      simp only [IsIwasawaCompact.eisensteinSeries]
      refine tsum_congr fun c' => ?_
      rw [eisensteinTerm_add_smul]
      congr 2
      push_cast
      ring
    simp only [f]
    simp_rw [hser]
    rw [det_tsum _ fun i k => by simpa [norm_mul, hnorm_exp] using hTsum i k]
    refine tsum_congr fun cs => ?_
    rw [show (Matrix.of fun i k => T i k (cs i) *
        Complex.exp (Complex.I * ((y * H i (cs i) : ℝ) : ℂ))) =
        Matrix.of fun i k => Complex.exp (Complex.I * ((y * H i (cs i) : ℝ) : ℂ)) *
          (Matrix.of fun i k => T i k (cs i)) i k by
      ext i k
      simp [mul_comm], Matrix.det_mul_column, ← Complex.exp_sum, mul_comm]
    congr 2
    simp only [θ, Finset.mul_sum]
    push_cast
    rw [Finset.mul_sum]
  have hBsum : Summable fun cs => ‖Bc cs‖ := summable_norm_det_pi T hTsum
  have hθ0 : θ c₀ = ∑ k, hK.height (ray F c s₀ * g₀ k) χ := by
    simp only [θ, H, c₀, g]
    exact Finset.sum_congr rfl fun k _ => by rw [height_out_one_mul]
  have hθ : ∀ cs, cs ≠ c₀ → θ cs ≠ θ c₀ := by
    intro cs hcs heq
    apply hs₀bad
    refine Set.mem_iUnion.mpr ⟨⟨cs, hcs⟩, ?_⟩
    change θ cs = ∑ k, hK.height (ray F c s₀ * g₀ k) χ
    rw [← hθ0]
    exact heq
  have hB0 : Bc c₀ ≠ 0 := by
    have hT0 : ∀ i k, T i k (Quotient.mk _ 1) = hK.heightPower lam0 (g i) * ψ k (g i) := by
      intro i k
      change hK.eisensteinTerm (ψ k) lam0 (g i) (Quotient.mk _ 1) = _
      rw [hK.eisensteinTerm_eq_of_representative (hinv k) r.isCompatible.levi hU lam0 (g i) _ 1
        rfl]
      simp [IsIwasawaCompact.parameterTwist, mul_comm]
    have hBc : Bc c₀ = (∏ i, hK.heightPower lam0 (g i)) * D0 s₀ := by
      change (Matrix.of fun i k => T i k (Quotient.mk _ 1)).det =
        (∏ i, hK.heightPower lam0 (g i)) * (Matrix.of fun i k => ψ k (g i)).det
      rw [← Matrix.det_mul_column]
      congr 1
      ext i k
      simp only [Matrix.of_apply, hT0]
    rw [hBc]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Complex.exp_ne_zero _) hs₀D
  obtain ⟨τ, m', hne⟩ := exists_shift_tsum_ne_zero hBsum hθ hB0
  have hfy0 : f (((m' : ℝ) * τ : ℝ) * Complex.I) ≠ 0 := by
    rw [hfy]
    exact hne
  have hz₁ : ((((m' : ℝ) * τ : ℝ) : ℂ) * Complex.I) ∈ S := by
    simp [S, hε]
  have h0S : (0 : ℂ) ∈ S := by simp [S, hε]
  have hfa : AnalyticOnNhd ℂ f S := hfd.analyticOnNhd hSo
  by_contra hall
  push Not at hall
  have hev : f =ᶠ[𝓝 0] 0 := by
    have hU' : {z : ℂ | sW + z • v ∈ W} ∈ 𝓝 (0 : ℂ) :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.preimage_mem_nhds
        (by simpa using hWo.mem_nhds hsW)
    filter_upwards [hU'] with z hz
    exact hall _ hz g
  exact hfy0 (hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hSc h0S hev hz₁)

end Main

end Langlands.Global.EisensteinGenericInjectivity
