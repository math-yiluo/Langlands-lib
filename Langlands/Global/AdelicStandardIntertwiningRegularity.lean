import Langlands.Global.AdelicStandardFamilyPresentation
import Langlands.Global.AdelicIntertwiningAutomorphyReduction
import Langlands.Global.AdelicIntertwiningConvergenceProof
import Langlands.Global.AdelicHeightPowerPolynomialBound
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness

/-! # Invariance, continuity and growth of regular intertwining integrals of a standard family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Aubert.General.RationalPointFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (I Q : StandardIndex F G fam.i fam.ν)
  [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
  [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
  [IsClosedImmersion (fam.p Q).hom.hom.left]

/-- **Regular intertwining integrals of a standard family.** For an automorphic form `φ` on
`U_I(𝔸) M_I(F) \ G(𝔸)` and a Weyl conjugation `(n, c)` from `P_I` to `P_Q`, there is a
threshold beyond which the intertwining integral `M(w, λ)φ` twisted back at `wλ`, that is
the integral `∫ φ_λ(n⁻¹ v g) dv` over `(V(F) ∩ nU(𝔸)n⁻¹) \ U_Q(𝔸)`, is left invariant under
`U_Q(𝔸) M_Q(F)`, continuous and of moderate growth. -/
theorem exists_intertwiningIntegral_regular {N₀ : ℕ} (hN : 0 < N₀)
    (n : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M I) (proj : fam.P Q ⟶ fam.M Q)
    (hproj : fam.l Q ≫ proj = 𝟙 (fam.M Q))
    (hc : IsWeylConjugation (fam.p I) (fam.l I) (fam.p Q) (fam.l Q) n.val c)
    {K : Subgroup (AdelicGroupPoints F G)} (hKI : IsIwasawaCompact (fam.p I) K)
    (hKQ : IsIwasawaCompact (fam.p Q) K) (hKmax : IsMaximalCompactSubgroup F G K)
    {d : ℕ} (rho : MatrixRepresentation G (Fin N₀)) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ)
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc
      (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I))
      (K.comap (ofInfinite F G).toMonoidHom) rho φ) :
    ∃ R₀ : ℝ, ∀ lam, (fam.standardPresentation I).IsRegularParameter
        (fam.isSplitTorus_splitComponent I) fam.isSplitTorus_torus R₀ lam →
      IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p Q) (fam.iU Q) (fam.l Q))
          (hKI.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam) ∧
        Continuous (hKI.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam) ∧
        HasModerateGrowthFunction F G rho
          (hKI.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam) := by
  let rI := fam.standardPresentation I
  let rQ := fam.standardPresentation Q
  let hAI := fam.isSplitTorus_splitComponent I
  let hT := fam.isSplitTorus_torus
  let : IsAffine (fam.P I).X.left := isAffine_of_isAffineHom (fam.p I).hom.hom.left
  let : IsAffine (fam.P Q).X.left := isAffine_of_isAffineHom (fam.p Q).hom.hom.left
  let : IsClosedImmersion (fam.iU Q).hom.hom.left :=
    (fam.isUnipotentRadical Q).1.isClosedSubgroup
  let : IsAffine (fam.U Q).X.left := isAffine_of_isAffineHom (fam.iU Q).hom.hom.left
  let : Smooth G.X.hom := fam.connectedReductive.smooth
  have hmul : IsIso (subgroupMultiplication (fam.l Q) (fam.iU Q)) :=
    ParabolicRootPresentation.isIso_subgroupMultiplication_of_radical rQ (fam.isUnipotentRadical Q)
  have hG := fam.connectedReductive
  have hU := fam.isUnipotentRadical I
  have hV := fam.isUnipotentRadical Q
  have hq := (fam.isCompatible Q).parabolic
  have hl' := (fam.isCompatible Q).levi
  obtain ⟨R₃, hR₃⟩ := intertwiningModerateGrowth F G (fam.P I) (fam.M I) (fam.U I) (fam.P Q)
    (fam.M Q) (fam.U Q) (fam.A I) (fam.p I) (fam.iU I) (fam.l I) (fam.a I) rI hAI hT (fam.p Q)
    (fam.iU Q) (fam.l Q) proj n.val c hG hU hq hV hl' hmul hproj hc K hKI hKQ rho hsmooth hcalc
    φ hKmax hrho hφ
  obtain ⟨R₄, hR₄⟩ := intertwiningAbsoluteConvergence F G (fam.P I) (fam.M I) (fam.U I) (fam.P Q)
    (fam.M Q) (fam.U Q) (fam.A I) (fam.p I) (fam.iU I) (fam.l I) (fam.a I) rI hAI hT (fam.p Q)
    (fam.iU Q) (fam.l Q) n.val c hG hU hq hV hl' hmul hc K hKI rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨m, ⟨e⟩⟩ := exists_complexParameterEquiv hG rI.isCompatible.parabolic
  refine ⟨max R₃ R₄, fun lam hlam => ?_⟩
  have h₃ : rI.IsRegularParameter hAI hT R₃ lam :=
    fun α hα => (le_max_left _ _).trans_lt (hlam α hα)
  have h₄ : rI.IsRegularParameter hAI hT R₄ lam :=
    fun α hα => (le_max_right _ _).trans_lt (hlam α hα)
  have hφU : IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I) (fam.iU I)) φ :=
    fun x hx g => hφ.1 x (Subgroup.mem_sup_left hx) g
  -- left invariance under `U_Q(𝔸)` and `M_Q(F)`
  have hleft : IsLeftInvariantUnder F G
      (parabolicQuotientSubgroup F (fam.p Q) (fam.iU Q) (fam.l Q))
      (hKI.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam) := by
    apply isLeftInvariantUnder_sup
    · rintro _ ⟨v, rfl⟩ g
      have hmem : map F (fam.U Q) G (fam.iU Q ≫ fam.p Q) v ∈
          AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (fam.iU Q ≫ fam.p Q)) := by
        change _ ∈ parabolicUnipotentImage F (fam.p Q) (fam.iU Q)
        exact ⟨v, rfl⟩
      exact hKI.intertwiningIntegral_radical_mul (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val
        hV.1.smooth hV.1.connectedSpace hV.1.isUnipotent hU.1.isUnipotent hφU lam ⟨_, hmem⟩ g
    · rintro _ ⟨m₀, rfl⟩ g
      exact hKI.intertwiningIntegral_levi_rational_mul hc hU rI.isCompatible.levi hV hφ.1 lam m₀ g
  -- continuity
  have hcontI : Continuous (hKI.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam) := by
    refine hKI.continuous_intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val
      hU.1.isUnipotent hφU hφ.2.1.1 lam (fun C hC => ?_)
    have hsingle : ∀ s ∈ ({e.symm lam} : Set (Fin m → ℂ)),
        rI.IsRegularParameter hAI hT R₄ (e s) := by
      intro s hs
      rw [Set.mem_singleton_iff.mp hs, e.apply_symm_apply]
      exact h₄
    obtain ⟨b, hb, hbound⟩ := hR₄ C hC m e {e.symm lam} isCompact_singleton hsingle
    exact ⟨b, hb, fun x g hg => by
      simpa only [e.apply_symm_apply] using hbound x g hg (e.symm lam) (Set.mem_singleton _)⟩
  -- moderate growth
  have hgrowth : HasModerateGrowthFunction F G rho
      (hKI.intertwiningIntegral (fam.iU I) (fam.iU Q ≫ fam.p Q) n.val φ lam) := by
    obtain ⟨C, hC, r, hT'⟩ := hR₃ lam h₃
    let mu := weylParameter (fam.l I) c proj lam
    obtain ⟨C', e', hC', he', hH⟩ := hKQ.exists_norm_heightPower_le_adelicHeight rho hN hrho mu
    let s : ℝ := (N₀ : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
    have hs : 0 < s := pow_pos (by exact_mod_cast hN) _
    refine ⟨C * C' * s ^ e', by positivity, r + e', fun g => ?_⟩
    have hpos := RepresentationGrowth.adelicSourceNorm_pos F G rho hN g
    rw [fam.intertwiningIntegral_eq_parameterTwist hKI hKQ c proj n.val φ lam]
    simp only [IsIwasawaCompact.parameterTwist, norm_mul]
    have hHg : RepresentationGrowth.adelicHeight F G rho g ^ e' =
        s ^ e' * RepresentationGrowth.adelicSourceNorm F G rho g ^ e' := by
      rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho g]
      exact Real.mul_rpow hs.le hpos.le
    calc
      _ ≤ (C * RepresentationGrowth.adelicSourceNorm F G rho g ^ r) *
          (C' * RepresentationGrowth.adelicHeight F G rho g ^ e') :=
        mul_le_mul (hT' g) (hH g) (norm_nonneg _) (by positivity)
      _ = C * C' * s ^ e' * RepresentationGrowth.adelicSourceNorm F G rho g ^ (r + e') := by
        rw [hHg, Real.rpow_add hpos]
        ring
  exact ⟨hleft, hcontI, hgrowth⟩

end Langlands.Global.StandardParabolicFamily
