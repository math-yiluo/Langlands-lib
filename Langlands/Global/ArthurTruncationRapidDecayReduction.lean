import Langlands.Global.ArthurTruncationRapidDecayStatement
import Langlands.Automorphic.GroupSchemeNormOneAtlas

/-! # Reduction of Arthur's Proposition 13.2 on `G(F) \ G(𝔸_F)¹`

Arthur 2005, Proposition 13.2(a),(b) and (13.5)–(13.6); Arthur 1980, Lemma 1.4. The target
`TruncationRapidDecayStatement` follows from `NormOneTruncationFamilyEstimateStatement`, stated
here: for every embedded Lie atlas on `G(F∞)¹` there is a suitable maximal compact subgroup `K`
for which the fixed-level family estimate (13.5)–(13.6) holds. The embedded atlas itself is
`exists_normOneLieAtlas`.

Part (a) of the proposition is derived from part (b): a uniformly tempered function is the
constant family over a one-point measure space. -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ContDiff ENNReal

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces
open Langlands.Automorphic.GroupSchemeFunctions AdelicSiegelFactors

set_option backward.isDefEq.respectTransparency false

section Estimate

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {d e N : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}

/-- **Arthur 2005, (13.5)–(13.6); Arthur 1980, Lemma 1.4.** The fixed-level family estimate
for given atlas, height, compact and truncation parameter: the second conjunct of
`IsNormOneTruncationEstimate`. -/
def IsNormOneFamilyEstimate (A : NormOneLieAtlas F G hsmooth e)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) (rho : MatrixRepresentation G (Fin N))
    (Tp : V T) : Prop :=
  ∀ C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅),
    C.compactSubgroup = K → ∀ (T₁ : V T) (n n₀ : ℕ), 0 < n → 0 < n₀ →
    ∀ (K₀ : Subgroup (FiniteAdelicGroupPoints F G))
      (hc : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))),
      IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G)) →
      ∃ (r : ℕ) (ops : Finset (NormOneDifferentialWord e)) (B : NNReal),
        0 < r ∧ (∀ X ∈ ops, X.OrderLE r) ∧
        ∀ (Ω : Type v) [MeasurableSpace Ω] (m : Measure Ω)
          (φ : Ω → normOneSubgroup F G → ℂ),
          (∀ o, IsNormOneCr A r K₀ hc (φ o)) →
          Measurable (fun p : Ω × normOneSubgroup F G => φ p.1 p.2) →
          ∀ x : normOneSubgroup F G, (x : AdelicGroupPoints F G) ∈
              siegelSet hi hK hρ C (simpleFinset ν hG hi) T₁ →
            Measurable (fun o => normOneTruncation hG hi D hK hρ Tp (φ o) x) ∧
            ENNReal.ofReal (RepresentationGrowth.adelicSourceNorm F G rho x ^ (n : ℝ)) *
                (∫⁻ o, ENNReal.ofReal ‖normOneTruncation hG hi D hK hρ Tp (φ o) x‖ ∂m) ≤
              (B : ℝ≥0∞) * ⨆ y : normOneSubgroup F G,
                ENNReal.ofReal (RepresentationGrowth.adelicSourceNorm F G rho y ^ (-(n₀ : ℝ))) *
                  ∑ X ∈ ops, ∫⁻ o, ENNReal.ofReal ‖normOneDifferential A X (φ o) y‖ ∂m

/-- The two parts of `IsNormOneTruncationEstimate`: rapid decrease of uniformly tempered
inputs and the family estimate. -/
theorem isNormOneTruncationEstimate_iff (A : NormOneLieAtlas F G hsmooth e)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) (rho : MatrixRepresentation G (Fin N))
    (Tp : V T) :
    IsNormOneTruncationEstimate.{u, v} A hG hi D hK hρ rho Tp ↔
      (∀ f : normOneSubgroup F G → ℂ, IsNormOneUniformlyTempered A rho f →
        IsRapidlyDecreasing hG hi hK hρ rho
          (normOneExtend (normOneTruncation hG hi D hK hρ Tp f))) ∧
        IsNormOneFamilyEstimate.{u, v} A hG hi D hK hρ rho Tp :=
  Iff.rfl

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The closed-representation height is bounded below by a positive constant. -/
theorem exists_pos_le_adelicSourceNorm (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ g : AdelicGroupPoints F G,
      c₀ ≤ RepresentationGrowth.adelicSourceNorm F G rho g := by
  have hNpos : (0 : ℝ) < (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult) :=
    pow_pos (Nat.cast_pos.2 hN) _
  refine ⟨((N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult))⁻¹, inv_pos.2 hNpos,
    fun g => ?_⟩
  have h1 := RepresentationGrowth.one_le_adelicHeight F G rho hN g
  rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm] at h1
  rw [inv_le_iff_one_le_mul₀' hNpos]
  exact h1

/-- **Part (a) from part (b).** If the family estimate holds, every smooth uniformly tempered
function on `G(𝔸_F)¹` has rapidly decreasing truncation on every Siegel set. Apply the
estimate to the constant family over a one-point measure space with `n + 1` and an
exponent `n₀ > p`; the right side is then bounded, because `H(y)^{p - n₀}` is bounded on
`G(𝔸_F)¹`. -/
theorem isRapidlyDecreasing_of_isNormOneFamilyEstimate (A : NormOneLieAtlas F G hsmooth e)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) (Tp : V T)
    (hfam : IsNormOneFamilyEstimate.{u, v} A hG hi D hK hρ rho Tp)
    (f : normOneSubgroup F G → ℂ) (hf : IsNormOneUniformlyTempered A rho f) :
    IsRapidlyDecreasing hG hi hK hρ rho
      (normOneExtend (normOneTruncation hG hi D hK hρ Tp f)) := by
  let := A.chartedSpace
  obtain ⟨⟨K₀, hc, hopen, hcr⟩, p, hp, hbound⟩ := hf
  choose Bw hBw0 hBw using hbound
  obtain ⟨c₀, hc₀, hc₀le⟩ := exists_pos_le_adelicSourceNorm (F := F) (G := G) rho hN
  intro C hC T₁ n
  -- the exponent `n₀ > p`
  set n₀ : ℕ := ⌈p⌉₊ + 1 with hn₀
  have hpn₀ : p - (n₀ : ℝ) ≤ 0 := by
    have := Nat.le_ceil p
    rw [hn₀]
    push_cast
    linarith
  obtain ⟨r, ops, B, -, -, hest⟩ :=
    hfam C hC T₁ (n + 1) n₀ n.succ_pos (Nat.succ_pos _) K₀ hc hopen
  -- the uniform bound of the right side
  set M : ℝ := (∑ X ∈ ops, Bw X) * c₀ ^ (p - (n₀ : ℝ)) with hM
  have hM0 : 0 ≤ M :=
    mul_nonneg (Finset.sum_nonneg fun X _ => hBw0 X) (Real.rpow_nonneg hc₀.le _)
  have hcr' : ∀ _o : PUnit.{v + 1}, IsNormOneCr A r K₀ hc f := fun _ =>
    ⟨hcr.1, hcr.2.1, fun x => (hcr.2.2 x).of_le (by exact_mod_cast le_top)⟩
  have hcont : Continuous f := continuous_of_isNormOneCr A hopen hcr
  have hmeas : Measurable (fun q : PUnit.{v + 1} × normOneSubgroup F G => f q.2) :=
    hcont.measurable.comp measurable_snd
  refine ⟨B * M * c₀⁻¹, fun x hxS hx1 => ?_⟩
  obtain ⟨-, hineq⟩ := hest PUnit.{v + 1} (Measure.dirac PUnit.unit) (fun _ => f) hcr' hmeas
    ⟨x, hx1⟩ hxS
  simp only [lintegral_dirac] at hineq
  set H : AdelicGroupPoints F G → ℝ := RepresentationGrowth.adelicSourceNorm F G rho with hH
  -- bound the supremum
  have hsup : (⨆ y : normOneSubgroup F G,
      ENNReal.ofReal (H y ^ (-(n₀ : ℝ))) *
        ∑ X ∈ ops, ENNReal.ofReal ‖normOneDifferential A X f y‖) ≤ ENNReal.ofReal M := by
    refine iSup_le fun y => ?_
    have hy0 : 0 < H y := lt_of_lt_of_le hc₀ (hc₀le y)
    have hterm : ∀ X ∈ ops, ENNReal.ofReal (H y ^ (-(n₀ : ℝ))) *
        ENNReal.ofReal ‖normOneDifferential A X f y‖ ≤
          ENNReal.ofReal (Bw X * c₀ ^ (p - (n₀ : ℝ))) := by
      intro X _
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc H y ^ (-(n₀ : ℝ)) * ‖normOneDifferential A X f y‖
          ≤ H y ^ (-(n₀ : ℝ)) * (Bw X * H y ^ p) :=
            mul_le_mul_of_nonneg_left (hBw X y) (Real.rpow_nonneg hy0.le _)
        _ = Bw X * H y ^ (p - (n₀ : ℝ)) := by
            rw [Real.rpow_sub hy0, div_eq_mul_inv, ← Real.rpow_neg hy0.le]
            ring
        _ ≤ Bw X * c₀ ^ (p - (n₀ : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hc₀ (hc₀le y) hpn₀) (hBw0 X)
    rw [Finset.mul_sum]
    calc ∑ X ∈ ops, ENNReal.ofReal (H y ^ (-(n₀ : ℝ))) *
          ENNReal.ofReal ‖normOneDifferential A X f y‖
        ≤ ∑ X ∈ ops, ENNReal.ofReal (Bw X * c₀ ^ (p - (n₀ : ℝ))) := Finset.sum_le_sum hterm
      _ = ENNReal.ofReal M := by
          rw [← ENNReal.ofReal_sum_of_nonneg fun X _ =>
            mul_nonneg (hBw0 X) (Real.rpow_nonneg hc₀.le _), hM, Finset.sum_mul]
  have hx0 : 0 < H x := lt_of_lt_of_le hc₀ (hc₀le x)
  have hpos : 0 < H x ^ ((n + 1 : ℕ) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hfinal : H x ^ ((n + 1 : ℕ) : ℝ) *
      ‖normOneTruncation hG hi D hK hρ Tp f ⟨x, hx1⟩‖ ≤ B * M := by
    have h := hineq.trans (mul_le_mul' le_rfl hsup)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx0.le _), ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul B.coe_nonneg] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg B.coe_nonneg hM0)).1 h
  have hext : normOneExtend (normOneTruncation hG hi D hK hρ Tp f) x =
      normOneTruncation hG hi D hK hρ Tp f ⟨x, hx1⟩ :=
    normOneExtend_coe _ ⟨x, hx1⟩
  rw [hext]
  have h1 : ‖normOneTruncation hG hi D hK hρ Tp f ⟨x, hx1⟩‖ ≤
      B * M / H x ^ ((n + 1 : ℕ) : ℝ) := (le_div_iff₀' hpos).2 hfinal
  have hpow : H x ^ ((n + 1 : ℕ) : ℝ) = H x ^ (n : ℝ) * H x := by
    rw [Nat.cast_succ, Real.rpow_add hx0, Real.rpow_one]
  have hBM : 0 ≤ B * M := mul_nonneg B.coe_nonneg hM0
  calc ‖normOneTruncation hG hi D hK hρ Tp f ⟨x, hx1⟩‖
      ≤ B * M / H x ^ ((n + 1 : ℕ) : ℝ) := h1
    _ = B * M * H x ^ (-(n : ℝ)) * (H x)⁻¹ := by
        rw [hpow, Real.rpow_neg hx0.le, div_eq_mul_inv, mul_inv]
        ring
    _ ≤ B * M * H x ^ (-(n : ℝ)) * c₀⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hc₀ (hc₀le x))
          (mul_nonneg hBM (Real.rpow_nonneg hx0.le _))
    _ = B * M * c₀⁻¹ * H x ^ (-(n : ℝ)) := by ring

end Estimate

/-- **Arthur 2005, Proposition 13.2(b), for a suitable maximal compact subgroup.** For every
number field `F`, connected reductive `G`, maximal split torus `i`, generic cocharacter `ν` and
embedded Lie atlas `A` on `G(F∞)¹`, there is a maximal compact subgroup `K` of `G(𝔸_F)` with
`P₀(𝔸_F) K = G(𝔸_F)`, whose parabolic part commutes with the positive torus of every actual
Siegel setup, with the following property. For reflection data `D`, the comparison `hρ` and every
closed matrix realization `rho` there is a threshold `c` such that the family estimate
(13.5)–(13.6) holds for every `T` with `β(T) > c` for each simple relative root `β`. Arthur fixes
one suitable maximal compact subgroup (2005, p. 24) and proves the estimate for it. -/
def NormOneTruncationFamilyEstimateStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
    ∀ (e : ℕ) (A : NormOneLieAtlas F G hG.smoothDimension_spec e),
    ∃ (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K),
      IsMaximalCompactSubgroup F G K ∧
      (∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j → IsPositiveTorusCompatible F G T i ν T₀ j K) ∧
      ∀ (D : RelativeRootReflectionData i) (hρ : Function.Bijective (restrictToTorus F i ν ∅))
        {N : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N → IsClosedSubgroup rho →
        ∃ c : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, c < eval T β Tp) →
          IsNormOneFamilyEstimate.{u, v} A hG hi D hK hρ rho Tp

/-- **Reduction of Arthur's Proposition 13.2.** Part (b) for a suitable maximal compact subgroup,
`NormOneTruncationFamilyEstimateStatement`, gives `TruncationRapidDecayStatement`. The atlas is
`exists_normOneLieAtlas`, and part (a) is derived from part (b) by
`isRapidlyDecreasing_of_isNormOneFamilyEstimate`. -/
theorem truncationRapidDecayStatement_of_familyEstimate
    (hfamily : NormOneTruncationFamilyEstimateStatement.{u, v}) :
    TruncationRapidDecayStatement.{u, v} := by
  intro F _ _ G _ _ T i _ ν hG hi hν
  obtain ⟨e, ⟨A⟩⟩ := Automorphic.GroupSchemeFunctions.exists_normOneLieAtlas F G hG
  obtain ⟨K, hK, hKmax, hKc, hest⟩ := hfamily F G T i ν hG hi hν e A
  refine ⟨e, A, K, hK, hKmax, hKc, fun D hρ N rho hN hcl => ?_⟩
  obtain ⟨c, hc⟩ := hest D hρ rho hN hcl
  exact ⟨c, fun Tp hTp => ⟨fun f hf =>
    isRapidlyDecreasing_of_isNormOneFamilyEstimate A hG hi D hK hρ rho hN Tp
      (hc Tp hTp) f hf, hc Tp hTp⟩⟩

end Langlands.Global.ArthurTruncation
