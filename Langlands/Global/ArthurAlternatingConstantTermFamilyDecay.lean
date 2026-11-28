import Langlands.Global.ArthurAlternatingWordSystem
import Langlands.Global.ArthurSigmaTorusBounds
import Langlands.Global.AdelicStandardLeviContractionModulo

/-! # Family decay of the alternating constant terms on the sigma region

Arthur 1980, Lemma 1.4, estimate (1.2) on p. 95, in family form. For a family `φ o` of functions
on `G(𝔸)¹` of class `Cʳ` at a fixed open compact level, Arthur's alternating constant term over
`R ⊆ P ⊆ S` of the extension of `φ o` is evaluated at the points `p a k` of the sigma region
(`p` in a compact subset of `P₀(𝔸)`, `a` in `sigmaTorusRegion`, `k` in a compact subset of
`G(𝔸)¹`). Its integral over the family, times any power `H^m` of the height, is bounded by a
constant times `M`, whenever the integrals over the family of the word derivatives of `φ` up to
a fixed length are bounded by `M H^{n₀}` on `G(𝔸)¹`. The word length depends only on the data,
`n₀` and `m`, not on the family.

The proof follows the sup-norm argument: if all roots of `S \ R` are bounded on `a`, the height
of `p a k` is bounded; otherwise, for the largest root `α`, the constant term along the maximal
radical omitting `α` vanishes and `normOneFamilyDecayModulo` gains the power `nw` of the
contraction factor of `α`, which beats the height growth. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open AlgebraicGeometry CategoryTheory NumberField Set MeasureTheory
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal ENNReal Pointwise

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints InfiniteAdelicGroupPoints
  RepresentationGrowth PositiveRealTorus AdelicSiegelFactors ArthurParabolicSpaces

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {K : Subgroup (AdelicGroupPoints F G)}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (D : RelativeRootReflectionData i) (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))
  {d e N : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  (At : NormOneLieAtlas F G hsmooth e) (ρ : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "G¹" => normOneSubgroup F G
local notation "Hρ" => adelicHeight F G ρ
local notation "Δ" => simpleFinset ν hG hi
local notation "J" => Finset (characterLattice T)
local notation "Pts" => intrinsicSubgroup F T
local notation "P₀" => MonoidHom.range
  (ContinuousMonoidHom.toMonoidHom (map F _ G (Standard.parabolicHom i ν ∅)))
local notation "aG" => positiveTorusMap F i

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [Mono i.hom.hom.left] in
private theorem relativeCharacterDecay_pow_eq_exp (α : characterLattice T) (a : Pts) (n : ℕ) :
    relativeCharacterDecay (𝟙 T) α a ^ n =
      Real.exp (-(n : ℝ) / (Module.finrank ℚ F : ℝ) * logNormHom F T a.val α) := by
  have hpos : 0 < ((normCharacter F T ((𝟙 T) ≫ α) a : ℝ≥0) : ℝ) := by
    exact_mod_cast (normCharacter F T ((𝟙 T) ≫ α) a).ne_zero.bot_lt
  rw [relativeCharacterDecay, Real.rpow_def_of_pos hpos, ← Real.exp_nat_mul, Category.id_comp]
  change Real.exp (_ * (Real.log _ * _)) = Real.exp (_ * Real.log _)
  congr 1
  ring

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem exists_height_factor_bound (hN : 0 < N) (Ω K' : Set A) (hΩ : IsCompact Ω)
    (hK' : IsCompact K') :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p ∈ Ω, ∀ a : A, ∀ k ∈ K', Hρ (p * a * k) ≤ C * Hρ a := by
  have hc := continuous_adelicHeight F G ρ hN
  obtain ⟨C₁, hC₁⟩ := (hΩ.image hc).bddAbove
  obtain ⟨C₂, hC₂⟩ := (hK'.image hc).bddAbove
  let c₁ := max 1 C₁
  let c₂ := max 1 C₂
  have h₁ : 1 ≤ c₁ := le_max_left _ _
  have h₂ : 1 ≤ c₂ := le_max_left _ _
  have hpos (x : A) : 0 ≤ Hρ x := zero_le_one.trans (one_le_adelicHeight F G ρ hN x)
  refine ⟨c₁ * c₂, one_le_mul_of_one_le_of_one_le h₁ h₂, fun p hp a k hk => ?_⟩
  calc
    Hρ (p * a * k) ≤ Hρ (p * a) * Hρ k := adelicHeight_mul_le F G ρ hN _ _
    _ ≤ (Hρ p * Hρ a) * Hρ k :=
      mul_le_mul_of_nonneg_right (adelicHeight_mul_le F G ρ hN _ _) (hpos _)
    _ ≤ (c₁ * Hρ a) * c₂ :=
      mul_le_mul (mul_le_mul_of_nonneg_right ((hC₁ ⟨p, hp, rfl⟩).trans (le_max_right _ _))
        (hpos _)) ((hC₂ ⟨k, hk, rfl⟩).trans (le_max_right _ _)) (hpos _)
        (mul_nonneg (zero_le_one.trans h₁) (hpos _))
    _ = (c₁ * c₂) * Hρ a := by ring

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem ofReal_mul_mul_ofReal {a : ℝ} (b : ℝ) (ha : 0 ≤ a) (M : ℝ≥0∞) :
    ENNReal.ofReal a * M * ENNReal.ofReal b = ENNReal.ofReal (a * b) * M := by
  rw [ENNReal.ofReal_mul ha]
  ring

include hν in
/-- **Family decay of the alternating constant terms on the sigma region.** -/
theorem alternatingConstantTerm_familyDecay (hN : 0 < N) {R S : J} (hRS : R ⊆ S) (hS : S ⊆ Δ)
    (T₁ Tp : V T) (Ω K' : Set A) (hΩ : IsCompact Ω) (hK' : IsCompact K') (hK'₁ : K' ⊆ G¹)
    (hΩP : Ω ⊆ P₀) {K₀ : Subgroup (FiniteAdelicGroupPoints F G)}
    (hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G)))
    (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G))) (n₀ m : ℕ) :
    ∃ (nw : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ p ∈ Ω, ∀ a ∈ sigmaTorusRegion hG hi D hK hρ R S T₁ Tp,
      ∀ k ∈ K', p * aG a * k ∈ G¹ →
      ∀ {Ω' : Type w} [MeasurableSpace Ω'] (mΩ : Measure Ω') (φ : Ω' → G¹ → ℂ) (r : ℕ),
      nw ≤ r → (∀ o, IsNormOneCr At r K₀ hK₀ (φ o)) →
      Measurable (fun q : Ω' × G¹ => φ q.1 q.2) →
      ∀ M : ℝ≥0∞, (∀ w : List (Fin e), w.length ≤ nw → ∀ y : G¹,
          ∫⁻ o, ‖normOneWordDerivative At w (φ o) y‖ₑ ∂mΩ ≤ ENNReal.ofReal (Hρ y ^ n₀) * M) →
      (∫⁻ o, ‖alternatingConstantTerm (ν := ν) hG hi R S (normOneExtension hG (φ o))
          (p * aG a * k)‖ₑ ∂mΩ) * ENNReal.ofReal (Hρ (p * aG a * k) ^ m) ≤
        ENNReal.ofReal C * M := by
  classical
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  obtain ⟨B, C₀, t₀, hB, hC₀, ht₀, hTorus⟩ :=
    sigmaTorusRegion_bounds hG hi hν D hK hρ ρ hN R S hRS hS T₁ Tp
  let A₀ := simpleRelativeRoots i ν
  have hS₀ : (S : Set (characterLattice T)) ⊆ A₀ := fun α hα =>
    (mem_simpleFinset hG hi).mp (hS hα)
  let b₀ : ℝ≥0 := ⟨Real.exp (-B), (Real.exp_pos _).le⟩
  have hb₀ : 0 < b₀ := NNReal.coe_pos.mp (Real.exp_pos _)
  let b : ℝ≥0ˣ := Units.mk0 b₀ hb₀.ne'
  let Ch := standardLeviWeakChamber F T (S : Set (characterLattice T)) b
  have hbLog : Real.log ((b : ℝ≥0) : ℝ) = -B := Real.log_exp _
  have hch (a : Pts) (ha : a ∈ sigmaTorusRegion hG hi D hK hρ R S T₁ Tp) : a ∈ Ch := by
    intro α hα
    rw [Category.id_comp]
    apply Units.val_le_val.mp
    apply NNReal.coe_le_coe.mp
    have ha0 : 0 < ((normCharacter F T α a : ℝ≥0) : ℝ) := by
      exact_mod_cast (normCharacter F T α a).ne_zero.bot_lt
    change Real.exp (-B) ≤ _
    rw [← Real.exp_log ha0]
    exact Real.exp_le_exp.mpr ((hTorus a ha).1 α hα)
  let Yf := (finite F G '' Ω) * (finite F G '' K')
  have hYf : IsCompact Yf :=
    (hΩ.image (finite F G).continuous).mul (hK'.image (finite F G).continuous)
  have hxfin (p : A) (hp : p ∈ Ω) (a : Pts) (k : A) (hk : k ∈ K') :
      finite F G (p * aG a * k) ∈ Yf := by
    have ha := finite_positiveMap F G T i T (𝟙 T) hi.isSplitSubtorus.1 a
    rw [map_mul, map_mul, show finite F G (aG a) = 1 from ha, mul_one]
    exact Set.mul_mem_mul (mem_image_of_mem _ hp) (mem_image_of_mem _ hk)
  let Df : ℝ := Module.finrank ℚ F
  have hDf : 0 < Df := Nat.cast_pos.mpr Module.finrank_pos
  let ex : ℝ := (n₀ : ℝ) + (m : ℝ)
  have hex : 0 ≤ ex := add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨nw, hnw⟩ := exists_nat_gt (Df * (t₀ * ex))
  have hnw' : t₀ * ex ≤ (nw : ℝ) / Df :=
    (le_div_iff₀ hDf).mpr (by simpa only [mul_comm] using hnw.le)
  obtain ⟨Cg, hCg, hgb⟩ :=
    exists_lintegral_alternatingWordSystem_le.{u, w} hν At (hK₀ := hK₀) hK₀o hS ρ hN n₀
  let R₀ := (map F _ G (Standard.unipotentHom i ν (S : Set (characterLattice T)))).toMonoidHom.range
  have hdecay (α : (S \ R : Finset (characterLattice T))) :
      ∃ K₁ : Set A, IsCompact K₁ ∧ K' ⊆ K₁ ∧ K₁ ⊆ G¹ ∧ ∃ C₁ : ℝ, 0 ≤ C₁ ∧
        ∀ p ∈ Ω, ∀ a : Ch, p * aG a.val ∈ G¹ → ∀ k ∈ K',
        ∀ {Ω' : Type w} [MeasurableSpace Ω'] (mΩ : Measure Ω') (φ : Ω' → G¹ → ℂ) (r : ℕ),
        nw ≤ r → (∀ o, IsNormOneCr At r K₀ hK₀ (φ o)) →
        Measurable (fun q : Ω' × G¹ => φ q.1 q.2) →
        ∫⁻ o, ‖alternatingWordSystem (ν := ν) hG hi At R S nw (φ o) [] (p * aG a.val * k)‖ₑ ∂mΩ ≤
          ENNReal.ofReal (C₁ * relativeCharacterDecay (𝟙 T) α.val a.val ^ nw) *
            ⨆ (k' ∈ K₁) (_ : finite F G k' = finite F G k) (w : List (Fin e))
              (_ : w.length = nw), ∫⁻ o, ‖alternatingWordSystem (ν := ν) hG hi At R S nw (φ o) w
                (p * aG a.val * k')‖ₑ ∂mΩ := by
    let M := A₀ \ {α.val}
    let U := Standard.unipotentScheme i ν M
    let j := Standard.unipotentHom i ν M
    let : IsAffine U.X.left := @isAffine_of_isAffineHom _ _ U.X.hom
      (Standard.isClosedSubgroup_unipotentHom i ν M).isAffineHom_source inferInstance
    let : IsClosedImmersion j.hom.hom.left := Standard.isClosedSubgroup_unipotentHom i ν M
    let ε (a : Ch) := relativeCharacterDecay (𝟙 T) α.val a.val
    have hε (a : Ch) : 0 ≤ ε a := (relativeCharacterDecay_pos (𝟙 T) α.val a.val).le
    have hεB (a : Ch) : ε a ≤ Real.exp (B / Df) := by
      have ha := a.prop α.val (Finset.mem_sdiff.mp α.2).1
      rw [Category.id_comp] at ha
      have hbpos : 0 < ((b : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr hb₀
      have hlo := Real.log_le_log hbpos (by exact_mod_cast Units.val_le_val.mpr ha)
      rw [hbLog] at hlo
      have hEq := relativeCharacterDecay_pow_eq_exp α.val a.val 1
      simp only [pow_one, Nat.cast_one] at hEq
      rw [show ε a = relativeCharacterDecay (𝟙 T) α.val a.val from rfl, hEq]
      apply Real.exp_le_exp.mpr
      change -B ≤ logNormHom F T a.val α.val at hlo
      rw [show -(1 : ℝ) / Df * logNormHom F T a.val α.val =
        (-logNormHom F T a.val α.val) / Df by ring]
      exact div_le_div_of_nonneg_right (by linarith) hDf.le
    obtain ⟨s, Ψ, hΨ₀, hΨ, hContraction, hΨ₁⟩ := exists_standardLeviContractionModulo_normOne hG hi
      hν hsmooth (S : Set (characterLattice T)) hS₀ α.val (Finset.mem_sdiff.mp α.2).1 b Ω hΩ hΩP
    have hgeom := (Standard.parabolicStructure i ν hG hi hν M (sdiff_subset : M ⊆ A₀)).2.2.1
    obtain ⟨K₁, hK₁, hIncl, hK₁₁, C₁, hC₁, hIter⟩ := normOneFamilyDecayModulo.{u, w} j At Ω
      (fun a : Ch => aG a.val) R₀ Ψ ε hgeom.1.smooth hgeom.1.connectedSpace hgeom.1.isUnipotent
      (Real.exp (B / Df)) (Real.exp_pos _).le hεB hε hContraction hΨ₀ hΨ₁ Yf hYf K₀ hK₀o hΨ nw K'
      hK' hK'₁
    refine ⟨K₁, hK₁, hIncl, hK₁₁, C₁, hC₁, ?_⟩
    intro p hp a hpa k hk Ω' _ mΩ φ r hr hφ hm
    exact hIter p hp a hpa k hk (hxfin p hp a.val k hk) mΩ
      (fun o w => alternatingWordSystem (ν := ν) hG hi At R S nw (φ o) w)
      (fun o w => continuous_alternatingWordSystem hν At hK₀o hS hr (hφ o) w)
      (fun w => measurable_alternatingWordSystem hν At hK₀o hS hr hφ hm w)
      (fun o w q y => by
        let U₀ := SubgroupFunctor.range j
        let z : AdelicSubgroupPoints.adelicPoints F G U₀ := ⟨_, ⟨rational F U q, rfl⟩⟩
        have hz : z ∈ AdelicSubgroupPoints.rationalSubgroup F G U₀ :=
          (mem_rationalSubgroup_range_iff j z).mpr ((mem_rationalImage_iff j _).mpr ⟨q, rfl⟩)
        exact alternatingWordSystem_isRationalInvariant hν At hK₀o hS hr (hφ o) w
          ⟨M, sdiff_subset⟩ z hz y)
      (fun o w l hl y => alternatingWordSystem_mul_ofFinite At hK₀o R S hr (hφ o) w l hl y)
      (fun o w l hl y => alternatingWordSystem_radical_mul hν At hK₀o hS hr (hφ o) w l hl y)
      (fun o w _ => constantTerm_alternatingWordSystem_eq_zero hν At hK₀o hRS hS α.2 hr (hφ o) w)
      (fun o w hw => isNormOnePathDerivative_alternatingWordSystem hν At hK₀o hS hr (hφ o) w hw)
  choose Kα hKα hKin hKα₁ Cα hCα hiter using hdecay
  have hcompact (α : (S \ R : Finset (characterLattice T))) :=
    exists_height_factor_bound ρ hN Ω (Kα α) hΩ (hKα α)
  choose Eα hEα hE using hcompact
  let Dα (α : (S \ R : Finset (characterLattice T))) := Eα α * C₀
  have hDα (α : (S \ R : Finset (characterLattice T))) : 0 < Dα α :=
    mul_pos (zero_lt_one.trans_le (hEα α)) (zero_lt_one.trans_le hC₀)
  obtain ⟨E₀, hE₀, hEbase⟩ := exists_height_factor_bound ρ hN Ω K' hΩ hK'
  let Cbase := E₀ * C₀
  have hCbase : 0 < Cbase := mul_pos (zero_lt_one.trans_le hE₀) (zero_lt_one.trans_le hC₀)
  let Base := Cg * Cbase ^ ex
  let Tail (α : (S \ R : Finset (characterLattice T))) := Cα α * Cg * Dα α ^ ex
  have hBase : 0 ≤ Base := mul_nonneg hCg (Real.rpow_nonneg hCbase.le _)
  have hTail (α : (S \ R : Finset (characterLattice T))) : 0 ≤ Tail α :=
    mul_nonneg (mul_nonneg (hCα α) hCg) (Real.rpow_nonneg (hDα α).le _)
  refine ⟨nw, Base + ∑ α, Tail α, add_nonneg hBase (Finset.sum_nonneg fun α _ => hTail α), ?_⟩
  intro p hp a ha k hk hx Ω' _ mΩ φ r hr hφ hm M hgrowth
  have hg0 (o : Ω') : alternatingConstantTerm (ν := ν) hG hi R S (normOneExtension hG (φ o)) =
      alternatingWordSystem (ν := ν) hG hi At R S nw (φ o) [] := by
    simp only [alternatingWordSystem, List.length_nil, zero_le, ite_true,
      normOneWordDerivative_nil]
  simp only [hg0]
  have hpa : p * aG a ∈ G¹ := by
    have h := (normOneSubgroup F G).mul_mem hx ((normOneSubgroup F G).inv_mem (hK'₁ hk))
    rwa [mul_inv_cancel_right] at h
  have hgbw (w : List (Fin e)) (hw : w.length ≤ nw) (y : A) (hy : y ∈ G¹) :
      ∫⁻ o, ‖alternatingWordSystem (ν := ν) hG hi At R S nw (φ o) w y‖ₑ ∂mΩ ≤
        ENNReal.ofReal (Cg * Hρ y ^ n₀) * M :=
    hgb mΩ φ nw r hr hφ hm M w (hgrowth w hw) ⟨y, hy⟩
  let logRoot (α : characterLattice T) := logNormHom F T a.val α
  let Lmax : Option (S \ R : Finset (characterLattice T)) → ℝ :=
    fun α => α.elim 0 (fun x => logRoot x.val)
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image Finset.univ Lmax ⟨none, Finset.mem_univ _⟩
  have hmax₀ : 0 ≤ Lmax s := hs none (Finset.mem_univ _)
  have hmax : ∀ α ∈ S \ R, logRoot α ≤ Lmax s := fun α hα =>
    hs (some ⟨α, hα⟩) (Finset.mem_univ _)
  have hha := (hTorus a ha).2 (Lmax s) hmax₀ hmax
  let x := p * aG a * k
  have hxH : 0 < Hρ x := zero_lt_one.trans_le (one_le_adelicHeight F G ρ hN x)
  have hHnn (y : A) : 0 ≤ Hρ y := zero_le_one.trans (one_le_adelicHeight F G ρ hN y)
  change (∫⁻ o, ‖alternatingWordSystem (ν := ν) hG hi At R S nw (φ o) [] x‖ₑ ∂mΩ) *
    ENNReal.ofReal (Hρ x ^ m) ≤ _
  cases s with
  | none =>
    have hha' : Hρ (aG a) ≤ C₀ := by
      simpa only [Lmax, Option.elim_none, mul_zero, Real.exp_zero, mul_one] using hha
    have hdx : Hρ x ≤ Cbase := (hEbase p hp _ k hk).trans
      (mul_le_mul_of_nonneg_left hha' (zero_le_one.trans hE₀))
    calc
      _ ≤ ENNReal.ofReal (Cg * Hρ x ^ n₀) * M * ENNReal.ofReal (Hρ x ^ m) :=
        mul_le_mul' (hgbw [] (Nat.zero_le _) x hx) le_rfl
      _ = ENNReal.ofReal (Cg * Hρ x ^ ex) * M := by
        rw [ofReal_mul_mul_ofReal _ (mul_nonneg hCg (pow_nonneg hxH.le _))]
        congr 2
        rw [show ex = (n₀ : ℝ) + (m : ℝ) from rfl, Real.rpow_add hxH, Real.rpow_natCast,
          Real.rpow_natCast, mul_assoc]
      _ ≤ ENNReal.ofReal (Base + ∑ α, Tail α) * M := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxH.le hdx hex) hCg).trans
          (le_add_of_nonneg_right (Finset.sum_nonneg fun α _ => hTail α))
  | some α =>
    let t := logRoot α.val
    have ht : 0 ≤ t := hmax₀
    let Hmax := Dα α * Real.exp (t₀ * t)
    have hHmax : 0 < Hmax := mul_pos (hDα α) (Real.exp_pos _)
    have hcap (k₁ : A) (hk₁ : k₁ ∈ Kα α) : Hρ (p * aG a * k₁) ≤ Hmax := by
      exact ((hE α p hp _ k₁ hk₁).trans
        (mul_le_mul_of_nonneg_left hha (zero_le_one.trans (hEα α)))).trans_eq
          (mul_assoc (Eα α) C₀ (Real.exp (t₀ * t))).symm
    have hfdec := hiter α p hp ⟨a, hch a ha⟩ hpa k hk mΩ φ r hr hφ hm
    have hsup : (⨆ (k' ∈ Kα α) (_ : finite F G k' = finite F G k) (w : List (Fin e))
        (_ : w.length = nw), ∫⁻ o, ‖alternatingWordSystem (ν := ν) hG hi At R S nw (φ o) w
          (p * aG a * k')‖ₑ ∂mΩ) ≤ ENNReal.ofReal (Cg * Hmax ^ n₀) * M := by
      refine iSup₂_le fun k' hk' => iSup_le fun _ => iSup_le fun w => iSup_le fun hw => ?_
      have hy : p * aG a * k' ∈ G¹ := (normOneSubgroup F G).mul_mem hpa (hKα₁ α hk')
      refine (hgbw w hw.le _ hy).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hHnn _) (hcap k' hk') n₀) hCg
    let ε := relativeCharacterDecay (𝟙 T) α.val a
    have hε : 0 ≤ ε := (relativeCharacterDecay_pos (𝟙 T) α.val a).le
    have hExpo : ε ^ nw * Hmax ^ ex ≤ Dα α ^ ex := by
      rw [show ε = relativeCharacterDecay (𝟙 T) α.val a from rfl, relativeCharacterDecay_pow_eq_exp,
        show Hmax = Dα α * Real.exp (t₀ * t) from rfl,
        Real.mul_rpow (hDα α).le (Real.exp_pos _).le, ← Real.exp_mul]
      change Real.exp (-(nw : ℝ) / Df * t) * (Dα α ^ ex * Real.exp (t₀ * t * ex)) ≤ _
      rw [mul_left_comm, ← Real.exp_add]
      have h : -(nw : ℝ) / Df * t + t₀ * t * ex ≤ 0 := by
        calc
          _ = (t₀ * ex - (nw : ℝ) / Df) * t := by ring
          _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hnw') ht
      exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr h)
        (Real.rpow_nonneg (hDα α).le _)).trans_eq (mul_one _)
    have hC1 : 0 ≤ Cα α * ε ^ nw := mul_nonneg (hCα α) (pow_nonneg hε _)
    have hC2 : 0 ≤ Cg * Hmax ^ n₀ := mul_nonneg hCg (pow_nonneg hHmax.le _)
    calc
      _ ≤ ENNReal.ofReal (Cα α * ε ^ nw) * (ENNReal.ofReal (Cg * Hmax ^ n₀) * M) *
            ENNReal.ofReal (Hmax ^ m) :=
        mul_le_mul' (hfdec.trans (mul_le_mul' le_rfl hsup))
          (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hxH.le (hcap k (hKin α hk)) m))
      _ = ENNReal.ofReal (Cα α * Cg * (ε ^ nw * Hmax ^ ex)) * M := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC1,
          ofReal_mul_mul_ofReal _ (mul_nonneg hC1 hC2)]
        congr 2
        rw [show ex = (n₀ : ℝ) + (m : ℝ) from rfl, Real.rpow_add hHmax, Real.rpow_natCast,
          Real.rpow_natCast]
        ring
      _ ≤ ENNReal.ofReal (Tail α) * M :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hExpo (mul_nonneg (hCα α) hCg))) le_rfl
      _ ≤ ENNReal.ofReal (Base + ∑ α, Tail α) * M := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        exact (Finset.single_le_sum (f := Tail) (fun α _ => hTail α) (Finset.mem_univ α)).trans
          (le_add_of_nonneg_left hBase)

end Langlands.Global.ArthurTruncation
