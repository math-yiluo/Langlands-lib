import Langlands.Global.ArthurAlternatingConstantTermFamilyDecay
import Langlands.Global.ArthurTruncationExpansion
import Langlands.Global.ArthurSiegelSetsIwasawaStatement
import Langlands.Global.ArthurSiegelCoveringProof
import Langlands.Global.ArthurSiegelReductionProof
import Langlands.Global.ArthurSiegelCosetSum
import Langlands.Global.AdelicRationalHeightSummability
import Langlands.Global.ArthurTruncationRapidDecayReduction

/-! # The family estimate (13.5)–(13.6) for every compact Iwasawa subgroup

The family inequality comes from Arthur 2005, Proposition 13.2(b) and (13.5)–(13.6), and Arthur
1980, Lemma 1.4. Given an embedded Lie atlas on `G(F∞)¹`, a compact subgroup `K` with
`P₀(𝔸) K = G(𝔸)`, reflection data, the real character comparison and a closed matrix realization in
`GL_N` with `N > 0`, the proof gives a threshold `c` such that the fixed-level family estimate
`IsNormOneFamilyEstimate` holds whenever `β(T) > c` for all simple relative roots `β`.

For each fixed norm-one point `x` in the Siegel set, the truncation of `φ o` equals the truncation
of its continuous rational extension. The sigma expansion at `x` is a finite sum of weighted
alternating constant terms at rational translates of `x`. The finite index set and weights are
independent of `o`, and measurability of the terms in `o` gives measurability of the truncation in
`o` at this fixed `x`. Each translate with nonzero coefficient is moved into the sigma region,
where `alternatingConstantTerm_familyDecay` bounds the integral over the family. Coset-sum decay
and norm minimality on the Siegel set combine these bounds. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open AlgebraicGeometry CategoryTheory NumberField Set MeasureTheory
open scoped Classical CategoryTheory.MonObj ENNReal NNReal Pointwise

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints ArthurParabolicSpaces
  AdelicSiegelFactors PositiveRealTorus RepresentationGrowth

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
local notation "Γ" => rationalSubgroup F G
local notation "Hρ" => adelicHeight F G ρ
local notation "Δ" => simpleFinset ν hG hi
local notation "J" => Finset (characterLattice T)
local notation "PImage(" R ")" => parabolicRationalImage
  (Standard.parabolicHom i ν (R : Set (characterLattice T)))
local notation "PΓ(" R ")" => parabolicRationalSubgroup F
  (Standard.parabolicHom i ν (R : Set (characterLattice T)))
local notation "PQuot(" R ")" => ParabolicRationalCosets F
  (Standard.parabolicHom i ν (R : Set (characterLattice T)))
local notation "H₀(" y ")" => height hi hK hρ y
local notation "σ₀" => ArthurRelative.sigma hG hi ν D
local notation "P₀" => MonoidHom.range
  (ContinuousMonoidHom.toMonoidHom (map F _ G (Standard.parabolicHom i ν ∅)))

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
/-- A finite bound in `ℝ≥0∞` against a factor `h ≥ 1` gives a real bound. -/
private theorem toReal_bound_of_le {I M : ℝ≥0∞} {h B : ℝ} (hh : 1 ≤ h) (hB : 0 ≤ B) (hM : M ≠ ⊤)
    (hI : I * ENNReal.ofReal h ≤ ENNReal.ofReal B * M) :
    I ≠ ⊤ ∧ I.toReal * h ≤ B * M.toReal := by
  have hne : ENNReal.ofReal B * M ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM
  have hle : I ≤ I * ENNReal.ofReal h :=
    le_mul_of_one_le_right (by positivity) (by simpa using ENNReal.ofReal_le_ofReal hh)
  have hI' : I ≠ ⊤ := ne_top_of_le_ne_top hne (hle.trans hI)
  refine ⟨hI', ?_⟩
  have h1 := ENNReal.toReal_mono hne hI
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (zero_le_one.trans hh), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hB] at h1

include hν in
/-- At a fixed adelic point, the alternating constant term of the extension is measurable in the
family parameter. -/
theorem measurable_alternatingConstantTerm_normOneExtension {R S : J} (hS : S ⊆ Δ)
    {K₀ : Subgroup (FiniteAdelicGroupPoints F G)}
    {hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))}
    (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G))) {Ω' : Type w} [MeasurableSpace Ω']
    {φ : Ω' → G¹ → ℂ} {r : ℕ} (hφ : ∀ o, IsNormOneCr At r K₀ hK₀ (φ o))
    (hm : Measurable (fun q : Ω' × G¹ => φ q.1 q.2)) (y : A) :
    Measurable (fun o => alternatingConstantTerm (ν := ν) hG hi R S (normOneExtension hG (φ o)) y) := by
  have h := (measurable_alternatingWordSystem (hG := hG) (hi := hi) (R := R) hν At hK₀o hS (Nat.zero_le r)
    hφ hm []).comp (measurable_id.prodMk (measurable_const : Measurable fun _ : Ω' => y))
  simpa [alternatingWordSystem, Function.comp_def] using h

section Representatives

variable (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
  (T₁ Tp : V T)

local notation "Ω" => compactPrefix F G T i ν (canonicalStandardFactors F G T i ν) C
local notation "coeff" => siegelSigmaCoefficient hG hi D hK hρ C T₁ Tp

include hν in
private theorem sigma_height_mul_left' {R S : J} (hRS : R ⊆ S) (hS : S ⊆ Δ)
    {z : A} (hz : z ∈ PImage(R)) (y : A) :
    σ₀ (R : Set (characterLattice T)) S (H₀(z * y) - Tp) =
      σ₀ (R : Set (characterLattice T)) S (H₀(y) - Tp) := by
  rw [arthurRelative_sigma_eq_sum hG hi hν D R S hS, arthurRelative_sigma_eq_sum hG hi hν D R S hS]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  obtain ⟨hQΔ, hSQ⟩ := Finset.mem_filter.mp hQ
  have hR₀ : (R : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun a ha =>
    (mem_simpleFinset hG hi).mp (hS (hRS ha))
  have hQ₀ : (Q : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun a ha =>
    (mem_simpleFinset hG hi).mp (Finset.mem_powerset.mp hQΔ ha)
  have hzQ : z ∈ PImage(Q) := parabolicRationalImage_mono hG hi hν
    (show (R : Set (characterLattice T)) ⊆ Q from hRS.trans hSQ) hQ₀ hz
  rw [tau_height_mul_left parabolicSpacesComparison hG hi hν D hK hρ Tp _ hR₀ hz y,
    tauHat_height_mul_left hG hi hν D hK hρ (Finset.mem_powerset.mp hQΔ) hzQ Tp y]

include hν in
private theorem alternatingConstantTerm_mul_left' {R S : J} (hS : S ⊆ Δ)
    (f : ContinuousRationalFunctions F G) {z : A} (hz : z ∈ PImage(R)) (y : A) :
    alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f) (z * y) =
      alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f) y := by
  unfold alternatingConstantTerm
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hPS, hRP⟩ := Finset.mem_filter.mp hP
  have hP₀ : (P : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun a ha =>
    (mem_simpleFinset hG hi).mp (hS (Finset.mem_powerset.mp hPS ha))
  have hzP : z ∈ PImage(P) := parabolicRationalImage_mono hG hi hν
    (show (R : Set (characterLattice T)) ⊆ P from hRP) hP₀ hz
  rw [constantTerm_rationalImage_mul hG hi hν ((Finset.mem_powerset.mp hPS).trans hS) f hzP y]

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem compactPrefix_subset_minimalParabolic' : Ω ⊆ P₀ := by
  let Q := (algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F)))
  rintro _ ⟨_, ⟨n, _, rfl⟩, _, ⟨m, _, rfl⟩, rfl⟩
  apply (mem_range_map_iff_of_isRepresentedBy F (Standard.isRepresentedBy_parabolicHom i ν ∅) _).mpr
  apply Subgroup.mul_mem
  · exact standardUnipotent_le_standardParabolic i ν ∅ Q
      (unipotent_mem_standard F G T i ν (canonicalStandardFactors F G T i ν) n)
  · exact standardLevi_le_standardParabolic i ν ∅ Q
      (levi_mem_standard F G T i ν (canonicalStandardFactors F G T i ν) m.val)

include hν in
omit [IsAffine G.X.left] in
private theorem exists_sigmaTorusRegion_of_mem' {R S : J} (hC : C.compactSubgroup = K) {y : A}
    (hy : y ∈ truncatedSiegelSet hG hi D hK hρ C R T₁ Tp)
    (hσ : σ₀ (R : Set (characterLattice T)) S (H₀(y) - Tp) = 1) (hyN : y ∈ normOneSubgroup F G) :
    ∃ p ∈ Ω, ∃ a ∈ sigmaTorusRegion hG hi D hK hρ R S T₁ Tp, ∃ k ∈ C.compactSubgroup,
      p * positiveTorusMap F i a * k = y := by
  obtain ⟨n, hn, m, hm, a, ha, k, hk, he⟩ := (mem_siegelSet_iff hi hK hρ C R T₁ y).mp hy.1
  let nG := map F _ G (Standard.unipotentHom i ν ∅) n
  let mG := map F _ G (Standard.leviHom i ν ∅) m.val
  let H₁ := normOneSubgroup F G
  let aG := positiveTorusMap F i a
  have hnG : nG ∈ H₁ := unipotentPoints_le_normOne hG hi hν (empty_subset _)
    (show nG ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range
      (Standard.unipotentHom i ν ∅)) from ⟨n, rfl⟩)
  have hmG : mG ∈ H₁ := map_normOneSubgroup_le F _ G (Standard.leviHom i ν ∅) ⟨m.val, m.2, rfl⟩
  have hkG : k ∈ H₁ :=
    compactSubgroup_le_normOneSubgroup F G C.compactSubgroup C.compact_compactSubgroup hk
  have haG : aG ∈ H₁ := by
    have hY : (nG * mG * aG) * k ∈ H₁ := he.symm ▸ hyN
    have hY' := H₁.mul_mem (H₁.inv_mem (H₁.mul_mem hnG hmG)) (H₁.mul_mem hY (H₁.inv_mem hkG))
    rwa [mul_inv_cancel_right, inv_mul_cancel_left] at hY'
  have hHy : H₀(y) = H₀(aG) := he ▸ height_siegel_product hG hi hν hK hρ n m a (hC ▸ hk)
  refine ⟨nG * mG, Set.mem_mul.mpr ⟨nG, ⟨n, hn, rfl⟩, mG, ⟨m, hm, rfl⟩, rfl⟩,
    a, ⟨ha, ?_, ?_, haG⟩, k, hk, he⟩
  · rw [← hHy]
    exact hy.2
  · rw [← hHy]
    exact hσ

include hν in
/-- **Family bound for the sigma summands.** For a pair `R ⊆ S` there is a word length `nw` and a
constant `B` such that for every norm-one point `x` one can choose distinct rational
representatives `emb c` of the cosets `c`, independent of the family, for which the integral over
the family of the `c`-th summand of the sigma expansion, times `H(emb c · x)^m`, is at most
`B M`, whenever the integrals of the word derivatives of length at most `nw` are bounded by
`M H^{n₀}` on `G(𝔸)¹`. -/
theorem exists_sigmaCoset_representatives_familyBound (hN : 0 < N) (hC : C.compactSubgroup = K)
    {R S : J} (hRS : R ⊆ S) (hS : S ⊆ Δ) {K₀ : Subgroup (FiniteAdelicGroupPoints F G)}
    (hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G)))
    (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G))) (n₀ m : ℕ) :
    ∃ (nw : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ x ∈ G¹, ∃ emb : PQuot(R) ↪ RationalGroupPoints F G,
      ∀ c : PQuot(R), ∀ {Ω' : Type w} [MeasurableSpace Ω'] (mΩ : Measure Ω')
        (φ : Ω' → G¹ → ℂ) (r : ℕ), nw ≤ r → (∀ o, IsNormOneCr At r K₀ hK₀ (φ o)) →
        Measurable (fun q : Ω' × G¹ => φ q.1 q.2) →
        ∀ M : ℝ≥0∞, (∀ w : List (Fin e), w.length ≤ nw → ∀ y : G¹,
          ∫⁻ o, ‖normOneWordDerivative At w (φ o) y‖ₑ ∂mΩ ≤ ENNReal.ofReal (Hρ y ^ n₀) * M) →
        (∫⁻ o, ‖(coeff R S (((Quotient.out c : Γ) : A) * x) : ℂ) *
            alternatingConstantTerm (ν := ν) hG hi R S (normOneExtension hG (φ o))
              (((Quotient.out c : Γ) : A) * x)‖ₑ ∂mΩ) *
          ENNReal.ofReal (Hρ (rational F G (emb c) * x) ^ m) ≤ ENNReal.ofReal B * M := by
  obtain ⟨nw, B, hB, hDecay⟩ := alternatingConstantTerm_familyDecay.{u, w} hG hi hν D hK hρ At ρ hN
    hRS hS T₁ Tp Ω (C.compactSubgroup : Set A)
    (isCompact_compactPrefix F G T i ν (canonicalStandardFactors F G T i ν) C)
    C.compact_compactSubgroup
    (compactSubgroup_le_normOneSubgroup F G C.compactSubgroup C.compact_compactSubgroup)
    (compactPrefix_subset_minimalParabolic' C) hK₀ hK₀o n₀ m
  refine ⟨nw, B, hB, fun x hx => ?_⟩
  have hrep (c : PQuot(R)) : ∃ δ : Γ, Quotient.mk _ δ = c ∧
      (coeff R S (((Quotient.out c : Γ) : A) * x) = 0 ∨
        (coeff R S (((Quotient.out c : Γ) : A) * x) = 1 ∧ ∃ z ∈ PImage(R),
          δ.val * x = z * (((Quotient.out c : Γ) : A) * x) ∧
          ∃ p ∈ Ω, ∃ a ∈ sigmaTorusRegion hG hi D hK hρ R S T₁ Tp, ∃ k ∈ C.compactSubgroup,
            p * positiveTorusMap F i a * k = δ.val * x)) := by
    let y := ((Quotient.out c : Γ) : A) * x
    by_cases hzero : coeff R S y = 0
    · exact ⟨Quotient.out c, Quotient.out_eq c, Or.inl hzero⟩
    · have hF₁ : siegelIndicator hG hi D hK hρ C R T₁ Tp y = 1 := by
        rcases siegelIndicator_eq_zero_or_one hG hi D hK hρ C T₁ Tp R y with hz | hz
        · exact (hzero (by simp only [siegelSigmaCoefficient, hz, zero_mul])).elim
        · exact hz
      have hσ₁ : σ₀ (R : Set (characterLattice T)) S (H₀(y) - Tp) = 1 := by
        rcases arthurRelative_sigma_eq_zero_or_one hG hi hν D R S hRS (H₀(y) - Tp) with hz | hz
        · exact (hzero (by simp only [siegelSigmaCoefficient, hz, mul_zero])).elim
        · exact hz
      have hcoeff : coeff R S y = 1 := by
        simp only [siegelSigmaCoefficient, hF₁, hσ₁, mul_one]
      have he : ∃ z ∈ PImage(R), z * y ∈ truncatedSiegelSet hG hi D hK hρ C R T₁ Tp := by
        by_contra hn
        exact zero_ne_one (by simpa only [siegelIndicator, ite_eq_right hn] using hF₁)
      obtain ⟨z, hz, hzY⟩ := he
      let zΓ : Γ :=
        ⟨z, rationalImage_le_rationalSubgroup _ ((mem_parabolicRationalImage_iff _ _).mp hz)⟩
      have hzΓ : zΓ ∈ PΓ(R) :=
        (mem_parabolicRationalSubgroup_iff_mem_parabolicRationalImage zΓ).mpr hz
      let δ := zΓ * (Quotient.out c : Γ)
      have hδ : Quotient.mk _ δ = c := by
        rw [← Quotient.out_eq c]
        apply Quotient.sound
        change QuotientGroup.rightRel (PΓ(R)) δ (Quotient.out c)
        rw [QuotientGroup.rightRel_apply]
        simpa only [δ, mul_inv_rev, mul_inv_cancel_left] using (PΓ(R)).inv_mem hzΓ
      have hδY : δ.val * x = z * y := mul_assoc _ _ _
      have hN₁ : δ.val * x ∈ normOneSubgroup F G := (normOneSubgroup F G).mul_mem
        (rationalSubgroup_le_normOneSubgroup F G δ.2) hx
      have hσ₂ : σ₀ (R : Set (characterLattice T)) S (H₀(δ.val * x) - Tp) = 1 := by
        rw [hδY, sigma_height_mul_left' hG hi hν D hK hρ Tp hRS hS hz, hσ₁]
      obtain ⟨p, hp, a, ha, k, hk, hpak⟩ := exists_sigmaTorusRegion_of_mem' hG hi hν D hK hρ C T₁
        Tp hC (hδY ▸ hzY) hσ₂ hN₁
      exact ⟨δ, hδ, Or.inr ⟨hcoeff, z, hz, hδY, p, hp, a, ha, k, hk, hpak⟩⟩
  choose δ hδ hcase using hrep
  choose q hq using fun c => (δ c).property
  let emb : PQuot(R) ↪ RationalGroupPoints F G :=
    ⟨q, fun c c' hc => by
      have hδeq : δ c = δ c' :=
        Subtype.ext ((hq c).symm.trans ((congrArg (rational F G) hc).trans (hq c')))
      exact (hδ c).symm.trans ((congrArg (Quotient.mk _) hδeq).trans (hδ c'))⟩
  refine ⟨emb, fun c Ω' _ mΩ φ r hr hφ hm M hgrowth => ?_⟩
  change _ * ENNReal.ofReal (Hρ (rational F G (q c) * x) ^ m) ≤ _
  rw [hq]
  rcases hcase c with h0 | ⟨h1, z, hz, hδz, p, hp, a, ha, k, hk, hpak⟩
  · simp only [h0, Int.cast_zero, zero_mul, enorm_zero, lintegral_zero, zero_le]
  · have hb (o : Ω') : (coeff R S (((Quotient.out c : Γ) : A) * x) : ℂ) *
        alternatingConstantTerm (ν := ν) hG hi R S (normOneExtension hG (φ o))
          (((Quotient.out c : Γ) : A) * x) =
        alternatingConstantTerm (ν := ν) hG hi R S (normOneExtension hG (φ o))
          ((δ c).val * x) := by
      have h := alternatingConstantTerm_mul_left' hG hi hν hS
        (normOneExtensionCRF hG (φ o) (continuous_of_isNormOneCr At hK₀o (hφ o)) (hφ o).1) hz
        (((Quotient.out c : Γ) : A) * x)
      rw [evaluate_normOneExtensionCRF] at h
      rw [h1, Int.cast_one, one_mul, hδz, h]
    simp only [hb]
    have hN₁ : (δ c).val * x ∈ normOneSubgroup F G := (normOneSubgroup F G).mul_mem
      (rationalSubgroup_le_normOneSubgroup F G (δ c).2) hx
    rw [← hpak] at hN₁ ⊢
    exact hDecay p hp a ha k hk hN₁ mΩ φ r hr hφ hm M hgrowth

end Representatives

include hν in
/-- **The family estimate (13.5)–(13.6) for a compact Iwasawa subgroup.** For every closed matrix
realization there is a threshold `c` such that the fixed-level family estimate holds for every
truncation parameter `T` with `β(T) > c` for all simple relative roots `β`. -/
theorem exists_isNormOneFamilyEstimate (hN : 0 < N) (hClosed : IsClosedSubgroup ρ) :
    ∃ c : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, c < eval T β Tp) →
      IsNormOneFamilyEstimate.{u, w} At hG hi D hK hρ ρ Tp := by
  obtain ⟨C₀, T₀, hC₀, hcover⟩ := iwasawaSiegelCovering F G T i ν hG hi hν K hK hρ
  have hred := iwasawaSiegelReduction F G T i ν hG hi hν K hK hρ
  obtain ⟨c, hRegroup⟩ := arthurTruncationSigmaExpansion hG hi hν D hK hρ C₀ T₀ hC₀ hcover hred
  refine ⟨c, fun Tp hTp => ?_⟩
  intro C hC T₁ n n₀ _ _ K₀ hK₀ hK₀o
  let W := siegelSigmaCoefficient hG hi D hK hρ C₀ T₀ Tp
  obtain ⟨Cmin, hCmin, hmin⟩ := arthurSiegelNormMinimality F G T i ν hG hi hν K hK hρ ρ hN C T₁
  obtain ⟨a₀, ha₀⟩ := rationalAdelicHeightSummability F G ρ hN hClosed
  obtain ⟨m, Csum, hCsum, hsum⟩ := siegelCosetSumDecay.{u, u} F G ρ hN a₀ ha₀ Cmin hCmin n
  have hPair (R S : J) : ∃ (nw : ℕ) (B : ℝ), 0 ≤ B ∧ (R ⊆ S → S ⊆ Δ → ∀ x ∈ G¹,
      ∃ emb : PQuot(R) ↪ RationalGroupPoints F G, ∀ c : PQuot(R),
      ∀ {Ω' : Type w} [MeasurableSpace Ω'] (mΩ : Measure Ω') (φ : Ω' → G¹ → ℂ) (r : ℕ),
      nw ≤ r → (∀ o, IsNormOneCr At r K₀ hK₀ (φ o)) →
      Measurable (fun q : Ω' × G¹ => φ q.1 q.2) →
      ∀ M : ℝ≥0∞, (∀ w : List (Fin e), w.length ≤ nw → ∀ y : G¹,
          ∫⁻ o, ‖normOneWordDerivative At w (φ o) y‖ₑ ∂mΩ ≤ ENNReal.ofReal (Hρ y ^ n₀) * M) →
      (∫⁻ o, ‖(W R S (((Quotient.out c : Γ) : A) * x) : ℂ) *
          alternatingConstantTerm (ν := ν) hG hi R S (normOneExtension hG (φ o))
            (((Quotient.out c : Γ) : A) * x)‖ₑ ∂mΩ) *
        ENNReal.ofReal (Hρ (rational F G (emb c) * x) ^ m) ≤ ENNReal.ofReal B * M) := by
    by_cases h : R ⊆ S ∧ S ⊆ Δ
    · obtain ⟨nw, B, hB, h'⟩ := exists_sigmaCoset_representatives_familyBound.{u, w} hG hi hν D hK
        hρ At ρ C₀ T₀ Tp hN hC₀ h.1 h.2 hK₀ hK₀o n₀ m
      exact ⟨nw, B, hB, fun _ _ => h'⟩
    · exact ⟨0, 0, le_rfl, fun hRS hS => (h ⟨hRS, hS⟩).elim⟩
  choose nw B hB hBound using hPair
  let r : ℕ := (∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset, nw R S) + 1
  have hnwr (R S : J) (hR : R ∈ (Δ).powerset) (hS : S ∈ (Δ).powerset) : nw R S ≤ r := by
    have h1 : nw R S ≤ ∑ S' ∈ (Δ).powerset, nw R S' :=
      Finset.single_le_sum (f := fun S' => nw R S') (fun _ _ => Nat.zero_le _) hS
    have h2 : ∑ S' ∈ (Δ).powerset, nw R S' ≤ ∑ R' ∈ (Δ).powerset, ∑ S' ∈ (Δ).powerset, nw R' S' :=
      Finset.single_le_sum (f := fun R' => ∑ S' ∈ (Δ).powerset, nw R' S') (fun _ _ => Nat.zero_le _)
        hR
    exact (h1.trans h2).trans (Nat.le_succ _)
  let ops := (normOneWordsUpTo e r).image normOneWord
  let Bsum : ℝ := ∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset.filter (R ⊆ ·), Csum * B R S
  have hBsum : 0 ≤ Bsum :=
    Finset.sum_nonneg fun R _ => Finset.sum_nonneg fun S _ => mul_nonneg hCsum (hB R S)
  refine ⟨r, ops, Real.toNNReal (Bsum + 1), Nat.succ_pos _, ?_, ?_⟩
  · intro X hX
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hX
    exact fun v hv => (normOneWord_orderLE w v hv).trans (mem_normOneWordsUpTo.mp hw)
  intro Ω' _ mΩ φ hφ hm x hx
  have hcont (o : Ω') : Continuous (φ o) := continuous_of_isNormOneCr At hK₀o (hφ o)
  let Hs := adelicSourceNorm F G ρ
  let t (R S : J) (dc : PQuot(R)) (o : Ω') : ℂ :=
    (W R S (((Quotient.out dc : Γ) : A) * x) : ℂ) *
      alternatingConstantTerm (ν := ν) hG hi R S (normOneExtension hG (φ o))
        (((Quotient.out dc : Γ) : A) * x)
  let Fs (R S : J) : Finset (PQuot(R)) := if h : S ⊆ Δ ∧ R ⊆ S then
      ((hRegroup Tp hTp 0 x).1 S h.1 R h.2).toFinset else ∅
  have hFs (R S : J) (hS : S ⊆ Δ) (hR : R ⊆ S) (dc : PQuot(R)) (hd : dc ∉ Fs R S) (o : Ω') :
      t R S dc o = 0 := by
    have hW : W R S (((Quotient.out dc : Γ) : A) * x) = 0 := by
      simp only [Fs, dite_eq_left (show S ⊆ Δ ∧ R ⊆ S from ⟨hS, hR⟩), Set.Finite.mem_toFinset,
        Function.mem_support, not_not] at hd
      exact hd
    simp only [t, hW, Int.cast_zero, zero_mul]
  have hexp (o : Ω') : normOneTruncation hG hi D hK hρ Tp (φ o) x =
      ∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset.filter (R ⊆ ·), ∑ dc ∈ Fs R S, t R S dc o := by
    have h1 : normOneTruncation hG hi D hK hρ Tp (φ o) x =
        truncation hG hi D hK hρ Tp
          (evaluate F G (normOneExtensionCRF hG (φ o) (hcont o) (hφ o).1)) x := by
      rw [evaluate_normOneExtensionCRF]
      exact truncation_congr_on_normOne hG hi D hK hρ hν Tp (fun y hy =>
        (normOneExtend_coe (φ o) ⟨y, hy⟩).trans (normOneExtension_coe hG (φ o) ⟨y, hy⟩).symm) x
    rw [h1, (hRegroup Tp hTp _ x).2]
    simp only [evaluate_normOneExtensionCRF]
    refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun S hS => ?_
    obtain ⟨hSΔ, hRS⟩ := Finset.mem_filter.mp hS
    exact tsum_eq_sum fun dc hd => hFs R S (Finset.mem_powerset.mp hSΔ) hRS dc hd o
  have hmt (R S : J) (hS : S ⊆ Δ) (dc : PQuot(R)) : Measurable (t R S dc) :=
    measurable_const.mul (measurable_alternatingConstantTerm_normOneExtension hG hi hν At hS hK₀o
      hφ hm _)
  have hmS (R S : J) (hS : S ∈ (Δ).powerset.filter (R ⊆ ·)) (dc : PQuot(R)) :
      Measurable fun o => ‖t R S dc o‖ₑ :=
    (hmt R S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) dc).enorm
  have hmeas : Measurable (fun o => normOneTruncation hG hi D hK hρ Tp (φ o) x) := by
    rw [show (fun o => normOneTruncation hG hi D hK hρ Tp (φ o) x) = fun o =>
      ∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset.filter (R ⊆ ·), ∑ dc ∈ Fs R S, t R S dc o from
        funext hexp]
    exact Finset.measurable_sum _ fun R _ => Finset.measurable_sum _ fun S hS =>
      Finset.measurable_sum _ fun dc _ =>
        hmt R S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) dc
  refine ⟨hmeas, ?_⟩
  change _ ≤ ENNReal.ofReal (Bsum + 1) * _
  set Mt := ⨆ y : normOneSubgroup F G, ENNReal.ofReal (Hs y ^ (-(n₀ : ℝ))) *
      ∑ X ∈ ops, ∫⁻ o, ENNReal.ofReal ‖normOneDifferential At X (φ o) y‖ ∂mΩ with hMt
  by_cases htop : Mt = ⊤
  · have hpos : ENNReal.ofReal (Bsum + 1) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    rw [htop, ENNReal.mul_top hpos]
    exact le_top
  have hHsH (y : A) : Hs y ≤ Hρ y := by
    have hy : 0 < Hs y := adelicSourceNorm_pos F G ρ hN y
    rw [show Hρ y = (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult) * Hs y from
      adelicHeight_eq_scalar_mul_sourceNorm F G ρ y]
    exact le_mul_of_one_le_left hy.le (one_le_pow₀ (by exact_mod_cast hN))
  have hgrowth (w : List (Fin e)) (hw : w.length ≤ r) (y : G¹) :
      ∫⁻ o, ‖normOneWordDerivative At w (φ o) y‖ₑ ∂mΩ ≤ ENNReal.ofReal (Hρ y ^ n₀) * Mt := by
    have hHs : 0 < Hs y := adelicSourceNorm_pos F G ρ hN y
    let Sy := ∑ X ∈ ops, ∫⁻ o, ENNReal.ofReal ‖normOneDifferential At X (φ o) y‖ ∂mΩ
    have hle1 : ∫⁻ o, ‖normOneWordDerivative At w (φ o) y‖ₑ ∂mΩ ≤ Sy := by
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun X => ∫⁻ o, ENNReal.ofReal ‖normOneDifferential At X (φ o) y‖ ∂mΩ)
        (fun _ _ => bot_le) (Finset.mem_image_of_mem normOneWord (mem_normOneWordsUpTo.mpr hw)))
      refine lintegral_congr fun o => ?_
      rw [normOneDifferential_normOneWord, ofReal_norm]
    have hle2 : ENNReal.ofReal (Hs y ^ (-(n₀ : ℝ))) * Sy ≤ Mt :=
      le_iSup (fun y : normOneSubgroup F G => ENNReal.ofReal (Hs y ^ (-(n₀ : ℝ))) *
        ∑ X ∈ ops, ∫⁻ o, ENNReal.ofReal ‖normOneDifferential At X (φ o) y‖ ∂mΩ) y
    have hone : ENNReal.ofReal (Hs y ^ n₀) * ENNReal.ofReal (Hs y ^ (-(n₀ : ℝ))) = 1 := by
      rw [← ENNReal.ofReal_mul (pow_nonneg hHs.le _), Real.rpow_neg hHs.le, Real.rpow_natCast,
        mul_inv_cancel₀ (pow_ne_zero _ hHs.ne'), ENNReal.ofReal_one]
    calc
      _ ≤ Sy := hle1
      _ = ENNReal.ofReal (Hs y ^ n₀) * (ENNReal.ofReal (Hs y ^ (-(n₀ : ℝ))) * Sy) := by
        rw [← mul_assoc, hone, one_mul]
      _ ≤ ENNReal.ofReal (Hs y ^ n₀) * Mt := mul_le_mul' le_rfl hle2
      _ ≤ ENNReal.ofReal (Hρ y ^ n₀) * Mt :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hHs.le (hHsH y) _)) le_rfl
  let I (R S : J) (dc : PQuot(R)) : ℝ≥0∞ := ∫⁻ o, ‖t R S dc o‖ₑ ∂mΩ
  have hHx : 0 < Hρ x := zero_lt_one.trans_le (one_le_adelicHeight F G ρ hN x)
  have hpair (R : J) (hR : R ∈ (Δ).powerset) (S : J) (hS : S ∈ (Δ).powerset.filter (R ⊆ ·)) :
      (∑ dc ∈ Fs R S, I R S dc) * ENNReal.ofReal (Hρ x ^ n) ≤
        ENNReal.ofReal (Csum * B R S) * Mt := by
    obtain ⟨hSΔ', hRS⟩ := Finset.mem_filter.mp hS
    have hSΔ := Finset.mem_powerset.mp hSΔ'
    obtain ⟨emb, hemb⟩ := hBound R S hRS hSΔ x x.2
    have hfinite (dc : PQuot(R)) : I R S dc ≠ ⊤ ∧
        (I R S dc).toReal * Hρ (rational F G (emb dc) * x) ^ m ≤ B R S * Mt.toReal :=
      toReal_bound_of_le (one_le_pow₀ (one_le_adelicHeight F G ρ hN _)) (hB R S) htop
        (hemb dc mΩ φ r (hnwr R S hR hSΔ') hφ hm Mt
          (fun w hw => hgrowth w (hw.trans (hnwr R S hR hSΔ'))))
    let Jt := {dc // dc ∈ Fs R S}
    let embJ : Jt ↪ RationalGroupPoints F G := (Function.Embedding.subtype _).trans emb
    have h := (hsum x Jt embJ (fun j => ((I R S j.val).toReal : ℂ)) (B R S * Mt.toReal)
      (mul_nonneg (hB R S) ENNReal.toReal_nonneg) (fun j => hmin x hx (emb j.val))
      (fun j => by
        rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
        exact (hfinite j.val).2)).2
    rw [tsum_fintype] at h
    have hsumeq : (∑ j : Jt, ((I R S j.val).toReal : ℂ)) =
        ((∑ dc ∈ Fs R S, (I R S dc).toReal : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_coe_sort (Fs R S) (fun dc => ((I R S dc).toReal : ℂ))
    have hnn : 0 ≤ ∑ dc ∈ Fs R S, (I R S dc).toReal :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    rw [hsumeq, Complex.norm_real, Real.norm_of_nonneg hnn] at h
    have hsumI : ∑ dc ∈ Fs R S, I R S dc = ENNReal.ofReal (∑ dc ∈ Fs R S, (I R S dc).toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
      exact Finset.sum_congr rfl fun dc _ => (ENNReal.ofReal_toReal (hfinite dc).1).symm
    rw [hsumI, ← ENNReal.ofReal_mul hnn]
    calc
      _ ≤ ENNReal.ofReal (Csum * B R S * Mt.toReal) :=
        ENNReal.ofReal_le_ofReal (h.trans_eq (by ring))
      _ = ENNReal.ofReal (Csum * B R S) * Mt := by
        rw [ENNReal.ofReal_mul (mul_nonneg hCsum (hB R S)), ENNReal.ofReal_toReal htop]
  have hint : ∫⁻ o, ∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset.filter (R ⊆ ·),
      ∑ dc ∈ Fs R S, ‖t R S dc o‖ₑ ∂mΩ =
        ∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset.filter (R ⊆ ·), ∑ dc ∈ Fs R S, I R S dc := by
    rw [lintegral_finsetSum _ fun R _ => Finset.measurable_sum _ fun S hS =>
      Finset.measurable_sum _ fun dc _ => hmS R S hS dc]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [lintegral_finsetSum _ fun S hS => Finset.measurable_sum _ fun dc _ => hmS R S hS dc]
    refine Finset.sum_congr rfl fun S hS => ?_
    exact lintegral_finsetSum _ fun dc _ => hmS R S hS dc
  calc
    ENNReal.ofReal (Hs x ^ (n : ℝ)) *
        ∫⁻ o, ENNReal.ofReal ‖normOneTruncation hG hi D hK hρ Tp (φ o) x‖ ∂mΩ
      ≤ ENNReal.ofReal (Hρ x ^ n) * ∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset.filter (R ⊆ ·),
          ∑ dc ∈ Fs R S, I R S dc := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) ?_
        · rw [Real.rpow_natCast]
          exact pow_le_pow_left₀ (adelicSourceNorm_pos F G ρ hN x).le (hHsH x) n
        · rw [← hint]
          refine lintegral_mono fun o => ?_
          rw [ofReal_norm, hexp]
          exact (enorm_sum_le _ _).trans (Finset.sum_le_sum fun R _ => (enorm_sum_le _ _).trans
            (Finset.sum_le_sum fun S _ => enorm_sum_le _ _))
    _ = ∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset.filter (R ⊆ ·),
          (∑ dc ∈ Fs R S, I R S dc) * ENNReal.ofReal (Hρ x ^ n) := by
        rw [mul_comm, Finset.sum_mul]
        exact Finset.sum_congr rfl fun R _ => Finset.sum_mul _ _ _
    _ ≤ ∑ R ∈ (Δ).powerset, ∑ S ∈ (Δ).powerset.filter (R ⊆ ·),
          ENNReal.ofReal (Csum * B R S) * Mt :=
        Finset.sum_le_sum fun R hR => Finset.sum_le_sum fun S hS => hpair R hR S hS
    _ = ENNReal.ofReal Bsum * Mt := by
        simp only [← Finset.sum_mul]
        congr 1
        rw [ENNReal.ofReal_sum_of_nonneg fun R _ =>
          Finset.sum_nonneg fun S _ => mul_nonneg hCsum (hB R S)]
        exact Finset.sum_congr rfl fun R _ =>
          (ENNReal.ofReal_sum_of_nonneg fun S _ => mul_nonneg hCsum (hB R S)).symm
    _ ≤ ENNReal.ofReal (Bsum + 1) * Mt :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end Langlands.Global.ArthurTruncation
