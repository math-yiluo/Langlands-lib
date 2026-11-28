import Langlands.Global.ArthurTruncationL2Quotient
import Langlands.Global.ArthurTruncationStatement
import Langlands.Global.ArthurTruncationSelfAdjointProof
import Langlands.Global.ArthurTruncationCentralTranslation
import Langlands.Global.AdelicFullRationalQuotientProduct
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.SplitCentralEmbedding

/-! # Orthogonal projection extensions of Arthur truncation from the pointwise statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set ComplexConjugate
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅)) (Tp : V T)

/-- Truncation is homogeneous for constant scalars: the constant terms are integrals and the
coset sums are unconditional sums, both of which commute with multiplication by a constant. -/
theorem truncation_const_mul (c : ℂ) (φ : AdelicGroupPoints F G → ℂ) (x : AdelicGroupPoints F G) :
    truncation hG hi D hK hρ Tp (fun y => c * φ y) x = c * truncation hG hi D hK hρ Tp φ x := by
  unfold truncation constantTerm subgroupConstantTerm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp_rw [integral_const_mul, mul_assoc c]
  rw [tsum_mul_left]
  ring

/-- **The full quotient.** At a fixed truncation parameter, preservation of locally bounded
invariant functions, pointwise idempotence and the compact-support pairing give the orthogonal
projection extension on `L²(G(F) \ G(𝔸_F))`. -/
theorem isOrthogonalL2Extension_truncation
    (hB : ∀ φ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      IsLocallyBoundedInvariant (rationalSubgroup F G) (truncation hG hi D hK hρ Tp φ))
    (hI : ∀ φ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      truncation hG hi D hK hρ Tp (truncation hG hi D hK hρ Tp φ) =
        truncation hG hi D hK hρ Tp φ)
    (hP : ∀ φ₁ φ₂ : AdelicGroupPoints F G → ℂ,
      IsLocallyBoundedInvariant (rationalSubgroup F G) φ₁ →
      Continuous φ₂ → (∀ g ∈ rationalSubgroup F G, ∀ x, φ₂ (g * x) = φ₂ x) →
      (∃ Cs : Set (AdelicGroupPoints F G), IsCompact Cs ∧
        ∀ x, φ₂ x ≠ 0 → ∃ g ∈ rationalSubgroup F G, g * x ∈ Cs) →
      Integrable (fun y : RationalQuotient F G =>
          φ₁ y.out * conj (truncation hG hi D hK hρ Tp φ₂ y.out))
        (rationalQuotientHaarMeasure F G) ∧
        ∫ y, truncation hG hi D hK hρ Tp φ₁ y.out * conj (φ₂ y.out)
            ∂(rationalQuotientHaarMeasure F G) =
          ∫ y, φ₁ y.out * conj (truncation hG hi D hK hρ Tp φ₂ y.out)
            ∂(rationalQuotientHaarMeasure F G)) :
    IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)
      (fun f q => truncation hG hi D hK hρ Tp
        (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out) :=
  isOrthogonalL2Extension_leftCosetSpace (rationalSubgroup F G) _ _
    (fun φ h1 h2 h3 => hB φ ⟨h1, h2, h3⟩) (fun φ h1 h2 h3 => hI φ ⟨h1, h2, h3⟩)
    (fun φ₁ φ₂ h1 h2 h3 hc hinv hcs => hP φ₁ φ₂ ⟨h1, h2, h3⟩ hc hinv hcs)

section NormOne

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The zero extension of a measurable function on `G(𝔸_F)¹`, bounded on compact sets and left
invariant under the principal norm-one subgroup, is locally bounded, measurable and left
`G(F)`-invariant on `G(𝔸_F)`. -/
theorem isLocallyBoundedInvariant_normOneExtend {φ : normOneSubgroup F G → ℂ}
    (hm : Measurable φ)
    (hb : ∀ C : Set (normOneSubgroup F G), IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖φ x‖ ≤ M)
    (hinv : ∀ g ∈ rationalNormOneSubgroup F G, ∀ x, φ (g * x) = φ x) :
    IsLocallyBoundedInvariant (rationalSubgroup F G) (normOneExtend φ) := by
  classical
  have hclosed := isClosed_normOneSubgroup F G
  refine ⟨?_, ?_, ?_⟩
  · unfold normOneExtend
    exact Measurable.dite hm measurable_const hclosed.measurableSet
  · intro C hC
    obtain ⟨M, hM⟩ := hb _ (hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hC)
    refine ⟨max M 0, fun x hx => ?_⟩
    unfold normOneExtend
    split_ifs with h
    · exact (hM ⟨x, h⟩ hx).trans (le_max_left _ _)
    · simp
  · intro g hg x
    have hgN : g ∈ normOneSubgroup F G := rationalSubgroup_le_normOneSubgroup F G hg
    have hiff : g * x ∈ normOneSubgroup F G ↔ x ∈ normOneSubgroup F G :=
      ⟨fun h => by
        have := (normOneSubgroup F G).mul_mem ((normOneSubgroup F G).inv_mem hgN) h
        rwa [inv_mul_cancel_left] at this, fun h => (normOneSubgroup F G).mul_mem hgN h⟩
    unfold normOneExtend
    by_cases hx : x ∈ normOneSubgroup F G
    · have hgx := hiff.mpr hx
      simp only [hgx, hx, ↓reduceDIte]
      have hmem : (⟨g, hgN⟩ : normOneSubgroup F G) ∈ rationalNormOneSubgroup F G := by
        obtain ⟨q, rfl⟩ := hg
        exact ⟨q, rfl⟩
      exact hinv _ hmem ⟨x, hx⟩
    · have hgx : g * x ∉ normOneSubgroup F G := mt hiff.mp hx
      simp only [hgx, hx, ↓reduceDIte]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem mem_rationalSubgroup_of_mem_rationalNormOne {g : normOneSubgroup F G}
    (hg : g ∈ rationalNormOneSubgroup F G) :
    (g : AdelicGroupPoints F G) ∈ rationalSubgroup F G := by
  obtain ⟨q, rfl⟩ := hg
  exact ⟨q, rfl⟩

/-- The norm-one truncation preserves measurable functions bounded on compact sets and left
invariant under the principal norm-one subgroup. -/
theorem normOneTruncation_locallyBounded
    (hB : ∀ φ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      IsLocallyBoundedInvariant (rationalSubgroup F G) (truncation hG hi D hK hρ Tp φ))
    {φ : normOneSubgroup F G → ℂ} (hm : Measurable φ)
    (hb : ∀ C : Set (normOneSubgroup F G), IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖φ x‖ ≤ M)
    (hinv : ∀ g ∈ rationalNormOneSubgroup F G, ∀ x, φ (g * x) = φ x) :
    Measurable (normOneTruncation hG hi D hK hρ Tp φ) ∧
      (∀ C : Set (normOneSubgroup F G), IsCompact C →
        ∃ M : ℝ, ∀ x ∈ C, ‖normOneTruncation hG hi D hK hρ Tp φ x‖ ≤ M) ∧
      ∀ g ∈ rationalNormOneSubgroup F G, ∀ x,
        normOneTruncation hG hi D hK hρ Tp φ (g * x) = normOneTruncation hG hi D hK hρ Tp φ x := by
  obtain ⟨h1, h2, h3⟩ := hB _ (isLocallyBoundedInvariant_normOneExtend hm hb hinv)
  refine ⟨h1.comp measurable_subtype_coe, fun C hC => ?_, fun g hg x => ?_⟩
  · obtain ⟨M, hM⟩ := h2 _ (hC.image continuous_subtype_val)
    exact ⟨M, fun x hx => hM _ ⟨x, hx, rfl⟩⟩
  · exact h3 _ (mem_rationalSubgroup_of_mem_rationalNormOne hg) x

/-- Pointwise idempotence of the norm-one truncation, from that of the full truncation. -/
theorem normOneTruncation_idem (hν : IsGenericCocharacter i ν)
    (hI : ∀ φ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      truncation hG hi D hK hρ Tp (truncation hG hi D hK hρ Tp φ) =
        truncation hG hi D hK hρ Tp φ)
    {φ : normOneSubgroup F G → ℂ} (hm : Measurable φ)
    (hb : ∀ C : Set (normOneSubgroup F G), IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖φ x‖ ≤ M)
    (hinv : ∀ g ∈ rationalNormOneSubgroup F G, ∀ x, φ (g * x) = φ x) :
    normOneTruncation hG hi D hK hρ Tp (normOneTruncation hG hi D hK hρ Tp φ) =
      normOneTruncation hG hi D hK hρ Tp φ := by
  funext x
  have hΦ := isLocallyBoundedInvariant_normOneExtend hm hb hinv
  calc normOneTruncation hG hi D hK hρ Tp (normOneTruncation hG hi D hK hρ Tp φ) x
      = normOneTruncation hG hi D hK hρ Tp
          (fun y => truncation hG hi D hK hρ Tp (normOneExtend φ) y) x := rfl
    _ = truncation hG hi D hK hρ Tp (truncation hG hi D hK hρ Tp (normOneExtend φ)) x :=
        normOneTruncation_restrict hG hi D hK hρ hν Tp _ x
    _ = truncation hG hi D hK hρ Tp (normOneExtend φ) x := by rw [hI _ hΦ]

end NormOne

section Pairing

/-- A nonnegative continuous compactly supported bump with value `1` at a given point has
positive integral for a measure that is positive on open sets. -/
theorem exists_bump_integral_pos {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] (mY : Measure Y)
    [mY.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts mY] (y : Y) :
    ∃ χ : Y → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ 0 ≤ χ ∧ χ y ≠ 0 ∧
      0 < ∫ x, χ x ∂mY := by
  obtain ⟨bump, hb1, -, hbc, hb01⟩ := exists_continuous_one_zero_of_isCompact
    isCompact_singleton isClosed_empty (Set.disjoint_empty {y})
  have hy : bump y ≠ 0 := by rw [hb1 (Set.mem_singleton y)]; norm_num
  exact ⟨bump, bump.continuous, hbc, fun x => (hb01 x).1, hy,
    bump.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hbc (fun x => (hb01 x).1) hy⟩

open PositiveRealTorus

variable (A : CommGroupScheme (Spec (CommRingCat.of F))) (jA : A.toGrp ⟶ G)
  (hinj : Function.Injective (characterRestrict jA)) [(characterRestrict jA).range.FiniteIndex]
  (J : Type u) [Fintype J] (e : A.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) J)
  (hc : IsCentral jA)

omit [NumberField F] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- A left `G(F)`-invariant function at the representative of the class with positive
coordinate `a` and norm-one class `q`. -/
theorem apply_out_rationalQuotientDecomposition [NumberField F] [IsAffineHom G.X.hom]
    {θ : AdelicGroupPoints F G → ℂ}
    (hθ : ∀ g ∈ rationalSubgroup F G, ∀ x, θ (g * x) = θ x)
    (a : intrinsicSubgroup F A) (q : NormOneRationalQuotient F G) :
    θ (rationalQuotientDecomposition F G A jA hinj J e hc (a, q)).out =
      θ (positivePointMap F G A jA a * (q.out : AdelicGroupPoints F G)) := by
  have hq : q = LeftCosetSpace.mk (rationalNormOneSubgroup F G) q.out :=
    (LeftCosetSpace.mk_out _ q).symm
  conv_lhs => rw [hq]
  rw [rationalQuotientDecomposition_mk, LeftCosetSpace.apply_out_mk _ hθ]

include hinj e hc in
/-- **The norm-one pairing.** Given a split central torus `A ⟶ T ⟶ G` with the hypotheses of
`rationalQuotientDecomposition`, the compact-support pairing for the full truncation at a
parameter `Tp` gives the compact-support pairing for the norm-one truncation at `Tp`. -/
theorem normOneTruncation_pairing_of_split (hν : IsGenericCocharacter i ν)
    (hA : IsSplitTorus A.toGrp) (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ i = jA)
    (hB : ∀ φ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      IsLocallyBoundedInvariant (rationalSubgroup F G) (truncation hG hi D hK hρ Tp φ))
    (hP : ∀ φ₁ φ₂ : AdelicGroupPoints F G → ℂ,
      IsLocallyBoundedInvariant (rationalSubgroup F G) φ₁ →
      Continuous φ₂ → (∀ g ∈ rationalSubgroup F G, ∀ x, φ₂ (g * x) = φ₂ x) →
      (∃ Cs : Set (AdelicGroupPoints F G), IsCompact Cs ∧
        ∀ x, φ₂ x ≠ 0 → ∃ g ∈ rationalSubgroup F G, g * x ∈ Cs) →
      Integrable (fun y : RationalQuotient F G =>
          φ₁ y.out * conj (truncation hG hi D hK hρ Tp φ₂ y.out))
        (rationalQuotientHaarMeasure F G) ∧
        ∫ y, truncation hG hi D hK hρ Tp φ₁ y.out * conj (φ₂ y.out)
            ∂(rationalQuotientHaarMeasure F G) =
          ∫ y, φ₁ y.out * conj (truncation hG hi D hK hρ Tp φ₂ y.out)
            ∂(rationalQuotientHaarMeasure F G))
    {φ₁ φ₂ : normOneSubgroup F G → ℂ} (hm₁ : Measurable φ₁)
    (hb₁ : ∀ C : Set (normOneSubgroup F G), IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖φ₁ x‖ ≤ M)
    (hinv₁ : ∀ g ∈ rationalNormOneSubgroup F G, ∀ x, φ₁ (g * x) = φ₁ x)
    (hc₂ : Continuous φ₂) (hinv₂ : ∀ g ∈ rationalNormOneSubgroup F G, ∀ x, φ₂ (g * x) = φ₂ x)
    (hcs₂ : ∃ Cs : Set (normOneSubgroup F G), IsCompact Cs ∧
      ∀ x, φ₂ x ≠ 0 → ∃ g ∈ rationalNormOneSubgroup F G, g * x ∈ Cs) :
    Integrable (fun y : NormOneRationalQuotient F G =>
        φ₁ y.out * conj (normOneTruncation hG hi D hK hρ Tp φ₂ y.out))
      (normOneRationalQuotientHaarMeasure F G) ∧
      ∫ y, normOneTruncation hG hi D hK hρ Tp φ₁ y.out * conj (φ₂ y.out)
          ∂(normOneRationalQuotientHaarMeasure F G) =
        ∫ y, φ₁ y.out * conj (normOneTruncation hG hi D hK hρ Tp φ₂ y.out)
          ∂(normOneRationalQuotientHaarMeasure F G) := by
  classical
  let π := normOneProjection F G A jA hinj J e hc
  let pf := positiveFactor F G A jA hinj J e
  let Q := rationalQuotientDecomposition F G A jA hinj J e hc
  let mA := normalizedPositiveHaarMeasure F G A jA hinj J e hc
  have hQ : MeasurePreserving Q (mA.prod (normOneRationalQuotientHaarMeasure F G))
      (rationalQuotientHaarMeasure F G) :=
    measurePreserving_rationalQuotientDecomposition F G A jA hinj J e hc
  have : SigmaFinite mA := normalizedPositiveHaarMeasure_sigmaFinite F G A jA hinj J e hc
  have : mA.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure F G A jA hinj J e hc
  have := positiveLocallyCompactSpace F A J e
  have : T2Space (intrinsicSubgroup F A) :=
    (positiveLogCoordinateEquiv F A J e).toHomeomorph.isEmbedding.t2Space
  have hπ1 : ∀ a, π (positivePointMap F G A jA a) = 1 :=
    normOneProjection_positivePointMap F G A jA hinj J e hc
  have hπn : ∀ n : normOneSubgroup F G, π n = n := normOneProjection_normOne F G A jA hinj J e hc
  have hpf1 : ∀ a, pf (positivePointMap F G A jA a) = a :=
    positiveFactor_positivePointMap F G A jA hinj J e
  have hpfn : ∀ n : normOneSubgroup F G, pf n = 1 := positiveFactor_normOne F G A jA hinj J e
  have hout : ∀ θ : AdelicGroupPoints F G → ℂ, (∀ g ∈ rationalSubgroup F G, ∀ x, θ (g * x) = θ x) →
      ∀ a q, θ (Q (a, q)).out = θ (positivePointMap F G A jA a * (q.out : AdelicGroupPoints F G)) :=
    fun θ hθ a q => apply_out_rationalQuotientDecomposition A jA hinj J e hc hθ a q
  -- a bump on the positive points
  obtain ⟨χr, hχc, hχs, hχ0, hχ1, hχpos⟩ := exists_bump_integral_pos mA 1
  let χ : intrinsicSubgroup F A → ℂ := fun a => (χr a : ℂ)
  -- rational points
  have hrat : ∀ g ∈ rationalSubgroup F G,
      π g ∈ rationalNormOneSubgroup F G ∧ pf g = 1 := by
    intro g hg
    obtain ⟨q, rfl⟩ := hg
    refine ⟨?_, ?_⟩
    · change normOneProjection F G A jA hinj J e hc (rational F G q) ∈ _
      rw [normOneProjection_rational]
      exact ⟨q, rfl⟩
    · exact positiveFactor_normOne F G A jA hinj J e (rationalNormOne F G q)
  -- the two functions on the full adelic group
  let Φ₁ : AdelicGroupPoints F G → ℂ := fun x => φ₁ (π x)
  let Ψ : AdelicGroupPoints F G → ℂ := fun x => χ (pf x) * φ₂ (π x)
  have hΦ₁ : IsLocallyBoundedInvariant (rationalSubgroup F G) Φ₁ := by
    refine ⟨hm₁.comp π.continuous.measurable, fun C hC => ?_, fun g hg x => ?_⟩
    · obtain ⟨M, hM⟩ := hb₁ _ (hC.image π.continuous)
      exact ⟨M, fun x hx => hM _ ⟨x, hx, rfl⟩⟩
    · change φ₁ (π (g * x)) = φ₁ (π x)
      rw [map_mul]
      exact hinv₁ _ (hrat g hg).1 _
  have hΨc : Continuous Ψ :=
    (Complex.continuous_ofReal.comp (hχc.comp pf.continuous)).mul (hc₂.comp π.continuous)
  have hΨinv : ∀ g ∈ rationalSubgroup F G, ∀ x, Ψ (g * x) = Ψ x := by
    intro g hg x
    change χ (pf (g * x)) * φ₂ (π (g * x)) = χ (pf x) * φ₂ (π x)
    rw [map_mul, map_mul, (hrat g hg).2, one_mul, hinv₂ _ (hrat g hg).1]
  have hΨ : IsLocallyBoundedInvariant (rationalSubgroup F G) Ψ :=
    ⟨hΨc.measurable, fun C hC => hC.exists_bound_of_continuousOn hΨc.continuousOn, hΨinv⟩
  have hΨcs : ∃ Cs : Set (AdelicGroupPoints F G), IsCompact Cs ∧
      ∀ x, Ψ x ≠ 0 → ∃ g ∈ rationalSubgroup F G, g * x ∈ Cs := by
    obtain ⟨Cs₂, hCs₂, hCs₂m⟩ := hcs₂
    refine ⟨(fun p : intrinsicSubgroup F A × normOneSubgroup F G =>
        positivePointMap F G A jA p.1 * (p.2 : AdelicGroupPoints F G)) '' (tsupport χr ×ˢ Cs₂),
      (hχs.prod hCs₂).image (((positivePointMap F G A jA).continuous.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)), fun x hx => ?_⟩
    have h1 : χr (pf x) ≠ 0 := fun h => hx (by simp [Ψ, χ, h])
    have h2 : φ₂ (π x) ≠ 0 := fun h => hx (by simp [Ψ, h])
    obtain ⟨g, hg, hgC⟩ := hCs₂m _ h2
    refine ⟨g, mem_rationalSubgroup_of_mem_rationalNormOne hg,
      ⟨(pf x, g * π x), ⟨subset_tsupport _ h1, hgC⟩, ?_⟩⟩
    have hx' : x = positivePointMap F G A jA (pf x) * (π x : AdelicGroupPoints F G) :=
      (positivePointMap_mul_normOneFactor F G A jA hinj J e x).symm
    dsimp only
    conv_rhs => rw [hx']
    rw [Subgroup.coe_mul, ← mul_assoc, ← mul_assoc,
      (positivePointMap_commute F G A jA hc (pf x) (g : AdelicGroupPoints F G)).eq]
  obtain ⟨hint, heq⟩ := hP Φ₁ Ψ hΦ₁ hΨc hΨinv hΨcs
  obtain ⟨hTm₁, -, hTinv₁⟩ := hB Φ₁ hΦ₁
  obtain ⟨hTmΨ, -, hTinvΨ⟩ := hB Ψ hΨ
  -- central translation by positive points
  have hc' : IsCentral (CommGroupScheme.groupHom f ≫ i) := by rw [hf]; exact hc
  have hz : ∀ a : intrinsicSubgroup F A,
      map F A.toGrp G (CommGroupScheme.groupHom f ≫ i) a.val = positivePointMap F G A jA a := by
    intro a
    rw [hf]
    rfl
  have hshift : ∀ (θ : AdelicGroupPoints F G → ℂ) (a : intrinsicSubgroup F A)
      (x : AdelicGroupPoints F G),
      truncation hG hi D hK hρ Tp θ (positivePointMap F G A jA a * x) =
        truncation hG hi D hK hρ Tp (fun g => θ (g * positivePointMap F G A jA a)) x := by
    intro θ a x
    have h := truncation_rightTranslate_splitCentral hi hK hρ hG D f hA hc' a.val Tp θ x
    simp only [hz a] at h
    rw [(positivePointMap_commute F G A jA hc a x).eq, h]
  have hnorm : ∀ (θ : AdelicGroupPoints F G → ℂ) (φ : normOneSubgroup F G → ℂ),
      (∀ n : normOneSubgroup F G, θ n = φ n) → ∀ n : normOneSubgroup F G,
      truncation hG hi D hK hρ Tp θ n = normOneTruncation hG hi D hK hρ Tp φ n := by
    intro θ φ hθ n
    exact truncation_congr_on_normOne hG hi D hK hρ hν Tp
      (fun y hy => (hθ ⟨y, hy⟩).trans (normOneExtend_coe φ ⟨y, hy⟩).symm) n
  -- the four functions in the product coordinates
  have hπz : ∀ (a : intrinsicSubgroup F A) (n : normOneSubgroup F G),
      π (positivePointMap F G A jA a * n) = n := by
    intro a n
    rw [map_mul, hπ1, hπn, one_mul]
  have E1 : ∀ a q, Φ₁ (Q (a, q)).out = φ₁ q.out := by
    intro a q
    rw [hout Φ₁ hΦ₁.2.2]
    exact congrArg φ₁ (hπz a q.out)
  have E3 : ∀ a q, Ψ (Q (a, q)).out = χ a * φ₂ q.out := by
    intro a q
    rw [hout Ψ hΨinv]
    change χ (pf _) * φ₂ (π _) = _
    rw [hπz, map_mul, hpf1, hpfn, mul_one]
  have E2 : ∀ a q, truncation hG hi D hK hρ Tp Φ₁ (Q (a, q)).out =
      normOneTruncation hG hi D hK hρ Tp φ₁ q.out := by
    intro a q
    rw [hout _ hTinv₁, hshift]
    have h : (fun g => Φ₁ (g * positivePointMap F G A jA a)) = Φ₁ := by
      funext g
      change φ₁ (π (g * _)) = φ₁ (π g)
      rw [map_mul, hπ1, mul_one]
    rw [h]
    exact hnorm Φ₁ φ₁ (fun n => congrArg φ₁ (hπn n)) q.out
  have E4 : ∀ a q, truncation hG hi D hK hρ Tp Ψ (Q (a, q)).out =
      χ a * normOneTruncation hG hi D hK hρ Tp φ₂ q.out := by
    intro a q
    rw [hout _ hTinvΨ, hshift]
    have h : truncation hG hi D hK hρ Tp (fun g => Ψ (g * positivePointMap F G A jA a)) q.out =
        truncation hG hi D hK hρ Tp (fun g => χ a * normOneExtend φ₂ g) q.out := by
      refine truncation_congr_on_normOne hG hi D hK hρ hν Tp (fun y hy => ?_) q.out
      change χ (pf (y * _)) * φ₂ (π (y * _)) = χ a * normOneExtend φ₂ y
      rw [map_mul, map_mul, hπ1, mul_one, hpf1, show pf y = 1 from hpfn ⟨y, hy⟩, one_mul,
        show π y = ⟨y, hy⟩ from hπn ⟨y, hy⟩, ← normOneExtend_coe φ₂ ⟨y, hy⟩]
    rw [h, truncation_const_mul]
    rfl
  -- transport of the integrals
  have hconj : Measurable (starRingEnd ℂ) := Complex.continuous_conj.measurable
  have hmeas : ∀ θ : AdelicGroupPoints F G → ℂ, Measurable θ →
      (∀ g ∈ rationalSubgroup F G, ∀ x, θ (g * x) = θ x) →
      Measurable (fun y : RationalQuotient F G => θ y.out) :=
    fun θ hθm hθ => LeftCosetSpace.measurable_out_of_invariant_complex _ hθm hθ
  have htrans : ∀ g : RationalQuotient F G → ℂ, Measurable g →
      ∫ y, g y ∂(rationalQuotientHaarMeasure F G) =
        ∫ p, g (Q p) ∂(mA.prod (normOneRationalQuotientHaarMeasure F G)) := by
    intro g hg
    rw [← hQ.map_eq, integral_map hQ.measurable.aemeasurable hg.aestronglyMeasurable]
  have hne : ∫ a, conj (χ a) ∂mA ≠ 0 := by
    simp only [χ, Complex.conj_ofReal]
    rw [show (∫ a, (χr a : ℂ) ∂mA) = ((∫ a, χr a ∂mA : ℝ) : ℂ) from integral_ofReal]
    exact Complex.ofReal_ne_zero.mpr hχpos.ne'
  have hIL : ∫ y, truncation hG hi D hK hρ Tp Φ₁ y.out * conj (Ψ y.out)
        ∂(rationalQuotientHaarMeasure F G) =
      (∫ a, conj (χ a) ∂mA) * ∫ q, normOneTruncation hG hi D hK hρ Tp φ₁ q.out * conj (φ₂ q.out)
        ∂(normOneRationalQuotientHaarMeasure F G) := by
    rw [htrans (fun y => truncation hG hi D hK hρ Tp Φ₁ y.out * conj (Ψ y.out))
      ((hmeas _ hTm₁ hTinv₁).mul (hconj.comp (hmeas _ hΨc.measurable hΨinv))),
      ← integral_prod_mul]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    obtain ⟨a, q⟩ := p
    simp only [E2, E3, map_mul]
    ring
  have hIR : ∫ y, Φ₁ y.out * conj (truncation hG hi D hK hρ Tp Ψ y.out)
        ∂(rationalQuotientHaarMeasure F G) =
      (∫ a, conj (χ a) ∂mA) * ∫ q, φ₁ q.out * conj (normOneTruncation hG hi D hK hρ Tp φ₂ q.out)
        ∂(normOneRationalQuotientHaarMeasure F G) := by
    rw [htrans (fun y => Φ₁ y.out * conj (truncation hG hi D hK hρ Tp Ψ y.out))
      ((hmeas _ hΦ₁.1 hΦ₁.2.2).mul (hconj.comp (hmeas _ hTmΨ hTinvΨ))),
      ← integral_prod_mul]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    obtain ⟨a, q⟩ := p
    simp only [E1, E4, map_mul]
    ring
  -- integrability on the norm-one quotient
  have hint2 : Integrable (fun p : intrinsicSubgroup F A × NormOneRationalQuotient F G =>
      conj (χ p.1) * (φ₁ p.2.out * conj (normOneTruncation hG hi D hK hρ Tp φ₂ p.2.out)))
      (mA.prod (normOneRationalQuotientHaarMeasure F G)) := by
    have hmR : Measurable (fun y : RationalQuotient F G =>
        Φ₁ y.out * conj (truncation hG hi D hK hρ Tp Ψ y.out)) :=
      (hmeas _ hΦ₁.1 hΦ₁.2.2).mul (hconj.comp (hmeas _ hTmΨ hTinvΨ))
    have h := hint
    rw [← hQ.map_eq] at h
    have h' := (integrable_map_measure hmR.aestronglyMeasurable hQ.measurable.aemeasurable).mp h
    refine h'.congr (ae_of_all _ fun p => ?_)
    obtain ⟨a, q⟩ := p
    simp only [Function.comp_apply, E1, E4, map_mul]
    ring
  have hae := hint2.prod_right_ae
  have hpos : 0 < mA {a | χr a ≠ 0} :=
    (isOpen_ne_fun hχc continuous_const).measure_pos mA ⟨1, hχ1⟩
  obtain ⟨a, ha, hχa⟩ : ∃ a, Integrable (fun q : NormOneRationalQuotient F G =>
      conj (χ a) * (φ₁ q.out * conj (normOneTruncation hG hi D hK hρ Tp φ₂ q.out)))
        (normOneRationalQuotientHaarMeasure F G) ∧ χr a ≠ 0 := by
    by_contra hcon
    have h0 : mA {a | χr a ≠ 0} = 0 :=
      measure_mono_null (fun a (h : χr a ≠ 0) hint' => hcon ⟨a, hint', h⟩) (ae_iff.mp hae)
    exact hpos.ne' h0
  have hca : conj (χ a) ≠ 0 := by
    simp only [χ, Complex.conj_ofReal]
    exact Complex.ofReal_ne_zero.mpr hχa
  refine ⟨(integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hca) _).mp ha, ?_⟩
  exact mul_left_cancel₀ hne (hIL.symm.trans (heq.trans hIR))

/-- **The norm-one quotient.** At a fixed truncation parameter, preservation of locally bounded
invariant functions, pointwise idempotence and the compact-support pairing for the full
truncation give the orthogonal projection extension of the norm-one truncation on
`L²(G(F) \ G(𝔸_F)¹)`. The pairing is transported through a split component of `G`, which
factors through the maximal split torus, using the product decomposition of the full quotient
and the commutation of truncation with central translations. -/
theorem isOrthogonalL2Extension_normOneTruncation (hν : IsGenericCocharacter i ν)
    (hB : ∀ φ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      IsLocallyBoundedInvariant (rationalSubgroup F G) (truncation hG hi D hK hρ Tp φ))
    (hI : ∀ φ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      truncation hG hi D hK hρ Tp (truncation hG hi D hK hρ Tp φ) =
        truncation hG hi D hK hρ Tp φ)
    (hP : ∀ φ₁ φ₂ : AdelicGroupPoints F G → ℂ,
      IsLocallyBoundedInvariant (rationalSubgroup F G) φ₁ →
      Continuous φ₂ → (∀ g ∈ rationalSubgroup F G, ∀ x, φ₂ (g * x) = φ₂ x) →
      (∃ Cs : Set (AdelicGroupPoints F G), IsCompact Cs ∧
        ∀ x, φ₂ x ≠ 0 → ∃ g ∈ rationalSubgroup F G, g * x ∈ Cs) →
      Integrable (fun y : RationalQuotient F G =>
          φ₁ y.out * conj (truncation hG hi D hK hρ Tp φ₂ y.out))
        (rationalQuotientHaarMeasure F G) ∧
        ∫ y, truncation hG hi D hK hρ Tp φ₁ y.out * conj (φ₂ y.out)
            ∂(rationalQuotientHaarMeasure F G) =
          ∫ y, φ₁ y.out * conj (truncation hG hi D hK hρ Tp φ₂ y.out)
            ∂(rationalQuotientHaarMeasure F G)) :
    IsOrthogonalL2Extension (normOneRationalQuotientHaarMeasure F G)
      (fun f q => normOneTruncation hG hi D hK hρ Tp
        (fun x => f (LeftCosetSpace.mk (rationalNormOneSubgroup F G) x)) q.out) := by
  obtain ⟨A, jA, hsc⟩ := (splitComponentStatement F G hG).1
  have hcs := hsc.isCentralSplitTorus
  have hinj := characterRestrict_injective_of_centralSplitTorusCharacter
    centralSplitTorusCharacter hG hsc
  have := hsc.finiteIndex_range_characterRestrict hG
  obtain ⟨J, hJ, ⟨e⟩⟩ := hcs.isSplitSubtorus.1
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨f, hf, -, -⟩ := hcs.exists_commFactor_of_isMaximalSplitTorus hi
  exact isOrthogonalL2Extension_leftCosetSpace (rationalNormOneSubgroup F G) _
    (normOneTruncation hG hi D hK hρ Tp)
    (fun _ h1 h2 h3 => normOneTruncation_locallyBounded hG hi D hK hρ Tp hB h1 h2 h3)
    (fun _ h1 h2 h3 => normOneTruncation_idem hG hi D hK hρ Tp hν hI h1 h2 h3)
    (fun _ _ h1 h2 h3 hc hinv hcs' => normOneTruncation_pairing_of_split hG hi D hK hρ Tp
      A jA hinj J e hcs.2 hν hcs.isSplitSubtorus.1 f hf hB hP h1 h2 h3 hc hinv hcs')

end Pairing

/-- **Reduction.** The pointwise vanishing and idempotence statement (with its suitable maximal
compact subgroup) and the compact-support pairing statement imply the orthogonal projection
extensions on both actual quotients. -/
theorem truncationOrthogonalProjection_of_projection_of_selfAdjoint
    (hproj : TruncationProjectionStatement.{u}) (hsa : TruncationSelfAdjointStatement.{u}) :
    TruncationOrthogonalProjectionStatement.{u} := by
  intro F _ _ G _ _ T i _ ν hG hi hν
  obtain ⟨K, hK, hmax, hcompat, hidem⟩ := hproj F G T i ν hG hi hν
  refine ⟨K, hK, hmax, hcompat, fun D hρ => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hidem D hρ
  obtain ⟨C₂, hC₂⟩ := hsa F G T i ν hG hi hν D K hK hρ
  refine ⟨max C₁ C₂, fun Tp hTp => ?_⟩
  have h₁ : ∀ β ∈ simpleRelativeRoots i ν, C₁ < eval T β Tp :=
    fun β hβ => (le_max_left _ _).trans_lt (hTp β hβ)
  have h₂ : ∀ β ∈ simpleRelativeRoots i ν, C₂ < eval T β Tp :=
    fun β hβ => (le_max_right _ _).trans_lt (hTp β hβ)
  obtain ⟨hloc, hpair⟩ := hC₂ Tp h₂
  have hB : ∀ φ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      IsLocallyBoundedInvariant (rationalSubgroup F G) (truncation hG hi D hK hρ Tp φ) :=
    fun φ hφ => (hloc φ hφ).1
  have hI : ∀ φ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      truncation hG hi D hK hρ Tp (truncation hG hi D hK hρ Tp φ) =
        truncation hG hi D hK hρ Tp φ :=
    fun φ hφ => (hC₁ Tp h₁ φ hφ).2
  have hP : ∀ φ₁ φ₂ : AdelicGroupPoints F G → ℂ,
      IsLocallyBoundedInvariant (rationalSubgroup F G) φ₁ →
      Continuous φ₂ → (∀ g ∈ rationalSubgroup F G, ∀ x, φ₂ (g * x) = φ₂ x) →
      (∃ Cs : Set (AdelicGroupPoints F G), IsCompact Cs ∧
        ∀ x, φ₂ x ≠ 0 → ∃ g ∈ rationalSubgroup F G, g * x ∈ Cs) →
      Integrable (fun y : RationalQuotient F G =>
          φ₁ y.out * conj (truncation hG hi D hK hρ Tp φ₂ y.out))
        (rationalQuotientHaarMeasure F G) ∧
        ∫ y, truncation hG hi D hK hρ Tp φ₁ y.out * conj (φ₂ y.out)
            ∂(rationalQuotientHaarMeasure F G) =
          ∫ y, φ₁ y.out * conj (truncation hG hi D hK hρ Tp φ₂ y.out)
            ∂(rationalQuotientHaarMeasure F G) := by
    intro φ₁ φ₂ hφ₁ hc hinv hcs
    obtain ⟨-, hint, heq⟩ := hpair φ₁ φ₂ hφ₁ hc hinv hcs
    exact ⟨hint, heq⟩
  exact ⟨isOrthogonalL2Extension_normOneTruncation hG hi D hK hρ Tp hν hB hI hP,
    isOrthogonalL2Extension_truncation hG hi D hK hρ Tp hB hI hP⟩

/-- The orthogonal projection extensions follow from the pointwise vanishing and idempotence
statement alone, the pairing statement being `truncationSelfAdjoint`. -/
theorem truncationOrthogonalProjection_of_projection
    (hproj : TruncationProjectionStatement.{u}) :
    TruncationOrthogonalProjectionStatement.{u} :=
  truncationOrthogonalProjection_of_projection_of_selfAdjoint hproj truncationSelfAdjoint

end Langlands.Global.ArthurTruncation
