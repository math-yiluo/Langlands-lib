import Langlands.Global.AdelicCuspidalExponentRegionBound
import Langlands.Global.ArthurSiegelCoveringProof
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.GroupScheme.Rational.StandardLeviRealDecompositionProof
import Langlands.GroupScheme.Rational.ArthurRelativeCombinatorics
import Langlands.Representation.Exponents.MaximalLeviExponentTransport

/-! # Boundedness on the fibres of the Iwasawa height `H_{P_R}`

Reduction theory relative to `P_R` (a family form of the published `iwasawaSiegelCovering`
argument) moves every point of `G(𝔸)` by `P_R(F)` into a Siegel region `Ω A_0 K` of `M_R`. On a
fibre of `H_{P_R}` the characters of `P_R` are fixed at the torus point, and therefore so are the
real forms on `𝔞_0` annihilated by the coroots of `R`. The bound of
`CuspidalExponentRegionBoundStatement` on such regions then bounds `f` on the fibre. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField Set TensorProduct Opposite
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints PositiveRealTorus AdelicSiegelFactors
  RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "A" => AdelicGroupPoints F G
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "aG" => positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T)
local notation "B₀" => (Subtype.mk ∅ (empty_subset (simpleRelativeRoots 𝓕.i 𝓕.ν)) : Idx)

section Cover

/-- **Relative Siegel covering in the family.** For a compact subgroup `K` with
`P_0(𝔸) K = G(𝔸)` and a standard index `R` there are a compact set `Ω ⊆ P_0(𝔸)` and `t > 0`
such that every `x ∈ G(𝔸)` has a left translate by a point of `P_R(F)` of the form `p a k` with
`p ∈ Ω`, `a` a positive torus point with `|α(a)| ≥ t` for the simple roots `α` of `R`, and
`k ∈ K`. Every point of `Ω` is the image of a point of `P_R(𝔸)` with zero logarithm. -/
theorem exists_relativeSiegelCover {K : Subgroup A} (hK : IsIwasawaCompact (𝓕.p B₀) K)
    (R : Idx) :
    ∃ (Ω : Set A) (t : ℝ≥0ˣ), IsCompact Ω ∧
      Ω ⊆ ((map F (𝓕.P B₀) G (𝓕.p B₀)).toMonoidHom.range : Set A) ∧
      (∀ p ∈ Ω, ∃ y : AdelicGroupPoints F (𝓕.P R), map F (𝓕.P R) G (𝓕.p R) y = p ∧
        characterLog F (𝓕.P R) y = 0) ∧
      ∀ x : A, ∃ q : RationalGroupPoints F (𝓕.P R), ∃ p ∈ Ω, ∃ a : intrinsicSubgroup F 𝓕.T,
        (∀ α ∈ R.1, t ≤ normCharacter F 𝓕.T α a) ∧ ∃ k ∈ K,
          p * aG a * k = map F (𝓕.P R) G (𝓕.p R) (rational F (𝓕.P R) q) * x := by
  classical
  let := 𝓕.maximalSplit.isSplitSubtorus.mono
  have hG := 𝓕.connectedReductive
  have hi := 𝓕.maximalSplit
  have hν := 𝓕.generic
  have hKs : IsIwasawaCompact (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) K :=
    hK.of_range_eq ((𝓕.isCompatible B₀).parabolic_eq.trans
      (Standard.isRepresentedBy_parabolicHom 𝓕.i 𝓕.ν ∅).2.symm)
  obtain ⟨T₀, j, hS⟩ := exists_siegelAlgebraicSetup_of_generic F 𝓕.i 𝓕.ν hG hi hν
  have hU₀ : IsUnipotent (Standard.unipotentScheme 𝓕.i 𝓕.ν ∅) := hS.2.2.2.2.1.1.isUnipotent
  obtain ⟨ΩN, hΩN, hcovN⟩ := exists_unipotentCompactCover_of_setup hS
  obtain ⟨ΩM, hΩM, hcovM⟩ := exists_leviCompactCover_of_setup centralSplitCompactQuotient hS
  have hRf : R.1.Finite :=
    (𝓕.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots 𝓕.i 𝓕.ν).subset R.2
  let S₁ : Finset (characterLattice 𝓕.T) := hRf.toFinset
  have hS₁ : (S₁ : Set (characterLattice 𝓕.T)) = R.1 := hRf.coe_toFinset
  obtain ⟨t, ht⟩ := exists_relativeChamberReduction F G 𝓕.T 𝓕.i 𝓕.ν T₀ j hG hS hKs S₁
    (hS₁ ▸ R.2)
  set ιN := map F (Standard.unipotentScheme 𝓕.i 𝓕.ν ∅) G (Standard.unipotentHom 𝓕.i 𝓕.ν ∅)
    with hιN
  set ιM := map F (Standard.leviScheme 𝓕.i 𝓕.ν ∅) G (Standard.leviHom 𝓕.i 𝓕.ν ∅) with hιM
  -- the factorizations through `P_0` and `P_R`
  have hP0 : standardParabolic 𝓕.i 𝓕.ν ∅ = SubgroupFunctor.range (𝓕.p B₀) :=
    (𝓕.isCompatible B₀).parabolic_eq.symm
  have hB₀R : SubgroupFunctor.range (𝓕.p B₀) ≤ SubgroupFunctor.range (𝓕.p R) :=
    (𝓕.le_iff_range_le B₀ R).mp (empty_subset _)
  have hleU (Q : Idx) (hQ : SubgroupFunctor.range (𝓕.p B₀) ≤ SubgroupFunctor.range (𝓕.p Q)) :
      SubgroupFunctor.range (Standard.unipotentHom 𝓕.i 𝓕.ν ∅) ≤ SubgroupFunctor.range (𝓕.p Q) := by
    rw [(Standard.isRepresentedBy_unipotentHom 𝓕.i 𝓕.ν ∅).2]
    exact ((standardUnipotent_le_standardParabolic 𝓕.i 𝓕.ν ∅).trans hP0.le).trans hQ
  have hleM (Q : Idx) (hQ : SubgroupFunctor.range (𝓕.p B₀) ≤ SubgroupFunctor.range (𝓕.p Q)) :
      SubgroupFunctor.range (Standard.leviHom 𝓕.i 𝓕.ν ∅) ≤ SubgroupFunctor.range (𝓕.p Q) := by
    rw [(Standard.isRepresentedBy_leviHom 𝓕.i 𝓕.ν ∅).2]
    exact ((standardLevi_le_standardParabolic 𝓕.i 𝓕.ν ∅).trans hP0.le).trans hQ
  have hfac (Q : Idx) (hQ : SubgroupFunctor.range (𝓕.p B₀) ≤ SubgroupFunctor.range (𝓕.p Q))
      (n : AdelicGroupPoints F (Standard.unipotentScheme 𝓕.i 𝓕.ν ∅))
      (m : normOneSubgroup F (Standard.leviScheme 𝓕.i 𝓕.ν ∅)) :
      ∃ y : AdelicGroupPoints F (𝓕.P Q), map F (𝓕.P Q) G (𝓕.p Q) y = ιN n * ιM m ∧
        characterLog F (𝓕.P Q) y = 0 := by
    let := (𝓕.isCompatible Q).parabolic.isClosedSubgroup.mono
    let jU := SubgroupFunctor.rangeFactor (Standard.unipotentHom 𝓕.i 𝓕.ν ∅) (𝓕.p Q) (hleU Q hQ)
    let jM := SubgroupFunctor.rangeFactor (Standard.leviHom 𝓕.i 𝓕.ν ∅) (𝓕.p Q) (hleM Q hQ)
    refine ⟨map F _ (𝓕.P Q) jU n * map F _ (𝓕.P Q) jM m, ?_, ?_⟩
    · rw [map_mul, ← map_comp_apply_of_hom, ← map_comp_apply_of_hom,
        SubgroupFunctor.rangeFactor_comp, SubgroupFunctor.rangeFactor_comp]
    · rw [characterLog_mul, characterLog_map, characterLog_map,
        characterLog_eq_zero_of_isUnipotent hU₀, (characterLog_eq_zero_iff F _ _).mpr m.2,
        map_zero, map_zero, add_zero]
  let φ : AdelicGroupPoints F (Standard.unipotentScheme 𝓕.i 𝓕.ν ∅) ×
      normOneSubgroup F (Standard.leviScheme 𝓕.i 𝓕.ν ∅) → A := fun z => ιN z.1 * ιM z.2
  have hφ : Continuous φ :=
    ((map F _ G _).continuous.comp continuous_fst).mul
      ((map F _ G _).continuous.comp (continuous_subtype_val.comp continuous_snd))
  refine ⟨φ '' (ΩN ×ˢ ΩM), t, (hΩN.prod hΩM).image hφ, ?_, ?_, fun x => ?_⟩
  · rintro _ ⟨⟨n, m⟩, -, rfl⟩
    obtain ⟨y, hy, -⟩ := hfac B₀ le_rfl n m
    exact ⟨y, hy⟩
  · rintro _ ⟨⟨n, m⟩, -, rfl⟩
    exact hfac R hB₀R n m
  obtain ⟨q, hq, n, m, a, ha, k, hk, heq⟩ := ht x
  -- the compact sets meeting the cosets of `M_0(F)` in `M_0(𝔸)^1` and of `N_0(F)` in `N_0(𝔸)`
  obtain ⟨mu, hmu⟩ := hcovM m
  set muG : RationalGroupPoints F G :=
    (Standard.leviScheme 𝓕.i 𝓕.ν ∅).affinePointsTarget (Standard.leviHom 𝓕.i 𝓕.ν ∅)
      (CommAlgCat.of F F) mu with hmuGdef
  have hmuG : ιM (rational F _ mu) = rational F G muG :=
    (DFunLike.congr_fun (rational_naturality F (Standard.leviScheme 𝓕.i 𝓕.ν ∅)
      (Standard.leviHom 𝓕.i 𝓕.ν ∅)) mu).symm
  have hconj : rational F G muG * ιN n * (rational F G muG)⁻¹ ∈
      standardUnipotentImage F G 𝓕.T 𝓕.i 𝓕.ν := by
    have hp : rational F G muG ∈ standardParabolicImage F G 𝓕.T 𝓕.i 𝓕.ν :=
      standardLeviImage_le_parabolic F G 𝓕.T 𝓕.i 𝓕.ν ⟨rational F _ mu, hmuG⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (standardParabolicImage_le_normalizer F G 𝓕.T 𝓕.i 𝓕.ν hp) (ιN n)).mp ⟨n, rfl⟩
  obtain ⟨n₂, hn₂⟩ := hconj
  obtain ⟨_, ⟨ρN, rfl⟩, hρN⟩ := hcovN n₂
  set ρG : RationalGroupPoints F G :=
    (Standard.unipotentScheme 𝓕.i 𝓕.ν ∅).affinePointsTarget (Standard.unipotentHom 𝓕.i 𝓕.ν ∅)
      (CommAlgCat.of F F) ρN with hρGdef
  have hρG : ιN (rational F _ ρN) = rational F G ρG :=
    (DFunLike.congr_fun (rational_naturality F (Standard.unipotentScheme 𝓕.i 𝓕.ν ∅)
      (Standard.unipotentHom 𝓕.i 𝓕.ν ∅)) ρN).symm
  -- the rational translate lies in `P_R(F)`
  have hR' : SubgroupFunctor.range (Standard.parabolicHom 𝓕.i 𝓕.ν (S₁ : Set (characterLattice 𝓕.T))) =
      SubgroupFunctor.range (𝓕.p R) := by
    rw [(Standard.isRepresentedBy_parabolicHom 𝓕.i 𝓕.ν _).2, hS₁, (𝓕.isCompatible R).parabolic_eq]
  rw [hR'] at hq
  have hmuP : muG ∈ (SubgroupFunctor.range (𝓕.p R)).carrier
      ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))) := hleM R hB₀R _ ⟨mu, rfl⟩
  have hρP : ρG ∈ (SubgroupFunctor.range (𝓕.p R)).carrier
      ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))) := hleU R hB₀R _ ⟨ρN, rfl⟩
  have hγ : ρG * muG * q ∈ (SubgroupFunctor.range (𝓕.p R)).carrier
      ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hρP hmuP) hq
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hγ
  have hyrat : map F (𝓕.P R) G (𝓕.p R) (rational F (𝓕.P R) y) = rational F G (ρG * muG * q) := by
    have h := DFunLike.congr_fun (rational_naturality F _ (𝓕.p R)) y
    change map F _ G (𝓕.p R) (rational F _ y) = rational F G (ρG * muG * q)
    rw [← hy]
    exact h.symm
  have haG : aG a = map F 𝓕.T.toGrp G 𝓕.i (a : AdelicGroupPoints F 𝓕.T.toGrp) := by
    change map F 𝓕.T.toGrp G (CommGroupScheme.groupHom (𝟙 𝓕.T) ≫ 𝓕.i) _ = _
    rw [show CommGroupScheme.groupHom (𝟙 𝓕.T) = 𝟙 𝓕.T.toGrp from rfl, Category.id_comp]
    rfl
  refine ⟨y, φ (rational F _ ρN * n₂, rationalNormOne F _ mu * m), ⟨_, ⟨hρN, hmu⟩, rfl⟩, a,
    fun α hα => ha α (hRf.mem_toFinset.mpr hα), k, hk, ?_⟩
  rw [hyrat, haG]
  change ιN (rational F _ ρN * n₂) *
      ιM ((rationalNormOne F _ mu * m : normOneSubgroup F _) : AdelicGroupPoints F _) *
      map F 𝓕.T.toGrp G 𝓕.i (a : AdelicGroupPoints F 𝓕.T.toGrp) * k =
    rational F G (ρG * muG * q) * x
  have hn₃ : ιN n₂ = rational F G muG * ιN n * (rational F G muG)⁻¹ := hn₂
  rw [Subgroup.coe_mul, rationalNormOne_val, map_mul, map_mul, hρG, hmuG, hn₃, map_mul,
    map_mul, mul_assoc (rational F G ρG * rational F G muG), ← heq]
  group

end Cover

section Forms

omit [NumberField F] in
/-- The real span of the simple roots of `R` and the annihilator of the coroots of `R` together
span `𝔞_0^*` (they are complementary, published `StandardLevi.complements`). -/
theorem span_roots_sup_corootAnnihilator (R : Idx) :
    Submodule.span ℝ ((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' R.1) ⊔
      corootAnnihilator 𝓕.i 𝓕.coroots R.1 = ⊤ := by
  let := 𝓕.maximalSplit.isSplitSubtorus.mono
  obtain ⟨B, hB⟩ := ArthurRelative.exists_isWeylInvariantInnerProduct 𝓕.connectedReductive
    𝓕.maximalSplit
  have hR : R.1 ⊆ relativeRoots 𝓕.i := fun α hα => (R.2 hα).1.1
  exact (StandardLevi.complements 𝓕.i 𝓕.coroots 𝓕.maximalSplit.isSplitSubtorus.1 B hB R.1
    hR).1.symm.sup_eq_top

omit [NumberField F] in
/-- Every real form on `𝔞_0` annihilated by the coroots of `R` is the restriction to the torus
of a real character parameter of `P_R` (published `standardLeviCharacterAnnihilator` and the
bijectivity of restriction of characters to a rational Levi subgroup). -/
theorem exists_parabolicParameter_of_mem_corootAnnihilator (R : Idx) {φ : Vstar 𝓕.T}
    (hφ : φ ∈ corootAnnihilator 𝓕.i 𝓕.coroots R.1) :
    ∃ m : ℝ ⊗[ℤ] GroupScheme.rationalCharacters (𝓕.P R),
      rationalCharacterRestrictReal (𝓕.torus R ≫ 𝓕.l R) m = φ := by
  have hp := (𝓕.isCompatible R).parabolic.isClosedSubgroup
  have hLevi := (𝓕.isCompatible R).levi.isClosedSubgroup.comp hp
  let : Mono (𝓕.l R ≫ 𝓕.p R).hom.hom.left := hLevi.mono
  have hrep : (standardLevi 𝓕.i 𝓕.ν R.1).IsRepresentedBy (𝓕.l R ≫ 𝓕.p R) :=
    ⟨Over.mono_of_mono_left _, (𝓕.isCompatible R).levi_eq⟩
  have hAnn := standardLeviCharacterAnnihilator F G 𝓕.connectedReductive 𝓕.T 𝓕.i
    𝓕.maximalSplit 𝓕.ν 𝓕.generic R.1 R.2 (𝓕.M R) (𝓕.l R ≫ 𝓕.p R) hLevi hrep (𝓕.torus R)
    (𝓕.torus_comp R) 𝓕.coroots
  rw [← hAnn] at hφ
  obtain ⟨m₀, rfl⟩ := hφ
  have hsurj : Function.Surjective (rationalCharacterRestrictReal (𝓕.l R)) :=
    LinearMap.baseChange_surjective ℝ
      (𝓕.isCompatible R).levi.characterRestrict_bijective.surjective
  obtain ⟨m, rfl⟩ := hsurj m₀
  exact ⟨m, (rationalCharacterRestrictReal_comp_apply _ _ m).symm⟩

omit [NumberField F] in
/-- Pairing a real character of the torus with the functional of a real cocharacter. -/
theorem realParameterPairing_cocharacterFunctional (v : Vstar 𝓕.T) (H : V 𝓕.T) :
    realParameterPairing F 𝓕.T.toGrp v (cocharacterFunctional H) = pair 𝓕.T v H := by
  induction v using TensorProduct.inductionOn with
  | tmul s χ =>
    rw [realParameterPairing_tmul, cocharacterFunctional_apply,
      show s ⊗ₜ[ℤ] χ = s • ((1 : ℝ) ⊗ₜ[ℤ] χ) by rw [TensorProduct.smul_tmul', smul_eq_mul,
        mul_one], map_smul, LinearMap.smul_apply, smul_eq_mul]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The Iwasawa height `H_{P_R}` of `p a k`, for `p` the image of a point of `P_R(𝔸)` with zero
logarithm, a positive torus point `a` with logarithm `H` and `k ∈ K`, paired with a real
character parameter `m` of `P_R`, is the restriction of `m` to the torus evaluated at `H`. -/
theorem realParameterPairing_height_mul (R : Idx) {K : Subgroup A}
    (hKR : IsIwasawaCompact (𝓕.p R) K) {p : A} {y : AdelicGroupPoints F (𝓕.P R)}
    (hy : map F (𝓕.P R) G (𝓕.p R) y = p) (hy0 : characterLog F (𝓕.P R) y = 0)
    (a : intrinsicSubgroup F 𝓕.T) (H : V 𝓕.T)
    (hH : cocharacterFunctional H = characterLog F 𝓕.T.toGrp a.val) {k : A} (hk : k ∈ K)
    (m : ℝ ⊗[ℤ] GroupScheme.rationalCharacters (𝓕.P R)) :
    realParameterPairing F (𝓕.P R) m (hKR.height (p * aG a * k)) =
      pair 𝓕.T (rationalCharacterRestrictReal (𝓕.torus R ≫ 𝓕.l R) m) H := by
  let : IsClosedImmersion (𝓕.p R).hom.hom.left := (𝓕.isCompatible R).parabolic.isClosedSubgroup
  have haG : aG a = map F (𝓕.P R) G (𝓕.p R)
      (map F 𝓕.T.toGrp (𝓕.P R) (𝓕.torus R ≫ 𝓕.l R) a.val) := by
    rw [← map_comp_apply_of_hom, Category.assoc, 𝓕.torus_comp]
    change map F 𝓕.T.toGrp G (CommGroupScheme.groupHom (𝟙 𝓕.T) ≫ 𝓕.i) _ = _
    rw [show CommGroupScheme.groupHom (𝟙 𝓕.T) = 𝟙 𝓕.T.toGrp from rfl, Category.id_comp]
    rfl
  rw [hKR.height_mul_right _ hk, ← hy, hKR.height_map_mul, hy0, zero_add, haG,
    hKR.height_map, characterLog_map, ← hH,
    Langlands.Global.ArthurTruncation.realParameterPairing_realCharacterDualMap,
    realParameterPairing_cocharacterFunctional]

end Forms

section Fibre

variable {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))

local notation "G∞" => InfiniteAdelicGroupPoints F G

open scoped Pointwise in
/-- **Boundedness on the fibres of `H_{P_R}`.** Under the hypotheses of
`CuspidalExponentRegionBoundStatement`, for a compact subgroup `K` with `P_0(𝔸) K = G(𝔸)` the
function `f` is bounded on every fibre of the Iwasawa height `H_{P_R} : G(𝔸) → 𝔞_{P_R}`. -/
def CuspidalExponentFibreBoundStatement : Prop :=
  0 < N → IsClosedSubgroup rho →
  ∀ (K : Subgroup A), IsIwasawaCompact (𝓕.p B₀) K →
  ∀ (Kinf : Subgroup G∞), Langlands.CompactIwasawa.IsMaximalCompact Kinf →
  ∀ (R : Idx) (hKR : IsIwasawaCompact (𝓕.p R) K) (f : A → ℂ),
    𝓕.IsAutomorphicOn hG Kinf rho R f →
  ∀ (s : ∀ Q : Idx, Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (c : ∀ Q : Idx, ComplexCharacterParameter F (𝓕.P Q) → A → ℂ),
    (∀ α ∈ R.1, 𝓕.IsExponentDecomposition hG Kinf rho (𝓕.removeSimpleRoot R α)
      (𝓕.constantTerm (𝓕.removeSimpleRoot R α) f) (s (𝓕.removeSimpleRoot R α))
      (c (𝓕.removeSimpleRoot R α))) →
    (∀ α ∈ R.1, ∀ mu ∈ s (𝓕.removeSimpleRoot R α), c (𝓕.removeSimpleRoot R α) mu ≠ 0 →
      ∃ β : relativeRoots 𝓕.i, β.1 ∉ (𝓕.removeSimpleRoot R α).1 ∧
        insert β.1 (𝓕.removeSimpleRoot R α).1 = R.1 ∧
        pair 𝓕.T (𝓕.realExponent (𝓕.removeSimpleRoot R α) mu)
          ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β) < 0) →
  ∀ x₀ : A, ∃ C : ℝ, ∀ x : A, hKR.height x = hKR.height x₀ → ‖f x‖ ≤ C

open scoped Pointwise in
theorem cuspidalExponentFibreBound : 𝓕.CuspidalExponentFibreBoundStatement hG rho := by
  intro hN hrho K hK Kinf hKinf R hKR f hf s c hdec hexp x₀
  let : IsClosedImmersion (𝓕.p R).hom.hom.left := (𝓕.isCompatible R).parabolic.isClosedSubgroup
  have hT : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.1.1
  let := hT.finite_realCharacterSpace
  obtain ⟨Ω, t, hΩ, hΩP, hΩlog, hcov⟩ := 𝓕.exists_relativeSiegelCover hK R
  -- a finite basis of the annihilator of the coroots of `R`
  let Wc := corootAnnihilator 𝓕.i 𝓕.coroots R.1
  let : Module.Free ℝ Wc := Module.Free.of_divisionRing ℝ Wc
  let : Module.Finite ℝ Wc := FiniteDimensional.finiteDimensional_submodule Wc
  let bW := Module.finBasis ℝ Wc
  let Φ : Set (Vstar 𝓕.T) := Set.range fun j => (bW j : Vstar 𝓕.T)
  have hΦR : Φ ⊆ Wc := by
    rintro _ ⟨j, rfl⟩
    exact (bW j).2
  have hspanΦ : Submodule.span ℝ Φ = Wc := by
    have h := congrArg (Submodule.map Wc.subtype) bW.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  have hspan : Submodule.span ℝ (((fun χ₀ : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] χ₀) '' R.1) ∪
      Φ) = ⊤ := by
    rw [Submodule.span_union, hspanΦ]
    exact 𝓕.span_roots_sup_corootAnnihilator R
  have hm (j : Fin (Module.finrank ℝ Wc)) :=
    𝓕.exists_parabolicParameter_of_mem_corootAnnihilator R (bW j).2
  choose mj hmj using hm
  let B := ∑ j, |realParameterPairing F (𝓕.P R) (mj j) (hKR.height x₀)|
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => abs_nonneg _
  -- the compact set of finite parts
  let Yf := finite F G '' Ω * finite F G '' (K : Set A)
  have hYf : IsCompact Yf :=
    (hΩ.image (finite F G).continuous).mul (hK.isCompact.image (finite F G).continuous)
  obtain ⟨C, -, hbd⟩ := 𝓕.cuspidalExponentRegionBound hG rho hN hrho Kinf hKinf R f hf s c hdec
    hexp Φ hspan hΦR t B hB Ω K hΩ hK.isCompact hΩP Yf hYf
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨q, p, hp, a, ha, k, hk, heq⟩ := hcov x
  obtain ⟨H, hH⟩ := exists_cocharacterFunctional_eq hT (characterLog F 𝓕.T.toGrp a.val)
  obtain ⟨y, hy, hy0⟩ := hΩlog p hp
  have hqΓ : map F (𝓕.P R) G (𝓕.p R) (rational F (𝓕.P R) q) ∈
      parabolicQuotientSubgroup F (𝓕.p R) (𝓕.iU R) (𝓕.l R) :=
    𝓕.rationalImage_le_parabolicQuotientSubgroup_of_le le_rfl ⟨q, rfl⟩
  have hfx : f x = f (p * aG a * k) := by
    rw [heq]
    exact (hf.1 _ hqΓ x).symm
  have hheight : hKR.height (p * aG a * k) = hKR.height x₀ := by
    rw [heq, hKR.height_rational_mul, hx]
  have hΦ : ∀ φ ∈ Φ, |pair 𝓕.T φ H| ≤ B := by
    rintro _ ⟨j, rfl⟩
    have h := 𝓕.realParameterPairing_height_mul R hKR hy hy0 a H hH hk (mj j)
    rw [hheight, hmj j] at h
    rw [← h]
    exact Finset.single_le_sum (f := fun j => |realParameterPairing F (𝓕.P R) (mj j)
      (hKR.height x₀)|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have hfin : finite F G (p * aG a * k) ∈ Yf := by
    have h1 : finite F G (p * aG a * k) = finite F G p * finite F G k := by
      simp only [map_mul, finite_positiveMap F G 𝓕.T 𝓕.i 𝓕.T (𝟙 𝓕.T) hT, mul_one]
    rw [h1]
    exact Set.mul_mem_mul ⟨p, hp, rfl⟩ ⟨k, hk, rfl⟩
  rw [hfx]
  exact hbd p hp a H hH ha hΦ k hk hfin

end Fibre

end Langlands.Global.StandardParabolicFamily
