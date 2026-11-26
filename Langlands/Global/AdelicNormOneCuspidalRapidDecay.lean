import Langlands.Global.AdelicNormOneCuspidalSeparationStatement
import Langlands.Global.AdelicRelativeCuspidalRapidDecay
import Langlands.Global.AdelicFiniteTranslateHeightReduction
import Langlands.Global.AdelicNormOneRootBox
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.Automorphic.GroupSchemeManifoldSmooth

/-! # Cuspidal rapid decay on the norm-one Siegel cover -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField Set
open scoped CategoryTheory.MonObj Classical Manifold ContDiff NNReal Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.LinearAlgebra.RationalSpan
  Langlands.Automorphic.GroupSchemeFunctions InfiniteAdelicGroupPoints PositiveRealTorus
  AdelicSiegelFactors RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {d N : ℕ}
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "H" => adelicHeight F G rho

/-- One set of rational orbit representatives in the norm-one group works for
all cuspidal functions with a common height exponent for their derivatives. -/
def AdelicNormOneCuspidalRapidDecayStatement : Prop :=
  IsConnectedReductive G → 0 < N → ∃ S : Set A,
    S ⊆ normOneSubgroup F G ∧
    (∀ x : normOneSubgroup F G, ∃ q : RationalGroupPoints F G, rational F G q * x.val ∈ S) ∧
    ∀ f : A → ℂ,
      IsAdelicSmoothFunction F G f → IsLeftInvariantUnder F G (rationalSubgroup F G) f →
      HasZeroProperParabolicConstantTerms f →
      ∀ R : ℝ, 0 ≤ R →
        (∀ s : List (smoothModel F d), ∃ C : ℝ, 0 ≤ C ∧
          ∀ x, ‖adelicIteratedDirectionalValue hsmooth s f x‖ ≤ C * H x ^ R) →
        ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ‖f x‖ * H x ^ m ≤ C

/-- Absolute cuspidal rapid decay follows from relative decay along the full
standard index. The norm-one constraint supplies the complementary bounds. -/
theorem adelicNormOneCuspidalRapidDecay :
    AdelicNormOneCuspidalRapidDecayStatement hsmooth rho := by
  intro hG hN
  let := hG.isAffineHom
  obtain ⟨T, i, ν, T₀, j, hS, C, t, W, hW, hcover⟩ :=
    hasFiniteRightSiegelCover_of_connectedReductive F G hG
  let fam := StandardParabolicFamily.ofMaximalSplitTorus hG i hS.1 ν hS.2.1
  let := hS.1.isSplitSubtorus.mono
  let B₀ : StandardIndex F G fam.i fam.ν := ⟨∅, empty_subset _⟩
  let D := canonicalStandardFactors F G T i ν
  let Ω := compactPrefix F G T i ν D C
  let K : Set A := (C.compactSubgroup : Set A) * W
  let Yf : Set (FiniteAdelicGroupPoints F G) := finite F G '' Ω * finite F G '' K
  let S : Set A := weakSiegelProduct F G T i ν D C T₀ j t * W ∩ normOneSubgroup F G
  refine ⟨S, inter_subset_right, ?_, ?_⟩
  · intro x
    obtain ⟨q, hq⟩ := hcover x
    exact ⟨q, hq, (normOneSubgroup F G).mul_mem (rationalNormOne F G q).2 x.2⟩
  intro f hf hRational hCusp R hR hGrowth m
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  obtain ⟨L, hL, hFixed⟩ := hf.2.2
  have hfSmooth (c : FiniteAdelicGroupPoints F G) :
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun y => f (pair F G y c)) :=
    (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hf.2.1 c)
  have hΩ : IsCompact Ω := isCompact_compactPrefix F G T i ν D C
  have hK : IsCompact K := C.compact_compactSubgroup.mul hW.isCompact
  have hYf : IsCompact Yf := (hΩ.image (finite F G).continuous).mul (hK.image (finite F G).continuous)
  have hΩB : Ω ⊆ ((map F (fam.P B₀) G (fam.p B₀)).toMonoidHom.range : Set A) := by
    rintro _ ⟨_, ⟨n, hn, rfl⟩, _, ⟨l, hl, rfl⟩, rfl⟩
    have heq := (fam.isCompatible B₀).parabolic_eq
    change SubgroupFunctor.range (fam.p B₀) = standardParabolic i ν ∅ at heq
    have hn' := (standardUnipotent_le_standardParabolic i ν ∅) _
      (unipotent_mem_standard F G T i ν D n)
    have hl' := (standardLevi_le_standardParabolic i ν ∅) _
      (levi_mem_standard F G T i ν D l.val)
    change _ ∈ (SubgroupFunctor.range (fam.p B₀)).carrier
      ((algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F))))
    rw [heq]
    exact ((standardParabolic i ν ∅).carrier _).mul_mem hn' hl'
  have hEndpoints := standardParabolicEndpoints F G hG T i hS.1 ν hS.2.1
  have hRad : SubgroupFunctor.range (fam.iU fam.top ≫ fam.p fam.top) = ⊥ :=
    (fam.range_radical_eq_standardUnipotent fam.top).trans hEndpoints.2.2.2.2
  have hfU (u : AdelicGroupPoints F (fam.U fam.top)) (x : A) :
      f (map F (fam.U fam.top) G (fam.iU fam.top ≫ fam.p fam.top) u * x) = f x := by
    have hu : map F (fam.U fam.top) G (fam.iU fam.top ≫ fam.p fam.top) u ∈
        (SubgroupFunctor.range (fam.iU fam.top ≫ fam.p fam.top)).carrier
          ((algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F)))) := ⟨u, rfl⟩
    rw [hRad] at hu
    have hEq : map F (fam.U fam.top) G (fam.iU fam.top ≫ fam.p fam.top) u = 1 := hu
    rw [hEq, one_mul]
  have hfCusp : fam.IsCuspidalAlong fam.top f := by
    intro Q hQ
    apply hCusp (fam.P Q) (fam.U Q) (fam.p Q) (fam.iU Q)
      (fam.isCompatible Q).parabolic (fam.isUnipotentRadical Q)
    intro heq
    apply not_le_of_gt hQ
    apply (fam.le_iff_range_le fam.top Q).mpr
    rw [heq]
    exact fun _ _ _ => trivial
  have hspan : ratSpan (((fun α : characterLattice T => 𝟙 T ≫ α) '' simpleRelativeRoots i ν) ∪
      Set.range (torusCharacterRestrict i)) = ⊤ := by
    simpa only [Category.id_comp, Set.image_id'] using
      simpleRelativeRoots_restrictedCharacters_ratSpan_eq_top F G T i ν hG hS.1 hS.2.1
  have hWeight : ∀ s : List (smoothModel F d), ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (_ : Unit) x, ‖adelicIteratedDirectionalValue hsmooth s f x‖ ≤ C' * H x ^ R * 1 := by
    intro s
    obtain ⟨C', hC', hs⟩ := hGrowth s
    exact ⟨C', hC', fun _ x => by simpa only [mul_one] using hs x⟩
  obtain ⟨C', hC', hDecay⟩ := fam.adelicRelativeCuspidalRapidDecay (𝟙 T) hsmooth rho
    hS.1.isSplitSubtorus.1 hN fam.top (Set.range (torusCharacterRestrict i)) hspan t 0 le_rfl
    Ω K hΩ hK hΩB Yf hYf L hL Unit (fun _ => f) (fun _ => 1) (fun _ => zero_le_one)
    (fun _ => hf.1) (fun _ => hfSmooth)
    (fun _ r hr x => hRational r (rationalImage_le_rationalSubgroup (fam.p B₀) hr) x)
    (fun _ => hfU) (fun _ => hFixed) (fun _ => hfCusp) R hR hWeight m
  refine ⟨C', hC', ?_⟩
  rintro x ⟨hx, _⟩
  obtain ⟨s, hs, w, hw, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨n, hn, l, hl, a, ha, k, hk, rfl⟩ :=
    (mem_productSet_iff F G T i ν D C T₀ j _ s).mp hs
  let a' : intrinsicSubgroup F T :=
    ⟨pointMap F T₀.toGrp T.toGrp (Adeles F) (CommGroupScheme.groupHom j) a.val,
      map_intrinsicSubgroup_le F T₀ T j ⟨a.val, a.2, rfl⟩⟩
  have ha' : a' ∈ weakSimpleRootChamber F T T (𝟙 T) G i ν t := by
    intro α hα
    change t ≤ normCharacter F T (𝟙 T ≫ α) a'.val
    rw [Category.id_comp, ← normCharacter_pullback F T₀ T j α a.val]
    exact ha α hα
  have hid : CommGroupScheme.groupHom (𝟙 T) ≫ i = i := Category.id_comp _
  have hMap : positiveMap F G T i T (𝟙 T) a' = positiveMap F G T i T₀ j a := by
    change map F T.toGrp G (CommGroupScheme.groupHom (𝟙 T) ≫ i) a'.val =
      map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ i) a.val
    rw [hid]
    exact (map_comp_apply_of_hom (p := i) (CommGroupScheme.groupHom j) a.val).symm
  have hLog (χ : characterLattice T) (hχ : χ ∈ Set.range (torusCharacterRestrict i)) :
      |logNormHom F T a'.val χ| ≤ (0 : ℝ) := by
    obtain ⟨ψ, rfl⟩ := hχ
    have haNorm : map F T.toGrp G i a'.val ∈ normOneSubgroup F G := by
      have haNorm := hS.positiveMap_mem_normOne F G T i ν T₀ j a
      rw [← hMap] at haNorm
      change map F T.toGrp G (CommGroupScheme.groupHom (𝟙 T) ≫ i) a'.val ∈
        normOneSubgroup F G at haNorm
      rwa [hid] at haNorm
    have hχNorm := normCharacter_restrict_eq_one_of_map_mem_normOne F G T i haNorm ψ
    change |Real.log ((normCharacter F T (torusCharacterRestrict i ψ) a'.val : ℝ≥0) : ℝ)| ≤ 0
    rw [hχNorm]
    simp
  let p := map F D.unipotent G D.unipotentInclusion n * map F D.levi G D.leviInclusion l.val
  have hp : p ∈ Ω := ⟨_, ⟨n, hn, rfl⟩, _, ⟨l, hl, rfl⟩, rfl⟩
  have hkw : k * w ∈ K := Set.mul_mem_mul hk hw
  have hfinite : finite F G (p * positiveMap F G T i T (𝟙 T) a' * (k * w)) ∈ Yf := by
    rw [map_mul, map_mul, finite_positiveMap F G T i T (𝟙 T) hS.1.isSplitSubtorus.1 a', mul_one]
    exact Set.mul_mem_mul (mem_image_of_mem _ hp) (mem_image_of_mem _ hkw)
  have hbound := hDecay () p hp a' ha' hLog (fun _ h => (h.2 h.1).elim) (k * w) hkw hfinite
  change ‖f (p * positiveMap F G T i T (𝟙 T) a' * (k * w))‖ *
    H (p * positiveMap F G T i T (𝟙 T) a' * (k * w)) ^ m ≤ C' * 1 at hbound
  simpa only [hMap, ← mul_assoc, mul_one, p] using hbound

end Langlands.Global.AdelicGroupPoints
