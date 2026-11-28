import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Langlands.Global.AdelicWavePacketSpectralCoordinates
import Langlands.Global.AdelicRelativeWavePacketAssociationReduction
import Langlands.Global.AdelicImaginaryIntertwiningProperties
import Langlands.Global.AdelicTruncatedEisensteinAsymptoticsStatement
import Langlands.Global.AdelicWavePacketChamberDecayReduction
import Langlands.GroupScheme.Rational.RelativeSplitCentralDirectionsProof
import Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof

/-! # The exceptional coroot hyperplanes in a wave-packet pairing -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Filter MeasureTheory Module
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  AdelicGroupPoints ArthurParabolicSpaces ArthurTruncation

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)

local notation "P[" i "," ν "," S "]" => Standard.parabolicScheme i ν S
local notation "M[" i "," ν "," S "]" => Standard.leviScheme i ν S
local notation "p[" i "," ν "," S "]" => Standard.parabolicHom i ν S
local notation "l[" i "," ν "," S "]" => Standard.leviToParabolic i ν S
local notation "Z[" n "]" => (Fin n → ℝ)
local notation "ζ[" n "]" => (volume : Measure Z[n])

section Centre

variable {n₀ : ℕ} (b : Basis (Fin n₀) ℝ (relativeCentralDirections i))
  (f : RestrictionSplitCentre.canonicalTorus F G ⟶ T)
  (hf : CommGroupScheme.groupHom f ≫ i = RestrictionSplitCentre.canonicalComponent F G)

include hG hi hf in
private theorem relativeParameterSpace_iff_centralFrequency_zero
    {S : Set (characterLattice T)} {A : CommGroupScheme (Spec (CommRingCat.of F))}
    {a : A.toGrp ⟶ M[i, ν, S]} (r : ParabolicRootPresentation p[i, ν, S] l[i, ν, S] a)
    (x : RealCharacterParameter F P[i, ν, S]) :
    x ∈ relativeParameterSpace p[i, ν, S] ↔ wavePacketCentralFrequency b (restrictToTorus F i ν S x) = 0 := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hT := hi.isSplitSubtorus.1
  have hZ := RestrictionSplitCentre.isSplitComponent_canonicalComponent F G
  have hrange := (hZ.restriction_kernels_eq_relativeRootSpans rootAnnihilatorCentrality hT f hf).2
  have hcomp : CommGroupScheme.groupHom f ≫ torusToParabolic F i ν S = splitCentreParabolicLift r := by
    apply (Standard.isRepresentedBy_parabolicHom i ν S).hom_ext
    rw [Category.assoc, torusToParabolic_comp, hf, splitCentreParabolicLift_comp]
  rw [relativeParameterSpace_eq_ker_centralRestriction r, LinearMap.mem_ker, ← hcomp]
  change rationalCharacterRestrictReal
    (CommGroupScheme.groupHom f ≫ torusToParabolic F i ν S) x = 0 ↔ _
  rw [← rationalCharacterRestrictReal_comp_apply, ← LinearMap.mem_ker, hrange]
  change restrictToTorus F i ν S x ∈ relativeRootSpanReal i ↔ _
  rw [← map_zero (wavePacketCentralFrequency b), wavePacketCentralFrequency_eq_iff hT, sub_zero]

include hG hi hν in
omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem exists_relative_coroot_value
    {S : Set (characterLattice T)} (hS : S ⊆ simpleRelativeRoots i ν)
    (π : P[i, ν, S] ⟶ M[i, ν, S]) (hπ : l[i, ν, S] ≫ π = 𝟙 M[i, ν, S])
    {α : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν) (hαS : α ∉ S) :
    ∃ x : RealCharacterParameter F P[i, ν, S],
      wavePacketCentralFrequency b (restrictToTorus F i ν S x) = 0 ∧
      realParameterPairing F P[i, ν, S] x (toCharacterDual F i ν S (corootVector D α)) = 1 := by
  let Δ := simpleRelativeRoots i ν
  have hT := hi.isSplitSubtorus.1
  let hperf := isPerfPair_of_isSplitTorus hT
  let W := ArthurRelative.weight hG hi ν D Δ α
  obtain ⟨y, hy⟩ := hperf.bijective_left.surjective W
  have hAnn : y ∈ corootAnnihilator i D S := by
    rw [mem_corootAnnihilator]
    intro β hβ
    change pair T y (D.realCoroot β) = 0
    have hne : α ≠ β.1 := fun h => hαS (h.symm ▸ hβ)
    rw [DFunLike.congr_fun hy (D.realCoroot β),
      ArthurRelative.weight_coroot hG hi D hν Set.Subset.rfl hα β (hS hβ),
      ite_eq_right hne]
  let L := Standard.leviHom i ν S
  let hL := Standard.isRepresentedBy_leviHom i ν S
  let t := standardLeviTorusFactor i ν S hL
  have ht : t ≫ L = i := standardLeviTorusFactor_comp i ν S hL
  have hrange := standardLeviCharacterAnnihilator F G hG T i hi ν hν S hS _ L
    (Standard.isClosedSubgroup_leviHom i ν S) hL t ht D
  obtain ⟨v, hv⟩ := hrange.symm ▸ hAnn
  have hlt : t ≫ l[i, ν, S] = torusToParabolic F i ν S := by
    apply (Standard.isRepresentedBy_parabolicHom i ν S).hom_ext
    rw [Category.assoc, Standard.leviToParabolic_comp, ht, torusToParabolic_comp]
  let x := rationalCharacterRestrictReal π v
  have hx : restrictToTorus F i ν S x = y := by
    change rationalCharacterRestrictReal (torusToParabolic F i ν S)
      (rationalCharacterRestrictReal π v) = y
    rw [rationalCharacterRestrictReal_comp_apply, ← hlt, Category.assoc, hπ, Category.comp_id, hv]
  refine ⟨x, ?_, ?_⟩
  · rw [hx]
    funext j
    change pair T y (b j : V T) = 0
    rw [DFunLike.congr_fun hy (b j : V T)]
    apply ArthurRelative.weight_eq_zero_of_mem_rootAnnihilator
    rw [mem_rootAnnihilator]
    exact fun β hβ => (mem_relativeCentralDirections i _).mp (b j).property β
      (simpleRelativeRoots_subset_relativeRoots i ν hβ)
  · rw [realParameterPairing_toCharacterDual, hx]
    have hαr := simpleRelativeRoots_subset_relativeRoots i ν hα
    rw [corootVector, dite_eq_left hαr, DFunLike.congr_fun hy (D.realCoroot ⟨α, hαr⟩),
      ArthurRelative.weight_coroot hG hi D hν Set.Subset.rfl hα _ hα, ite_eq_left rfl]

end Centre

/-- A projected simple-coroot denominator factor is nonzero almost everywhere in the
common central frequency and the two independent relative frequencies. -/
def WavePacketCorootFactorNonvanishingStatement : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
    {ν : cocharacterLattice T} (_hG : IsConnectedReductive G) (_hi : IsMaximalSplitTorus i)
    (_hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    {n₀ : ℕ} (b : Basis (Fin n₀) ℝ (relativeCentralDirections i))
    (f : RestrictionSplitCentre.canonicalTorus F G ⟶ T),
    CommGroupScheme.groupHom f ≫ i = RestrictionSplitCentre.canonicalComponent F G →
    ∀ {J J' S : Set (characterLattice T)}, S ⊆ simpleRelativeRoots i ν →
    ∀
    {A Aₛ : CommGroupScheme (Spec (CommRingCat.of F))}
    {a : A.toGrp ⟶ M[i, ν, J]} {aₛ : Aₛ.toGrp ⟶ M[i, ν, S]}
    (_r : ParabolicRootPresentation p[i, ν, J] l[i, ν, J] a)
    (_rₛ : ParabolicRootPresentation p[i, ν, S] l[i, ν, S] aₛ)
    (π : P[i, ν, S] ⟶ M[i, ν, S]), l[i, ν, S] ≫ π = 𝟙 M[i, ν, S] →
    ∀
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
    (c : M[i, ν, S] ⟶ M[i, ν, J]), IsWeylConjugation p[i, ν, J] l[i, ν, J] p[i, ν, S] l[i, ν, S] w c →
    ∀
    (c' : M[i, ν, S] ⟶ M[i, ν, J'])
    {n n' u v : ℕ} (e : Z[n] ≃ₗ[ℝ] RealCharacterParameter F P[i, ν, J])
    (e' : Z[n'] ≃ₗ[ℝ] RealCharacterParameter F P[i, ν, J'])
    (B : (Z[u] × Z[n₀]) ≃ₗ[ℝ] Z[n]) (B' : (Z[v] × Z[n₀]) ≃ₗ[ℝ] Z[n']),
    (∀ u z j, pair T (restrictToTorus F i ν J (e (B (u, z)))) (b j : V T) = z j) →
    ∀ (ν₁ : Measure Z[u]) (ν₂ : Measure Z[v]) [ν₁.IsAddHaarMeasure] [ν₂.IsAddHaarMeasure]
    {α : characterLattice T}, α ∈ simpleRelativeRoots i ν → α ∉ S →
    ∀ᵐ s : Z[n₀] × (Z[u] × Z[v]) ∂(ζ[n₀].prod (ν₁.prod ν₂)),
      complexParameterPairing F P[i, ν, S]
        (weylParameter l[i, ν, J] c π (imaginaryParameter F _ (e (B (s.2.1, s.1)))) +
          weylParameter l[i, ν, J'] c' π (parameterConj F _ (imaginaryParameter F _ (e' (B' (s.2.2, s.1))))))
        (toCharacterDual F i ν S (corootVector D α)) ≠ 0

/-- A Levi character with a prescribed coroot value gives a point off the kernel. -/
theorem ae_wavePacketCorootFactor_ne_zero : WavePacketCorootFactorNonvanishingStatement := by
  intro F _ _ G _ _ _ T i _ ν hG hi hν D n₀ b f hf J J' S hS A Aₛ a aₛ r rₛ π hπ
    w c hc c' n n' u v e e' B B' hB ν₁ ν₂ _ _ α hα hαS
  let X := Z[n₀] × (Z[u] × Z[v])
  let H := toCharacterDual F i ν S (corootVector D α)
  let p₁ : X →ₗ[ℝ] Z[u] × Z[n₀] :=
    ((LinearMap.fst ℝ Z[u] Z[v]).comp (LinearMap.snd ℝ Z[n₀] (Z[u] × Z[v]))).prod
      (LinearMap.fst ℝ Z[n₀] (Z[u] × Z[v]))
  let p₂ : X →ₗ[ℝ] Z[v] × Z[n₀] :=
    ((LinearMap.snd ℝ Z[u] Z[v]).comp (LinearMap.snd ℝ Z[n₀] (Z[u] × Z[v]))).prod
      (LinearMap.fst ℝ Z[n₀] (Z[u] × Z[v]))
  let L := ((realParameterPairing F P[i, ν, S]).flip H).comp
    ((realWeylParameter l[i, ν, J] c π ∘ₗ e.toLinearMap ∘ₗ B.toLinearMap ∘ₗ p₁) -
      (realWeylParameter l[i, ν, J'] c' π ∘ₗ e'.toLinearMap ∘ₗ B'.toLinearMap ∘ₗ p₂))
  obtain ⟨y, hy, hyH⟩ := exists_relative_coroot_value hG hi hν D b hS π hπ hα hαS
  have hyRel := (relativeParameterSpace_iff_centralFrequency_zero hG hi b f hf rₛ y).mpr hy
  obtain ⟨W, hW⟩ := exists_relativeWeylParameter_linearEquiv r rₛ hπ hc
  obtain ⟨x, hx⟩ := W.surjective ⟨y, hyRel⟩
  have hWy : realWeylParameter l[i, ν, J] c π (x : RealCharacterParameter F P[i, ν, J]) = y :=
    (hW x).symm.trans (congrArg Subtype.val hx)
  have hx0 := (relativeParameterSpace_iff_centralFrequency_zero hG hi b f hf r
    (x : RealCharacterParameter F P[i, ν, J])).mp x.property
  obtain ⟨⟨a₀, z₀⟩, he⟩ := (B.trans e).surjective x.val
  change e (B (a₀, z₀)) = x.val at he
  have hz₀ : z₀ = 0 := by
    funext j
    have hj := hB a₀ z₀ j
    change wavePacketCentralFrequency b (restrictToTorus F i ν J (e (B (a₀, z₀)))) j = z₀ j at hj
    rw [he, hx0] at hj
    exact hj.symm
  subst z₀
  have hL : L (0, a₀, 0) = 1 := by
    change realParameterPairing F P[i, ν, S]
      (realWeylParameter l[i, ν, J] c π (e (B (a₀, 0))) -
        realWeylParameter l[i, ν, J'] c' π (e' (B' (0, 0)))) H = 1
    rw [he, hWy, show (0, 0) = (0 : Z[v] × Z[n₀]) from rfl,
      map_zero, map_zero, map_zero, sub_zero]
    exact hyH
  have hker : L.ker ≠ ⊤ := by
    intro h
    have hm : (0, a₀, 0) ∈ L.ker := h ▸ Submodule.mem_top
    simp only [LinearMap.mem_ker, hL, one_ne_zero] at hm
  have hae : ∀ᵐ s ∂(ζ[n₀].prod (ν₁.prod ν₂)), L s ≠ 0 := by
    let : (ν₁.prod ν₂).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    let : (ζ[n₀].prod (ν₁.prod ν₂)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    rw [ae_iff]
    simp only [not_ne_iff]
    exact Measure.addHaar_submodule (ζ[n₀].prod (ν₁.prod ν₂)) L.ker hker
  filter_upwards [hae] with s hs
  rw [parameterConj_imaginaryParameter, map_neg, weylParameter_imaginaryParameter,
    weylParameter_imaginaryParameter, ← sub_eq_add_neg, ← map_sub,
    ChamberDecay.complexParameterPairing_imaginaryParameter]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hs) Complex.I_ne_zero

end Langlands.Global
