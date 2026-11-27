import Langlands.Global.ArthurAlternatingConstantTerm
import Langlands.Global.AdelicHarishChandraDirectionalGrowth
import Langlands.Automorphic.GroupSchemeSliceAdelicGrowthReduction

/-! # Uniform directional growth of Arthur's alternating constant terms -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints RepresentationGrowth Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  {d N : ℕ} (hSmooth : SmoothOfRelativeDimension d G.X.hom) (ρ : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "Δ" => simpleFinset ν hG hi
local notation "J" => Finset (characterLattice T)
local notation "H" => adelicHeight F G ρ
local notation "diffCalc" => adelicDifferentialCommutator_of_smooth F G hSmooth

include hν in
/-- The finite signed sum preserves the finite right level, smoothness on
archimedean slices, and a common growth exponent for derivative words. -/
theorem alternatingConstantTerm_uniformGrowth (hN : 0 < N) (R S : J) (hS : S ⊆ Δ)
    (f : FinitePlotSmoothRationalFunctions F G)
    (hf : HasAdelicUniformModerateGrowth F G ρ hSmooth diffCalc f) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hSmooth
    let g := alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f.val)
    ∃ (L : Subgroup Gf) (r : ℝ), IsOpen (L : Set Gf) ∧ 0 ≤ r ∧ Continuous g ∧
      (∀ b : Gf, ContMDiff IG IC ∞ (fun a : G∞ => g (pair F G a b))) ∧
      (∀ l ∈ L, ∀ x, g (x * ofFinite F G l) = g x) ∧
      ∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖adelicIteratedDirectionalValue hSmooth s g x‖ ≤ C * H x ^ r := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hSmooth
  intro g
  have hfCont : Continuous (evaluate F G f.val) := f.val.property
  obtain ⟨hfS, hfL⟩ := (mem_finitePlotSmoothRationalSubrepresentation_iff_contMDiff F G hSmooth f.val).mp f.prop
  obtain ⟨L, hL⟩ := hfL
  have hfLevel (l : Gf) (hl : l ∈ L.toSubgroup) (x : A) :
      evaluate F G f.val (x * ofFinite F G l) = evaluate F G f.val x :=
    congrArg (fun φ : ContinuousRationalFunctions F G => evaluate F G φ x) (hL ⟨l, hl⟩)
  obtain ⟨e, he⟩ := (hasAdelicUniformModerateGrowth_iff F G ρ hSmooth diffCalc hN f).mp hf
  let r : ℝ := e
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hGrow (s : List W) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖adelicIteratedDirectionalValue hSmooth s (evaluate F G f.val) x‖ ≤ C * H x ^ r := by
    obtain ⟨C, hC, hbound⟩ := he (adelicDirectionalWordEnveloping hSmooth s)
    refine ⟨C, hC, fun x => ?_⟩
    rw [← evaluate_adelicDirectionalWordEnveloping hSmooth diffCalc]
    simpa only [r, Real.rpow_natCast] using hbound x
  let s := S.powerset.filter (R ⊆ ·)
  let c (Q : s) := (-1 : ℂ) ^ ((Δ).card - Q.val.card)
  let gQ (Q : s) := constantTerm F i ν (Q.val : Set (characterLattice T)) (evaluate F G f.val)
  have hsum : g = ∑ Q ∈ s.attach, c Q • gQ Q := by
    funext x
    simp only [g, alternatingConstantTerm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, c, gQ]
    exact (Finset.sum_attach s (fun P : J => (-1 : ℂ) ^ ((Δ).card - P.card) *
      constantTerm F i ν (P : Set (characterLattice T)) (evaluate F G f.val) x)).symm
  have hQ (Q : s) := by
    let P := (Q.val : Set (characterLattice T))
    let U := Standard.unipotentScheme i ν P
    let j := Standard.unipotentHom i ν P
    have hP : P ⊆ simpleRelativeRoots i ν := fun α hα =>
      (mem_simpleFinset hG hi).mp (hS (Finset.mem_powerset.mp (Finset.mem_filter.mp Q.2).1 hα))
    have hgeom := (Standard.parabolicStructure i ν hG hi hν P hP).2.2.1
    let : IsAffine U.X.left := @isAffine_of_isAffineHom _ _ U.X.hom
      (Standard.isClosedSubgroup_unipotentHom i ν P).isAffineHom_source inferInstance
    let : IsClosedImmersion j.hom.hom.left := Standard.isClosedSubgroup_unipotentHom i ν P
    have hRat (q : RationalGroupPoints F U) (x : A) :
        evaluate F G f.val (map F U G j (rational F U q) * x) = evaluate F G f.val x := by
      rw [map_rational]
      exact evaluate_rational_mul F G f.val _ x
    exact adelicConstantTermDirectionalGrowth j hSmooth ρ
      hgeom.1.smooth hgeom.1.connectedSpace hgeom.1.isUnipotent hN L.toSubgroup L.isOpen
      Unit (fun _ => evaluate F G f.val) (fun _ => 1) (fun _ => zero_le_one)
      (fun _ => hfCont) (fun _ => hfS) (fun _ => hRat) (fun _ => hfLevel) r hr
      (fun a => by
        obtain ⟨C, hC, hB⟩ := hGrow a
        exact ⟨C, hC, fun _ x => by simpa only [mul_one] using hB x⟩)
  have hSmoothQ (Q : s) (b : Gf) : ContMDiff IG IC ∞ (fun a : G∞ => gQ Q (pair F G a b)) :=
    (hQ Q).2.1 () b
  refine ⟨L.toSubgroup, r, L.isOpen, hr, ?_, ?_, ?_, ?_⟩
  · have hApp : g = fun x => ∑ Q ∈ s.attach, c Q * gQ Q x := by
      funext x
      rw [hsum]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hApp]
    exact continuous_finsetSum _ fun Q _ => continuous_const.mul ((hQ Q).1 ())
  · intro b
    rw [hsum]
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine contMDiff_finsetSum (f := fun Q (a : G∞) => c Q • gQ Q (pair F G a b)) fun Q _ => ?_
    exact (((ContinuousLinearMap.mul ℝ ℂ) (c Q)).contDiff.contMDiff).comp (hSmoothQ Q b)
  · intro l hl x
    rw [hsum]
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_congr rfl fun Q _ => congrArg (c Q • ·) ((hQ Q).2.2.1 () l hl x)
  · intro word
    have hBounds (Q : s) := (hQ Q).2.2.2.2 word
    choose C hC hB using hBounds
    refine ⟨∑ Q ∈ s.attach, ‖c Q‖ * C Q,
      Finset.sum_nonneg (fun Q _ => mul_nonneg (norm_nonneg _) (hC Q)), fun x => ?_⟩
    rw [hsum, adelicIteratedDirectionalValue_finsetSum hSmooth word s.attach c gQ hSmoothQ]
    simp only [Finset.sum_apply, Pi.smul_apply]
    calc
      _ ≤ ∑ Q ∈ s.attach, ‖c Q • adelicIteratedDirectionalValue hSmooth word (gQ Q) x‖ := norm_sum_le _ _
      _ ≤ ∑ Q ∈ s.attach, (‖c Q‖ * C Q) * H x ^ r := by
        refine Finset.sum_le_sum fun Q _ => ?_
        rw [norm_smul, mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [mul_one] using hB Q () x
      _ = _ := by rw [Finset.sum_mul]

end Langlands.Global.ArthurTruncation
