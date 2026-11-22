import Langlands.Global.AdelicHarishChandraDecomposition
import Langlands.Global.AdelicConstantTermDirectionalGrowth
import Langlands.Global.AdelicUniformDirectionalGrowth
import Langlands.Global.AdelicConstantTermEvaluation

/-! # Uniform directional growth of Harish-Chandra components -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints Langlands.Geometry.Manifold
  RepresentationGrowth AdelicSubgroupPoints HarishChandraDecomposition

section DirectionalSum

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)

/-- A real right-orbit derivative word acts linearly on finite sums of functions
that are smooth on each archimedean slice. -/
private theorem adelicIteratedDirectionalValue_finsetSum
    {J : Type w} (s : List W) (t : Finset J) (c : J → ℂ) (f : J → A → ℂ) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    (∀ i (b : Gf), ContMDiff IG IC ∞ (fun y : G∞ => f i (pair F G y b))) →
    adelicIteratedDirectionalValue hG s (∑ i ∈ t, c i • f i) =
      ∑ i ∈ t, c i • adelicIteratedDirectionalValue hG s (f i) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  intro hf
  let B := manifoldSmoothFunctions F G hG
  let d₀ (X : W) : Module.End ℂ B :=
    { toFun := fun h => ⟨groupDirectionalValue IG X h.val, contMDiff_groupDirectionalValue IG X h.prop⟩
      map_add' := fun h k => Subtype.ext (funext fun x => groupDirectionalValue_add IG X h.prop k.prop x)
      map_smul' := fun c h => Subtype.ext (funext fun x => groupDirectionalValue_const_smul IG X c h.prop x) }
  let D (s : List W) : Module.End ℂ B := s.foldr (fun X g => (d₀ X).comp g) LinearMap.id
  funext x
  rw [← pair_projections F G x]
  let b := finite F G x
  let a := infinite F G x
  have hslice (s : List W) (f : A → ℂ) (h : B) (heq : h.val = fun y => f (pair F G y b)) :
      (D s h).val = fun y => adelicIteratedDirectionalValue hG s f (pair F G y b) := by
    induction s with
    | nil => exact heq
    | cons X s ih =>
      funext y
      change groupDirectionalValue IG X (D s h).val y = _
      rw [adelicIteratedDirectionalValue_cons, adelicDirectionalValue_pair, ih]
  let fs (i : J) : B := ⟨fun y => f i (pair F G y b), hf i b⟩
  let h : B := ∑ i ∈ t, c i • fs i
  have hh : h.val = fun y => (∑ i ∈ t, c i • f i) (pair F G y b) := by
    funext y
    simp only [h, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    rfl
  change adelicIteratedDirectionalValue hG s (∑ i ∈ t, c i • f i) (pair F G a b) = _
  rw [← show (D s h).val a = _ from congrFun (hslice s _ _ hh) a]
  simp only [h, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => congrArg (c i • ·) ?_
  exact congrFun (hslice s (f i) (fs i) rfl) a

end DirectionalSum

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)
  {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)
  (rho : MatrixRepresentation G (Fin N)) (hcalc : AdelicDifferentialCommutator F G hG)
  (hN : 0 < N) (hrho : IsClosedSubgroup rho) (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν
local notation "B₀" => (Subtype.mk ∅ (empty_subset Δ) : Idx)
local notation "rad(" Q ")" => SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q)
local notation "𝔉" => UniformGrowthFrechetSpace F G rho hG hcalc hN hrho R L
local notation "value" => UniformGrowthFrechetSpace.toFun F G rho hG hcalc hN hrho R L
local notation "asContinuous" => uniformGrowthToContinuousRational F G rho hN hrho hG hcalc R L
local notation "height" => adelicHeight F G rho

/-- Harish-Chandra components of a continuous linear Fréchet-valued family
have continuous linear point evaluations and uniform derivative growth,
and supply the relative smooth cuspidal family on the boundary. -/
def AdelicHarishChandraDirectionalGrowthStatement : Prop :=
  0 ≤ R → IsOpen (L : Set Gf) →
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  ∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℂ E] (S : E →L[ℂ] 𝔉)
    (P : Finset (characterLattice 𝓕.T)),
    ∃ ev : A → E →L[ℂ] ℂ,
      (∀ q, (fun x => ev x q) = 𝓕.hcComponent P (value (S q))) ∧
      (∀ q, Continuous (fun x => ev x q)) ∧
      (∀ q (b : Gf), ContMDiff IG IC ∞ (fun y : G∞ => ev (pair F G y b) q)) ∧
      (∀ q, ∀ r ∈ rationalImage F (𝓕.p B₀), ∀ x, ev (r * x) q = ev x q) ∧
      (∀ q (u : AdelicGroupPoints F (𝓕.U (𝓕.finsetIndex P))), ∀ x,
        ev (map F _ G (𝓕.iU (𝓕.finsetIndex P) ≫ 𝓕.p (𝓕.finsetIndex P)) u * x) q = ev x q) ∧
      (∀ q, ∀ l ∈ L, ∀ x, ev (x * ofFinite F G l) q = ev x q) ∧
      (∀ q, 𝓕.IsCuspidalAlong (𝓕.finsetIndex P) (fun x => ev x q)) ∧
      (∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧ ∀ q x,
        ‖adelicIteratedDirectionalValue hG s (fun y => ev y q) x‖ ≤ C * height x ^ R * ‖q‖)

theorem adelicHarishChandraDirectionalGrowth :
    AdelicHarishChandraDirectionalGrowthStatement.{u, v} 𝓕 hG rho hcalc hN hrho R L := by
  intro hR hLopen
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  intro E _ _ S P
  let f (q : E) := asContinuous (S q)
  have hf (q : E) : Continuous (value (S q)) :=
    (f q).property
  have hfS (q : E) (b : Gf) : ContMDiff IG IC ∞ (fun y : G∞ => value (S q) (pair F G y b)) := by
    let v := (S q : uniformGrowthLevelSubmodule F G rho hG hcalc R L).val
    exact ((mem_finitePlotSmoothRationalSubrepresentation_iff_contMDiff F G hG v.val).mp v.prop).1 b
  have hfL (q : E) : ∀ l ∈ L, ∀ x, value (S q) (x * ofFinite F G l) = value (S q) x := by
    intro l hl x
    let v := (S q : uniformGrowthLevelSubmodule F G rho hG hcalc R L)
    exact congrArg (fun z : FinitePlotSmoothRationalFunctions F G => evaluate F G z.val x) (v.prop.1 l hl)
  have hGrow := adelicUniformDirectionalGrowth hG rho hcalc hN hrho R L hR E S
  let g (Q : Idx) (q : E) := 𝓕.constantTerm Q (value (S q))
  have hGrowth (Q : Idx) := by
    have hU := (𝓕.isUnipotentRadical Q).isGeometricUnipotentRadical
    have hinv (q : E) (r : RationalGroupPoints F (𝓕.U Q)) (x : A) :
        value (S q) (map F (𝓕.U Q) G (𝓕.iU Q ≫ 𝓕.p Q) (rational F (𝓕.U Q) r) * x) = value (S q) x := by
      rw [map_rational]
      exact evaluate_rational_mul F G (f q) _ x
    exact adelicConstantTermDirectionalGrowth (𝓕.iU Q ≫ 𝓕.p Q) hG rho
      hU.2.1 hU.2.2.1 hU.2.2.2.1 hN L hLopen E (fun q => value (S q)) norm
      (fun q => norm_nonneg q) hf hfS hinv hfL R hR hGrow
  let eval (Q : Idx) (x : A) : E →L[ℂ] ℂ := by
    let := 𝓕.compactSpace_radicalRationalQuotient Q
    exact (subgroupConstantTermEvalCLM F G rho hN hrho hG hcalc R L (𝓕.iU Q ≫ 𝓕.p Q) x).comp S
  have hev (Q : Idx) (q : E) (x : A) : eval Q x q = g Q q x := by
    let := 𝓕.compactSpace_radicalRationalQuotient Q
    exact subgroupConstantTermEvalCLM_apply F G rho hN hrho hG hcalc R L (𝓕.iU Q ≫ 𝓕.p Q) x (S q)
  let c (Q : Finset (characterLattice 𝓕.T)) := (-1 : ℂ) ^ (P \ Q).card
  let ev (x : A) : E →L[ℂ] ℂ := ∑ Q ∈ P.powerset, c Q • eval (𝓕.finsetIndex Q) x
  have hSum (q : E) : (fun x => ev x q) = ∑ Q ∈ P.powerset, c Q • g (𝓕.finsetIndex Q) q := by
    funext x
    simp only [ev, sum_apply, smul_apply,
      hev, Finset.sum_apply, Pi.smul_apply]
  have hSum_apply (q : E) (x : A) : ev x q = ∑ Q ∈ P.powerset, c Q • g (𝓕.finsetIndex Q) q x := by
    simpa only [Finset.sum_apply, Pi.smul_apply] using congrFun (hSum q) x
  have hComponent (q : E) : (fun x => ev x q) = 𝓕.hcComponent P (value (S q)) := hSum q
  have hP₀ (Q : Idx) (q : E) (r : A) (hr : r ∈ rationalImage F (𝓕.p B₀)) (x : A) :
      g Q q (r * x) = g Q q x := by
    let := isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
    let := 𝓕.compactSpace_radicalRationalQuotient Q
    obtain ⟨v, rfl⟩ := (mem_rationalImage_iff _ _).mp hr
    let vG := (𝓕.P B₀).affinePointsTarget (𝓕.p B₀) (CommAlgCat.of F F) v
    have hNormalizer : (rad(Q)).IsNormalizedBy (SubgroupFunctor.range (𝓕.p B₀)) := by
      intro U r u hr hu
      have hrQ := ((𝓕.le_iff_range_le B₀ Q).mp (empty_subset Q.val)) U hr
      rw [(𝓕.isCompatible Q).parabolic_eq] at hrQ
      rw [𝓕.range_radical_eq_standardUnipotent] at hu ⊢
      exact StandardLeviIntersection.conj_mem_standardUnipotent 𝓕.i 𝓕.ν hrQ hu
    have hC (y : A) : g Q q y = normalizedConstantTerm F G rad(Q) (f q) y :=
      (normalizedConstantTerm_range_eq_subgroupConstantTerm F G (𝓕.iU Q ≫ 𝓕.p Q) (f q) y).symm
    rw [hC, hC, map_rational]
    exact normalizedConstantTerm_rationalNormalizer_mul F G rad(Q) hNormalizer ⟨vG, ⟨v, rfl⟩⟩ (f q) x
  have hUP (Q : Finset (characterLattice 𝓕.T)) (hQP : Q ⊆ P) (q : E)
      (u : AdelicGroupPoints F (𝓕.U (𝓕.finsetIndex P))) (x : A) :
      g (𝓕.finsetIndex Q) q (map F _ G (𝓕.iU (𝓕.finsetIndex P) ≫ 𝓕.p (𝓕.finsetIndex P)) u * x) =
        g (𝓕.finsetIndex Q) q x := by
    let J := 𝓕.finsetIndex Q
    let := isClosed_adelicPoints_range F G (𝓕.iU J ≫ 𝓕.p J)
    let := 𝓕.compactSpace_radicalRationalQuotient J
    let uG := map F _ G (𝓕.iU (𝓕.finsetIndex P) ≫ 𝓕.p (𝓕.finsetIndex P)) u
    have hJP : J ≤ 𝓕.finsetIndex P := fun α hα => ⟨hQP hα.1, hα.2⟩
    have huG : uG ∈ adelicPoints F G rad(J) := 𝓕.radical_le_of_le hJP _ ⟨u, rfl⟩
    have hC (y : A) : g J q y = normalizedConstantTerm F G rad(J) (f q) y :=
      (normalizedConstantTerm_range_eq_subgroupConstantTerm F G (𝓕.iU J ≫ 𝓕.p J) (f q) y).symm
    change g J q (uG * x) = g J q x
    rw [hC, hC]
    exact normalizedConstantTerm_subgroup_mul F G rad(J) (f q) ⟨uG, huG⟩ x
  refine ⟨ev, hComponent, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    simp only [hSum_apply]
    apply continuous_finsetSum
    intro Q _
    exact continuous_const.mul ((hGrowth (𝓕.finsetIndex Q)).1 q)
  · intro q b
    simp only [hSum_apply]
    refine contMDiff_finsetSum
      (f := fun Q (y : G∞) => c Q • g (𝓕.finsetIndex Q) q (pair F G y b)) (fun Q _ => ?_)
    exact (((ContinuousLinearMap.mul ℝ ℂ) (c Q)).contDiff.contMDiff).comp
      ((hGrowth (𝓕.finsetIndex Q)).2.1 q b)
  · intro q r hr x
    simp only [hSum_apply]
    exact Finset.sum_congr rfl (fun Q _ => congrArg (c Q • ·) (hP₀ (𝓕.finsetIndex Q) q r hr x))
  · intro q u x
    simp only [hSum_apply]
    exact Finset.sum_congr rfl (fun Q hQ => congrArg (c Q • ·) (hUP Q (Finset.mem_powerset.mp hQ) q u x))
  · intro q l hl x
    simp only [hSum_apply]
    exact Finset.sum_congr rfl (fun Q _ => congrArg (c Q • ·) ((hGrowth (𝓕.finsetIndex Q)).2.2.1 q l hl x))
  · intro q
    rw [hComponent]
    exact 𝓕.isCuspidalAlong_hcComponent P (f q)
  · intro s
    have hBounds (Q : Finset (characterLattice 𝓕.T)) := (hGrowth (𝓕.finsetIndex Q)).2.2.2.2 s
    choose C hC hCs using hBounds
    refine ⟨∑ Q ∈ P.powerset, ‖c Q‖ * C Q,
      Finset.sum_nonneg (fun Q _ => mul_nonneg (norm_nonneg _) (hC Q)), fun q x => ?_⟩
    rw [hSum, adelicIteratedDirectionalValue_finsetSum hG s P.powerset c (fun Q => g (𝓕.finsetIndex Q) q)
      (fun Q b => (hGrowth (𝓕.finsetIndex Q)).2.1 q b)]
    simp only [Finset.sum_apply, Pi.smul_apply]
    calc
      _ ≤ ∑ Q ∈ P.powerset, ‖c Q • adelicIteratedDirectionalValue hG s (g (𝓕.finsetIndex Q) q) x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ Q ∈ P.powerset, (‖c Q‖ * C Q) * height x ^ R * ‖q‖ := by
        refine Finset.sum_le_sum fun Q _ => ?_
        rw [norm_smul]
        calc
          _ ≤ ‖c Q‖ * (C Q * height x ^ R * ‖q‖) :=
            mul_le_mul_of_nonneg_left (hCs Q q x) (norm_nonneg _)
          _ = _ := by ring
      _ = _ := by simp only [Finset.sum_mul]

end StandardParabolicFamily
end Langlands.Global
