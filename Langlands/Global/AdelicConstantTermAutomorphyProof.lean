import Langlands.Global.AdelicRightConvolutionEnveloping
import Langlands.Global.AdelicUnipotentConstantTermEnveloping
import Langlands.Global.AdelicConstantTermAutomorphyStatement
import Langlands.Global.AdelicUnipotentConstantTermDifferentiation
import Langlands.Global.AdelicInducingConstantTermCovariance
import Langlands.Global.AdelicCuspidalProductVanishing
import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicParabolicConstantTermGrowth

/-! # Constant terms of automorphic functions on parabolic quotients are automorphic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj TensorProduct Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Index" => StandardIndex F G fam.i fam.ν
local notation "Γ[" J "]" => parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)

section Invariance

variable {P Q : StandardIndex F G fam.i fam.ν}

/-- The rational points of a smaller standard parabolic lie in `U_P(𝔸) M_P(F)`. -/
theorem rationalImage_le_parabolicQuotientSubgroup_of_le (hQP : Q ≤ P) :
    rationalImage F (fam.p Q) ≤ Γ[P] := by
  have hle : SubgroupFunctor.range (fam.p Q) ≤ SubgroupFunctor.range (fam.p P) :=
    (fam.le_iff_range_le Q P).mp hQP
  let : IsClosedImmersion (fam.p P).hom.hom.left := (fam.isCompatible P).parabolic.isClosedSubgroup
  have hcomp := SubgroupFunctor.rangeFactor_comp (fam.p Q) (fam.p P) hle
  rw [← hcomp]
  exact (rationalImage_comp_le _ _).trans (rationalImage_le_parabolicQuotientSubgroup _ _ _
    (fam.isCompatible P).levi (fam.isUnipotentRadical P))

/-- The rational points of the radical of a smaller standard parabolic lie in
`U_P(𝔸) M_P(F)`. -/
theorem rationalRadicalImage_le_of_le (hQP : Q ≤ P) :
    rationalImage F (fam.iU Q ≫ fam.p Q) ≤ Γ[P] :=
  (rationalImage_comp_le _ _).trans (fam.rationalImage_le_parabolicQuotientSubgroup_of_le hQP)

/-- The constant term along `Q ≤ P` of a continuous function on `U_P(𝔸) M_P(F) \ G(𝔸)` is
continuous and left invariant under `U_Q(𝔸) M_Q(F)`. -/
theorem constantTerm_continuous_and_invariant (hQP : Q ≤ P) {φ : AdelicGroupPoints F G → ℂ}
    (hc : Continuous φ) (hinv : IsLeftInvariantUnder F G Γ[P] φ) :
    Continuous (fam.constantTerm Q φ) ∧ IsLeftInvariantUnder F G Γ[Q] (fam.constantTerm Q φ) := by
  let : IsClosedImmersion (fam.p Q).hom.hom.left := (fam.isCompatible Q).parabolic.isClosedSubgroup
  obtain ⟨hcont, hrat, hrad⟩ := inducingConstantTermCovariance (fam.p Q) (fam.iU Q)
    (fam.isUnipotentRadical Q) φ hc
    (fun x hx g => hinv x (fam.rationalImage_le_parabolicQuotientSubgroup_of_le hQP hx) g)
  refine ⟨hcont, ?_⟩
  have hle : Γ[Q] ≤ scalarLeftStabilizer (fam.constantTerm Q φ) := by
    apply sup_le
    · intro x hx g
      exact hrad x hx g
    · rintro _ ⟨m, rfl⟩ g
      apply hrat
      exact (rationalImage_comp_le (fam.l Q) (fam.p Q)) ⟨m, rfl⟩
  intro x hx g
  exact hle hx g

end Invariance


section Enveloping

variable {P Q : StandardIndex F G fam.i fam.ν} {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

open scoped Classical in
/-- Continuous functions on `U_P(𝔸) M_P(F) \ G(𝔸)` with plot-smooth infinite slices, fixed on
the right by a given subgroup `L` of `G(𝔸_f)`. Openness of `L` is not part of this
structure; the lemmas that need it assume it separately. -/
structure IsRegularOn (P : StandardIndex F G fam.i fam.ν)
    (L : Subgroup (FiniteAdelicGroupPoints F G)) (f : AdelicGroupPoints F G → ℂ) : Prop where
  continuous : Continuous f
  smooth : ∀ b, functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G
  invariant : IsLeftInvariantUnder F G Γ[P] f
  level : ∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x

open scoped Classical in
/-- Right-orbit derivatives preserve regularity, and the constant term of a regular function has
plot-smooth slices whose derivatives are the constant terms of the derivatives. -/
theorem isRegularOn_derivative (hQP : Q ≤ P) {L : Subgroup (FiniteAdelicGroupPoints F G)}
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    {f : AdelicGroupPoints F G → ℂ} (hf : fam.IsRegularOn P L f) :
    (∀ X : smoothModel F d, fam.IsRegularOn P L (adelicDirectionalValue hsmooth X f)) ∧
    ∀ b, ∃ _h : functionInfiniteSlice F G (fam.constantTerm Q f) b ∈ InfinitePlotSmoothFunctions F G,
      ∀ X : smoothModel F d, ∀ a : InfiniteAdelicGroupPoints F G,
        letI := fun v : NumberField.InfinitePlace F =>
          InfinitePlaceGroupPoints.completionRCLike F v
        letI := smoothChartedSpace F G hsmooth
        groupDirectionalValue 𝓘(ℝ, smoothModel F d) X
            (functionInfiniteSlice F G (fam.constantTerm Q f) b) a =
          fam.constantTerm Q (adelicDirectionalValue hsmooth X f) (pair F G a b) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have hS : ∀ b : FiniteAdelicGroupPoints F G,
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun y => f (pair F G y b)) := fun b =>
    (InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hf.smooth b)
  have hR : ∀ (q : RationalGroupPoints F (fam.U Q)) (x : AdelicGroupPoints F G),
      f (map F (fam.U Q) G (fam.iU Q ≫ fam.p Q) (rational F (fam.U Q) q) * x) = f x :=
    fun q x => hf.invariant _ (fam.rationalRadicalImage_le_of_le hQP ⟨q, rfl⟩) x
  obtain ⟨hD, hCT⟩ := adelicUnipotentConstantTermDifferentiation (fam.iU Q ≫ fam.p Q) hsmooth
    (fam.isUnipotentRadical Q).1.smooth (fam.isUnipotentRadical Q).1.connectedSpace
    (fam.isUnipotentRadical Q).1.isUnipotent L hL f hf.continuous hS hR hf.level
  refine ⟨fun X => ?_, fun b => ⟨(InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hsmooth
    _).mpr (hCT b).1, fun X a => (hCT b).2 X a⟩⟩
  obtain ⟨hc, hs, -, hl⟩ := hD X
  refine ⟨hc, fun b => (InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
    (hs b), ?_, hl⟩
  intro y hy x
  have hfun : (fun t : InfiniteAdelicGroupPoints F G => f (y * x * ofInfinite F G t)) =
      fun t => f (x * ofInfinite F G t) :=
    funext fun t => by rw [mul_assoc]; exact hf.invariant y hy _
  unfold adelicDirectionalValue
  rw [hfun]

variable {L : Subgroup (FiniteAdelicGroupPoints F G)}

open scoped Classical in
theorem IsRegularOn.add {f g : AdelicGroupPoints F G → ℂ} (hf : fam.IsRegularOn P L f)
    (hg : fam.IsRegularOn P L g) : fam.IsRegularOn P L (f + g) where
  continuous := hf.continuous.add hg.continuous
  smooth b := (InfinitePlotSmoothFunctions F G).add_mem (hf.smooth b) (hg.smooth b)
  invariant x hx y := by
    simp only [Pi.add_apply, hf.invariant x hx y, hg.invariant x hx y]
  level l hl x := by
    simp only [Pi.add_apply, hf.level l hl x, hg.level l hl x]

open scoped Classical in
theorem IsRegularOn.smul (c : ℂ) {f : AdelicGroupPoints F G → ℂ} (hf : fam.IsRegularOn P L f) :
    fam.IsRegularOn P L (c • f) where
  continuous := hf.continuous.const_smul c
  smooth b := (InfinitePlotSmoothFunctions F G).smul_mem c (hf.smooth b)
  invariant x hx y := by
    simp only [Pi.smul_apply, hf.invariant x hx y]
  level l hl x := by
    simp only [Pi.smul_apply, hf.level l hl x]

/-- The constant term is additive on regular functions. -/
theorem constantTerm_add_of_isRegularOn (hQP : Q ≤ P) {f g : AdelicGroupPoints F G → ℂ}
    (hf : fam.IsRegularOn P L f) (hg : fam.IsRegularOn P L g) :
    fam.constantTerm Q (f + g) = fam.constantTerm Q f + fam.constantTerm Q g := by
  funext x
  have hif := fam.integrable_constantTermIntegrand_of_le P Q hQP hf.continuous hf.invariant x
  have hig := fam.integrable_constantTermIntegrand_of_le P Q hQP hg.continuous hg.invariant x
  unfold constantTerm subgroupConstantTerm
  simpa only [Pi.add_apply] using integral_add hif hig

open scoped Classical in
/-- Every element of the archimedean enveloping algebra acts on the slices of a regular function
through a regular function, and acts on the slices of its constant term through the constant
term of that function. -/
theorem constantTerm_envelopingAction (hQP : Q ≤ P)
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (a : AdelicEnvelopingAlgebra F G hsmooth) :
    ∀ (f : AdelicGroupPoints F G → ℂ) (hf : fam.IsRegularOn P L f),
      ∃ (fa : AdelicGroupPoints F G → ℂ) (hfa : fam.IsRegularOn P L fa),
        (∀ b, plotSmoothEnvelopingAction F G hsmooth hcalc a
            ⟨functionInfiniteSlice F G f b, hf.smooth b⟩ =
          ⟨functionInfiniteSlice F G fa b, hfa.smooth b⟩) ∧
        ∀ b (h : functionInfiniteSlice F G (fam.constantTerm Q f) b ∈
            InfinitePlotSmoothFunctions F G)
          (h' : functionInfiniteSlice F G (fam.constantTerm Q fa) b ∈
            InfinitePlotSmoothFunctions F G),
          plotSmoothEnvelopingAction F G hsmooth hcalc a ⟨_, h⟩ = ⟨_, h'⟩ := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  induction a using Langlands.Global.AdelicGroupPoints.complexEnveloping_induction with
  | h1 =>
    intro f hf
    refine ⟨f, hf, fun b => ?_, fun b h h' => ?_⟩
    · rw [map_one, Module.End.one_apply]
    · rw [map_one, Module.End.one_apply]
  | hadd x y hx hy =>
    intro f hf
    obtain ⟨fx, hfx, hsx, hcx⟩ := hx f hf
    obtain ⟨fy, hfy, hsy, hcy⟩ := hy f hf
    refine ⟨fx + fy, hfx.add fam hfy, fun b => ?_, fun b h h' => ?_⟩
    · rw [map_add, LinearMap.add_apply, hsx b, hsy b]
      rfl
    · obtain ⟨hx0, -⟩ := (fam.isRegularOn_derivative hsmooth hQP hL hfx).2 b
      obtain ⟨hy0, -⟩ := (fam.isRegularOn_derivative hsmooth hQP hL hfy).2 b
      rw [map_add, LinearMap.add_apply, hcx b h hx0, hcy b h hy0]
      apply Subtype.ext
      funext z
      change fam.constantTerm Q fx _ + fam.constantTerm Q fy _ = fam.constantTerm Q (fx + fy) _
      rw [fam.constantTerm_add_of_isRegularOn hQP hfx hfy]
      rfl
  | hsmul c x hx =>
    intro f hf
    obtain ⟨fx, hfx, hsx, hcx⟩ := hx f hf
    refine ⟨c • fx, hfx.smul fam c, fun b => ?_, fun b h h' => ?_⟩
    · rw [map_smul, LinearMap.smul_apply, hsx b]
      rfl
    · obtain ⟨hx0, -⟩ := (fam.isRegularOn_derivative hsmooth hQP hL hfx).2 b
      rw [map_smul, LinearMap.smul_apply, hcx b h hx0]
      apply Subtype.ext
      funext z
      change c * fam.constantTerm Q fx _ = fam.constantTerm Q (c • fx) _
      rw [fam.constantTerm_const_smul]
      rfl
  | hgen X x hx =>
    intro f hf
    obtain ⟨fx, hfx, hsx, hcx⟩ := hx f hf
    obtain ⟨hDer, hCT⟩ := fam.isRegularOn_derivative hsmooth hQP hL hfx
    refine ⟨adelicDirectionalValue hsmooth X fx, hDer X, fun b => ?_, fun b h h' => ?_⟩
    · rw [map_mul, Module.End.mul_apply, hsx b, plotSmoothEnvelopingAction_real_generator]
      apply Subtype.ext
      funext z
      exact (adelicDirectionalValue_pair hsmooth X fx z b).symm
    · obtain ⟨hx0, hxD⟩ := hCT b
      rw [map_mul, Module.End.mul_apply, hcx b h hx0, plotSmoothEnvelopingAction_real_generator]
      apply Subtype.ext
      funext z
      exact hxD X z

end Enveloping

section Finiteness

variable {P Q : StandardIndex F G fam.i fam.ν}

/-- Continuous functions on `U_P(𝔸) M_P(F) \ G(𝔸)`. -/
def continuousInvariantSubmodule (P : StandardIndex F G fam.i fam.ν) :
    Submodule ℂ (AdelicGroupPoints F G → ℂ) where
  carrier := {f | Continuous f ∧ IsLeftInvariantUnder F G Γ[P] f}
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  add_mem' {f g} hf hg := ⟨hf.1.add hg.1, fun x hx y => by
    simp only [Pi.add_apply, hf.2 x hx y, hg.2 x hx y]⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun x hx y => by
    simp only [Pi.smul_apply, hf.2 x hx y]⟩

/-- The constant term along `Q ≤ P` as a linear map on continuous functions on
`U_P(𝔸) M_P(F) \ G(𝔸)`. -/
def constantTermOnContinuous (hQP : Q ≤ P) :
    fam.continuousInvariantSubmodule P →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) where
  toFun f := fam.constantTerm Q f.val
  map_add' f g := by
    funext x
    have hif := fam.integrable_constantTermIntegrand_of_le P Q hQP f.2.1 f.2.2 x
    have hig := fam.integrable_constantTermIntegrand_of_le P Q hQP g.2.1 g.2.2 x
    change fam.constantTerm Q (f.val + g.val) x = fam.constantTerm Q f.val x + fam.constantTerm Q g.val x
    unfold constantTerm subgroupConstantTerm
    simpa only [Pi.add_apply] using integral_add hif hig
  map_smul' c f := by
    change fam.constantTerm Q (c • f.val) = c • fam.constantTerm Q f.val
    exact fam.constantTerm_const_smul Q c f.val

/-- Finiteness under right translation by a subgroup of `G(F_∞)` passes to constant terms. -/
theorem isInfiniteSubgroupFiniteFunction_constantTerm (hQP : Q ≤ P)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {φ : AdelicGroupPoints F G → ℂ}
    (hc : Continuous φ) (hinv : IsLeftInvariantUnder F G Γ[P] φ)
    (hK : IsInfiniteSubgroupFiniteFunction F G Kinf φ) :
    IsInfiniteSubgroupFiniteFunction F G Kinf (fam.constantTerm Q φ) := by
  let C := fam.continuousInvariantSubmodule P
  let T := fam.constantTermOnContinuous hQP
  let R : Kinf → C := fun k => ⟨fun g => φ (g * ofInfinite F G k),
    hc.comp (continuous_id.mul continuous_const), fun x hx y => by
      change φ (x * y * ofInfinite F G k) = φ (y * ofInfinite F G k)
      rw [mul_assoc]
      exact hinv x hx _⟩
  let V : Submodule ℂ C := Submodule.span ℂ (Set.range R)
  have hV : V.map C.subtype = Submodule.span ℂ (Set.range fun k : Kinf =>
      fun g : AdelicGroupPoints F G => φ (g * ofInfinite F G k)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hfin : FiniteDimensional ℂ (V.map C.subtype) := by
    rw [hV]
    exact hK
  have hVfin : FiniteDimensional ℂ V :=
    LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective C.subtype
      Subtype.val_injective V).symm
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kinf =>
    fun g : AdelicGroupPoints F G => fam.constantTerm Q φ (g * ofInfinite F G k)))
  apply Submodule.finiteDimensional_of_le (S₂ := V.map T)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  refine ⟨R k, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  funext g
  change fam.constantTerm Q (fun g => φ (g * ofInfinite F G k)) g =
    fam.constantTerm Q φ (g * ofInfinite F G k)
  unfold constantTerm subgroupConstantTerm
  simp only [mul_assoc]

/-- An ideal of the center annihilating the slices of a regular function annihilates the slices
of its constant term. -/
theorem isCenterFiniteFunction_constantTerm (hQP : Q ≤ P) {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    {L : Subgroup (FiniteAdelicGroupPoints F G)} (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    {φ : AdelicGroupPoints F G → ℂ} (hreg : fam.IsRegularOn P L φ)
    (hz : IsCenterFiniteFunction F G hsmooth hcalc φ) :
    IsCenterFiniteFunction F G hsmooth hcalc (fam.constantTerm Q φ) := by
  classical
  obtain ⟨J, hJfin, hJ⟩ := hz
  refine ⟨J, hJfin, fun z hz b h => ?_⟩
  obtain ⟨fz, hfz, hsl, hct⟩ :=
    fam.constantTerm_envelopingAction hsmooth hQP hL hcalc (z : AdelicEnvelopingAlgebra F G hsmooth)
      φ hreg
  have hzero : fz = 0 := by
    funext x
    have h1 := hJ z hz (finite F G x) (hreg.smooth (finite F G x))
    have h3 : (⟨functionInfiniteSlice F G fz (finite F G x), hfz.smooth _⟩ :
        InfinitePlotSmoothFunctions F G) = 0 := by
      rw [← hsl (finite F G x)]
      exact h1
    have h4 := congrArg (fun s : InfinitePlotSmoothFunctions F G => s.val (infinite F G x)) h3
    simpa [functionInfiniteSlice] using h4
  have h0 : functionInfiniteSlice F G (fam.constantTerm Q fz) b ∈
      InfinitePlotSmoothFunctions F G := by
    rw [hzero]
    convert (InfinitePlotSmoothFunctions F G).zero_mem using 1
    funext a
    simp [functionInfiniteSlice, constantTerm, subgroupConstantTerm]
  change InfiniteAdelicGroupPoints.plotSmoothEnvelopingAction F G hsmooth hcalc
    (z : AdelicEnvelopingAlgebra F G hsmooth) _ = 0
  rw [hct b h h0]
  apply Subtype.ext
  funext a
  simp [hzero, functionInfiniteSlice, constantTerm, subgroupConstantTerm]

end Finiteness

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Constant terms of automorphic functions on parabolic quotients are automorphic. -/
theorem constantTermAutomorphy : ConstantTermAutomorphyStatement.{u} := by
  intro F _ _ G _ _ _ fam Kinf N d rho hsmooth hrho P Q hQP φ hφ
  obtain ⟨hinv, ⟨hc, hS, L, hL, hLv⟩, hK, hz, hgr⟩ := hφ
  have hreg : fam.IsRegularOn P L φ := ⟨hc, hS, hinv, hLv⟩
  obtain ⟨hCTc, hCTinv⟩ := fam.constantTerm_continuous_and_invariant hQP hc hinv
  refine ⟨hCTinv, ⟨hCTc, fun b => ((fam.isRegularOn_derivative hsmooth hQP hL hreg).2 b).1, L, hL,
    fun l hl x => ?_⟩, fam.isInfiniteSubgroupFiniteFunction_constantTerm hQP Kinf hc hinv hK,
    fam.isCenterFiniteFunction_constantTerm hQP hsmooth _ hL hreg hz, ?_⟩
  · unfold StandardParabolicFamily.constantTerm subgroupConstantTerm
    congr 1
    funext q
    rw [← mul_assoc, hLv l hl]
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · have hG : Subsingleton (AdelicGroupPoints F G) :=
        ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
          (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
      refine ⟨‖fam.constantTerm Q φ 1‖ + 1, by positivity, 0, fun g => ?_⟩
      rw [Subsingleton.elim g 1, Real.rpow_zero, mul_one]
      linarith
    · exact (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mpr
        (fam.hasHeightGrowth_constantTerm hN Q
          ((hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mp hgr)
          (fam.isLeftInvariantUnder_rationalImage_of_le hQP hinv))

end Langlands.Global
