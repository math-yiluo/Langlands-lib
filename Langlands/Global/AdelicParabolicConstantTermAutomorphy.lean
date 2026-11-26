import Langlands.Global.AdelicUnipotentConstantTermDifferentiation
import Langlands.Global.AdelicInducingConstantTermCovariance
import Langlands.Global.AdelicParabolicConstantTermGrowth
import Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation

/-! # Constant terms of automorphic functions along nested parabolic subgroups

Mœglin–Waldspurger I.2.6 and I.2.17, Bernstein–Lapid §6.2: for parabolic subgroups
`P' ⊆ P` of `G`, the constant term `C_{U'}φ(g) = ∫_{U'(F) \ U'(𝔸)} φ(u g) du` of an automorphic
function `φ` on `U(𝔸)M(F) \ G(𝔸)` is an automorphic function on `U'(𝔸)M'(F) \ G(𝔸)`. The module
proves this for every subgroup `Γ ⊇ P'(F)` in place of `U(𝔸)M(F)`, with the same infinite
subgroup, the same matrix representation and the same annihilating ideal of the center of the
enveloping algebra. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open AdelicGroupPoints InfiniteAdelicGroupPoints Langlands.GroupScheme
  Langlands.Automorphic.GroupSchemeFunctions Langlands.Geometry.Manifold

section Unipotent

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "V" => SubgroupFunctor.range j
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "ν" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V

/-- Continuity and invariance under the rational points `U(F)` make the constant-term
integrand integrable on the compact quotient `U(F) \ U(𝔸)`. -/
theorem integrable_subgroupConstantTermIntegrand
    (hUs : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    {f : A → ℂ} (hf : Continuous f) (hinv : IsLeftInvariantUnder F G (rationalImage F j) f)
    (g : A) :
    letI : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set A) :=
      AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
    Integrable (fun q : Q =>
      f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G V) : A) * g)) ν := by
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set A) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : CompactSpace Q :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hUs hconn hu
  let : IsProbabilityMeasure ν :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G V
  let w := LeftCosetSpace.lift Γ
    (fun x : AdelicSubgroupPoints.adelicPoints F G V => f ((x : A) * g))
    (fun x y => by
      change f (((x.val : A) * y.val) * g) = f (y.val * g)
      rw [mul_assoc]
      exact hinv _ ((mem_rationalSubgroup_range_iff j x.val).mp x.2) _)
  have hw : Continuous w :=
    (LeftCosetSpace.continuous_iff Γ).mpr (hf.comp (continuous_subtype_val.mul continuous_const))
  have heq : (fun q : Q =>
      f (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G V) : A) * g)) = w := by
    funext q
    exact congrArg w (Quotient.out_eq q)
  rw [heq]
  exact hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The constant term is additive on continuous `U(F)`-invariant functions. -/
theorem subgroupConstantTerm_add
    (hUs : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    {f h : A → ℂ} (hf : Continuous f) (hfi : IsLeftInvariantUnder F G (rationalImage F j) f)
    (hh : Continuous h) (hhi : IsLeftInvariantUnder F G (rationalImage F j) h) :
    subgroupConstantTerm F j (f + h) = subgroupConstantTerm F j f + subgroupConstantTerm F j h := by
  funext g
  unfold subgroupConstantTerm
  simpa only [Pi.add_apply] using integral_add
    (integrable_subgroupConstantTermIntegrand j hUs hconn hu hf hfi g)
    (integrable_subgroupConstantTermIntegrand j hUs hconn hu hh hhi g)

/-- The constant term commutes with scalar multiplication. -/
theorem subgroupConstantTerm_smul (c : ℂ) (f : A → ℂ) :
    subgroupConstantTerm F j (c • f) = c • subgroupConstantTerm F j f := by
  funext g
  unfold subgroupConstantTerm
  simpa only [Pi.smul_apply] using integral_smul c _

/-- The constant term of zero is zero. -/
theorem subgroupConstantTerm_zero : subgroupConstantTerm F j (0 : A → ℂ) = 0 := by
  funext g
  unfold subgroupConstantTerm
  exact integral_zero _ _

/-- The constant term commutes with right translation. -/
theorem subgroupConstantTerm_rightTranslate (f : A → ℂ) (y g : A) :
    subgroupConstantTerm F j (fun x => f (x * y)) g = subgroupConstantTerm F j f (g * y) := by
  unfold subgroupConstantTerm
  simp only [mul_assoc]

end Unipotent

section Enveloping

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G

/-- Functions to which differentiation under the unipotent average applies: continuous,
plot-smooth on every infinite slice, left invariant under `U(F)` and right invariant under a
subgroup `L` of `G(𝔸_f)`. -/
def IsUnipotentAverageRegular (L : Subgroup Gf) (f : A → ℂ) : Prop :=
  Continuous f ∧ (∀ b, functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G) ∧
    IsLeftInvariantUnder F G (rationalImage F j) f ∧
    ∀ l ∈ L, ∀ x : A, f (x * ofFinite F G l) = f x

variable {j}

omit [IsAffine U.X.left] [LocallyOfFiniteType G.X.hom] [IsClosedImmersion j.hom.hom.left] in
theorem IsUnipotentAverageRegular.zero (L : Subgroup Gf) :
    IsUnipotentAverageRegular j L (0 : A → ℂ) :=
  ⟨continuous_const, fun _ => (InfinitePlotSmoothFunctions F G).zero_mem,
    fun _ _ _ => rfl, fun _ _ _ => rfl⟩

omit [IsAffine U.X.left] [LocallyOfFiniteType G.X.hom] [IsClosedImmersion j.hom.hom.left] in
theorem IsUnipotentAverageRegular.add {L : Subgroup Gf} {f h : A → ℂ}
    (hf : IsUnipotentAverageRegular j L f) (hh : IsUnipotentAverageRegular j L h) :
    IsUnipotentAverageRegular j L (f + h) :=
  ⟨hf.1.add hh.1, fun b => (InfinitePlotSmoothFunctions F G).add_mem (hf.2.1 b) (hh.2.1 b),
    fun x hx g => by simp only [Pi.add_apply, hf.2.2.1 x hx g, hh.2.2.1 x hx g],
    fun l hl x => by simp only [Pi.add_apply, hf.2.2.2 l hl x, hh.2.2.2 l hl x]⟩

omit [IsAffine U.X.left] [LocallyOfFiniteType G.X.hom] [IsClosedImmersion j.hom.hom.left] in
theorem IsUnipotentAverageRegular.smul {L : Subgroup Gf} {f : A → ℂ}
    (hf : IsUnipotentAverageRegular j L f) (c : ℂ) :
    IsUnipotentAverageRegular j L (c • f) :=
  ⟨hf.1.const_smul c, fun b => (InfinitePlotSmoothFunctions F G).smul_mem c (hf.2.1 b),
    fun x hx g => by simp only [Pi.smul_apply, hf.2.2.1 x hx g],
    fun l hl x => by simp only [Pi.smul_apply, hf.2.2.2 l hl x]⟩

omit [IsAffine U.X.left] [LocallyOfFiniteType G.X.hom] [IsClosedImmersion j.hom.hom.left] in
/-- A function all of whose infinite slices vanish is zero. -/
theorem eq_zero_of_functionInfiniteSlice_eq_zero {f : A → ℂ}
    (hf : ∀ b, functionInfiniteSlice F G f b = 0) : f = 0 := by
  funext x
  rw [← pair_projections F G x]
  exact congrFun (hf (finite F G x)) (infinite F G x)

/-- **Enveloping derivatives under the unipotent average.** For every element `D` of the
complex enveloping algebra and every regular `f`, there is a regular `f'` whose infinite slices
are the images of those of `f` under `D`, and such that `D` maps every infinite slice of the
constant term of `f` along `U` to the corresponding slice of the constant term of `f'`. -/
theorem exists_unipotentAverage_envelopingLift
    (hUs : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (L : Subgroup Gf) (hLo : IsOpen (L : Set Gf)) (D : AdelicEnvelopingAlgebra F G hsmooth) :
    ∀ f : A → ℂ, IsUnipotentAverageRegular j L f → ∃ f' : A → ℂ,
      IsUnipotentAverageRegular j L f' ∧
      (∀ b (h : functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G),
        (plotSmoothEnvelopingAction F G hsmooth hcalc D ⟨_, h⟩).val =
          functionInfiniteSlice F G f' b) ∧
      (∀ b (h : functionInfiniteSlice F G (subgroupConstantTerm F j f) b ∈
          InfinitePlotSmoothFunctions F G),
        (plotSmoothEnvelopingAction F G hsmooth hcalc D ⟨_, h⟩).val =
          functionInfiniteSlice F G (subgroupConstantTerm F j f') b) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  have hdiff := adelicUnipotentConstantTermDifferentiation j hsmooth hUs hconn hu L hLo
  -- the first-order step
  have hdir : ∀ (X : smoothModel F d) (f : A → ℂ), IsUnipotentAverageRegular j L f →
      IsUnipotentAverageRegular j L (adelicDirectionalValue hsmooth X f) ∧
      ∀ b a, groupDirectionalValue 𝓘(ℝ, smoothModel F d) X
          (fun y => subgroupConstantTerm F j f (pair F G y b)) a =
        subgroupConstantTerm F j (adelicDirectionalValue hsmooth X f) (pair F G a b) := by
    intro X f hf
    have h := hdiff f hf.1
      (fun b => (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hf.2.1 b))
      (fun q x => hf.2.2.1 _ ⟨q, rfl⟩ x) hf.2.2.2
    obtain ⟨hc, hs, hr, hl⟩ := h.1 X
    refine ⟨⟨hc, fun b => (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr (hs b), ?_, hl⟩,
      fun b a => (h.2 b).2 X a⟩
    rintro _ ⟨q, rfl⟩ x
    exact hr q x
  have hadd : ∀ {f h : A → ℂ}, IsUnipotentAverageRegular j L f →
      IsUnipotentAverageRegular j L h →
      subgroupConstantTerm F j (f + h) = subgroupConstantTerm F j f + subgroupConstantTerm F j h :=
    fun hf hh => subgroupConstantTerm_add j hUs hconn hu hf.1 hf.2.2.1 hh.1 hh.2.2.1
  -- the complexified Lie algebra
  have hLie : ∀ X : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G),
      ∀ f : A → ℂ, IsUnipotentAverageRegular j L f → ∃ f' : A → ℂ,
        IsUnipotentAverageRegular j L f' ∧
        (∀ b (h : functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G),
          (complexPlotSmoothLieAction F G hsmooth hcalc X ⟨_, h⟩).val =
            functionInfiniteSlice F G f' b) ∧
        (∀ b (h : functionInfiniteSlice F G (subgroupConstantTerm F j f) b ∈
            InfinitePlotSmoothFunctions F G),
          (complexPlotSmoothLieAction F G hsmooth hcalc X ⟨_, h⟩).val =
            functionInfiniteSlice F G (subgroupConstantTerm F j f') b) := by
    intro X
    induction X using TensorProduct.inductionOn with
    | tmul z X =>
      intro f hf
      obtain ⟨hreg, hC⟩ := hdir X f hf
      refine ⟨z • adelicDirectionalValue hsmooth X f, hreg.smul z, fun b h => ?_, fun b h => ?_⟩
      · rw [complexPlotSmoothLieAction_tmul, LinearMap.smul_apply]
        funext a
        change z • (plotSmoothDifferential F G hsmooth X ⟨_, h⟩).val a =
          z • adelicDirectionalValue hsmooth X f (pair F G a b)
        rw [adelicDirectionalValue_pair]
        rfl
      · rw [complexPlotSmoothLieAction_tmul, LinearMap.smul_apply, subgroupConstantTerm_smul]
        funext a
        change z • (plotSmoothDifferential F G hsmooth X ⟨_, h⟩).val a =
          z • subgroupConstantTerm F j (adelicDirectionalValue hsmooth X f) (pair F G a b)
        rw [← hC b a]
        rfl
    | add X Y hX hY =>
      intro f hf
      obtain ⟨f₁, hf₁, h₁s, h₁c⟩ := hX f hf
      obtain ⟨f₂, hf₂, h₂s, h₂c⟩ := hY f hf
      refine ⟨f₁ + f₂, hf₁.add hf₂, fun b h => ?_, fun b h => ?_⟩
      · rw [map_add, LinearMap.add_apply, Submodule.coe_add, h₁s b h, h₂s b h]
        rfl
      · rw [map_add, LinearMap.add_apply, Submodule.coe_add, h₁c b h, h₂c b h, hadd hf₁ hf₂]
        rfl
  -- the enveloping algebra, through the tensor algebra
  suffices hT : ∀ y : TensorAlgebra ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)),
      ∀ f : A → ℂ, IsUnipotentAverageRegular j L f → ∃ f' : A → ℂ,
        IsUnipotentAverageRegular j L f' ∧
        (∀ b (h : functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G),
          (plotSmoothEnvelopingAction F G hsmooth hcalc
            (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ y) ⟨_, h⟩).val =
            functionInfiniteSlice F G f' b) ∧
        (∀ b (h : functionInfiniteSlice F G (subgroupConstantTerm F j f) b ∈
            InfinitePlotSmoothFunctions F G),
          (plotSmoothEnvelopingAction F G hsmooth hcalc
            (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ y) ⟨_, h⟩).val =
            functionInfiniteSlice F G (subgroupConstantTerm F j f') b) by
    obtain ⟨y, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
      (UniversalEnvelopingAlgebra.ringCon ℂ
        (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) D
    exact hT y
  intro y
  induction y using TensorAlgebra.induction with
  | algebraMap c =>
    intro f hf
    refine ⟨c • f, hf.smul c, fun b h => ?_, fun b h => ?_⟩
    · simp only [AlgHom.commutes, Module.algebraMap_end_apply]
      rfl
    · simp only [AlgHom.commutes, Module.algebraMap_end_apply, subgroupConstantTerm_smul]
      rfl
  | «ι» X =>
    intro f hf
    obtain ⟨f', hf', hs, hc⟩ := hLie X f hf
    refine ⟨f', hf', fun b h => ?_, fun b h => ?_⟩
    · change (plotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.ι ℂ X) ⟨_, h⟩).val = _
      rw [plotSmoothEnvelopingAction_generator]
      exact hs b h
    · change (plotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.ι ℂ X) ⟨_, h⟩).val = _
      rw [plotSmoothEnvelopingAction_generator]
      exact hc b h
  | mul y z hy hz =>
    intro f hf
    obtain ⟨f₁, hf₁, h₁s, h₁c⟩ := hz f hf
    obtain ⟨f₂, hf₂, h₂s, h₂c⟩ := hy f₁ hf₁
    refine ⟨f₂, hf₂, fun b h => ?_, fun b h => ?_⟩
    · rw [map_mul, map_mul, Module.End.mul_apply]
      have e : plotSmoothEnvelopingAction F G hsmooth hcalc
          (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ z) ⟨_, h⟩ = ⟨_, hf₁.2.1 b⟩ :=
        Subtype.ext (h₁s b h)
      rw [e]
      exact h₂s b _
    · rw [map_mul, map_mul, Module.End.mul_apply]
      have hm : functionInfiniteSlice F G (subgroupConstantTerm F j f₁) b ∈
          InfinitePlotSmoothFunctions F G :=
        h₁c b h ▸ (plotSmoothEnvelopingAction F G hsmooth hcalc
          (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ z) ⟨_, h⟩).property
      have e : plotSmoothEnvelopingAction F G hsmooth hcalc
          (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ z) ⟨_, h⟩ = ⟨_, hm⟩ :=
        Subtype.ext (h₁c b h)
      rw [e]
      exact h₂c b _
  | add y z hy hz =>
    intro f hf
    obtain ⟨f₁, hf₁, h₁s, h₁c⟩ := hy f hf
    obtain ⟨f₂, hf₂, h₂s, h₂c⟩ := hz f hf
    refine ⟨f₁ + f₂, hf₁.add hf₂, fun b h => ?_, fun b h => ?_⟩
    · rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, h₁s b h, h₂s b h]
      rfl
    · rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, h₁c b h, h₂c b h,
        hadd hf₁ hf₂]
      rfl

include hsmooth in
/-- The constant term of a regular function is plot-smooth on every infinite slice. -/
theorem IsUnipotentAverageRegular.subgroupConstantTerm_slice_mem
    (hUs : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    {L : Subgroup Gf} (hLo : IsOpen (L : Set Gf)) {f : A → ℂ}
    (hf : IsUnipotentAverageRegular j L f) (b : Gf) :
    functionInfiniteSlice F G (subgroupConstantTerm F j f) b ∈ InfinitePlotSmoothFunctions F G := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have h := adelicUnipotentConstantTermDifferentiation j hsmooth hUs hconn hu L hLo f hf.1
    (fun b => (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hf.2.1 b))
    (fun q x => hf.2.2.1 _ ⟨q, rfl⟩ x) hf.2.2.2
  exact (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr (h.2 b).1

/-- An element of the center that annihilates every infinite slice of a regular function
annihilates every infinite slice of its constant term along `U`. -/
theorem IsUnipotentAverageRegular.centerAction_subgroupConstantTerm_eq_zero
    (hUs : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    {L : Subgroup Gf} (hLo : IsOpen (L : Set Gf)) {f : A → ℂ}
    (hf : IsUnipotentAverageRegular j L f) (z : AdelicEnvelopingCenter F G hsmooth)
    (hz : ∀ b (h : functionInfiniteSlice F G f b ∈ InfinitePlotSmoothFunctions F G),
      plotSmoothCenterAction F G hsmooth hcalc z ⟨_, h⟩ = 0)
    (b : Gf)
    (h : functionInfiniteSlice F G (subgroupConstantTerm F j f) b ∈
      InfinitePlotSmoothFunctions F G) :
    plotSmoothCenterAction F G hsmooth hcalc z ⟨_, h⟩ = 0 := by
  obtain ⟨f', _, hs, hc⟩ :=
    exists_unipotentAverage_envelopingLift hsmooth hcalc hUs hconn hu L hLo z.val f hf
  have h0 : f' = 0 := eq_zero_of_functionInfiniteSlice_eq_zero (fun b => by
    rw [← hs b (hf.2.1 b)]
    exact congrArg Subtype.val (hz b (hf.2.1 b)))
  apply Subtype.ext
  change (plotSmoothEnvelopingAction F G hsmooth hcalc z.val ⟨_, h⟩).val = 0
  rw [hc b h, h0, subgroupConstantTerm_zero]
  rfl

end Enveloping

section Growth

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

local notation "A" => AdelicGroupPoints F G
local notation "V" => SubgroupFunctor.range j

open AdelicSubgroupPoints RepresentationGrowth in
/-- The probability average along a compact unipotent quotient preserves moderate growth for
the adelic norm of a matrix representation. -/
theorem HasModerateGrowthFunction.subgroupConstantTerm
    (hUs : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    {N : ℕ} {rho : MatrixRepresentation G (Fin N)} {f : A → ℂ}
    (hf : HasModerateGrowthFunction F G rho f)
    (hinv : IsLeftInvariantUnder F G (rationalImage F j) f) :
    HasModerateGrowthFunction F G rho (subgroupConstantTerm F j f) := by
  let H := adelicPoints F G V
  let Δ := AdelicSubgroupPoints.rationalSubgroup F G V
  let : IsClosed (H : Set A) := isClosed_adelicPoints_range F G j
  let : CompactSpace (RationalQuotient F G V) :=
    compactSpace_rationalQuotient_range_unipotent F j hUs hconn hu
  let : IsProbabilityMeasure (normalizedRationalQuotientHaarMeasure F G V) :=
    normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨C, hC, r, hb⟩ := hf
    have hm (x : A) : adelicMatrix F G rho x = 1 := by
      apply Units.ext
      ext i k
      exact Fin.elim0 i
    have hs (x y : A) : adelicSourceNorm F G rho x = adelicSourceNorm F G rho y := by
      simp only [adelicSourceNorm, hm]
    refine ⟨C, hC, r, fun g => ?_⟩
    change ‖∫ q : RationalQuotient F G V, f ((Quotient.out q : H).val * g)
      ∂normalizedRationalQuotientHaarMeasure F G V‖ ≤ _
    refine (norm_integral_le_of_norm_le_const (C := C * adelicSourceNorm F G rho g ^ r)
      (Filter.Eventually.of_forall fun q => ?_)).trans_eq (by simp)
    rw [hs g ((Quotient.out q : H).val * g)]
    exact hb _
  · rw [hasModerateGrowthFunction_iff_hasHeightGrowth hN] at hf ⊢
    let Ht := adelicHeight F G rho
    have hH (x : A) : 0 ≤ Ht x := zero_le_one.trans (one_le_adelicHeight F G rho hN x)
    obtain ⟨C, r, hC, hr, hf⟩ := hf
    obtain ⟨B, hB⟩ := exists_le_of_compactSpace_leftCosetSpace Δ (fun n : H => Ht n.val)
      ((continuous_adelicHeight F G rho hN).comp continuous_subtype_val)
    have hB0 : 0 ≤ B := by
      obtain ⟨δ, _, hd⟩ := hB 1
      exact (hH (δ * (1 : H)).val).trans hd
    refine ⟨C * B ^ r, r, mul_nonneg hC (Real.rpow_nonneg hB0 _), hr, fun g => ?_⟩
    change ‖∫ q : RationalQuotient F G V, f ((Quotient.out q : H).val * g)
      ∂normalizedRationalQuotientHaarMeasure F G V‖ ≤ C * B ^ r * Ht g ^ r
    refine (norm_integral_le_of_norm_le_const (C := C * B ^ r * Ht g ^ r)
      (Filter.Eventually.of_forall fun q => ?_)).trans_eq (by simp)
    let v : H := Quotient.out q
    obtain ⟨δ, hδ, hδB⟩ := hB v
    let w : H := δ * v
    have heq : f (w.val * g) = f (v.val * g) := by
      change f ((δ.val * v.val) * g) = f (v.val * g)
      rw [mul_assoc, hinv _ ((mem_rationalSubgroup_range_iff j δ).mp hδ)]
    change ‖f (v.val * g)‖ ≤ _
    rw [← heq]
    have hw : Ht (w.val * g) ≤ B * Ht g :=
      (adelicHeight_mul_le F G rho hN _ _).trans (mul_le_mul_of_nonneg_right hδB (hH g))
    calc
      ‖f (w.val * g)‖ ≤ C * Ht (w.val * g) ^ r := hf _
      _ ≤ C * (B * Ht g) ^ r := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hH _) hw hr) hC
      _ = C * B ^ r * Ht g ^ r := by rw [Real.mul_rpow hB0 (hH g), mul_assoc]

end Growth

section Parabolic

variable {F : Type u} [Field F] [NumberField F]
  {G P' M' U' : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U'.X.left]
  [LocallyOfFiniteType G.X.hom]
  (p' : P' ⟶ G) (iU' : U' ⟶ P') (l' : M' ⟶ P') [IsClosedImmersion (iU' ≫ p').hom.hom.left]
  {d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "A" => AdelicGroupPoints F G

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Invariance under two subgroups gives invariance under the subgroup they generate. -/
theorem IsLeftInvariantUnder.sup {Γ₁ Γ₂ : Subgroup A} {f : A → ℂ}
    (h₁ : IsLeftInvariantUnder F G Γ₁ f) (h₂ : IsLeftInvariantUnder F G Γ₂ f) :
    IsLeftInvariantUnder F G (Γ₁ ⊔ Γ₂) f := by
  let S : Subgroup A :=
    { carrier := {x | ∀ g, f (x * g) = f g}
      mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
      one_mem' := fun g => by rw [one_mul]
      inv_mem' := fun {a} ha g => by rw [← ha (a⁻¹ * g), mul_inv_cancel_left] }
  intro x hx
  exact (sup_le (fun y hy => h₁ y hy) (fun y hy => h₂ y hy) : Γ₁ ⊔ Γ₂ ≤ S) hx

/-- **Constant terms of automorphic functions are automorphic.** Let `p' : P' → G` be a subgroup
with geometric unipotent radical `iU' : U' → P'`, `iU' ≫ p'` a closed immersion, and let
`l' : M' → P'` be any homomorphism. If `φ`
is automorphic on `Γ \ G(𝔸)` for a subgroup `Γ` containing the rational points `P'(F)`, then
its constant term along `U'` is automorphic on `U'(𝔸)M'(F) \ G(𝔸)`, for the same infinite
subgroup `Kinf` and the same matrix representation. -/
theorem IsAutomorphicFunctionOn.subgroupConstantTerm_of_rationalImage_le
    (hU' : LeviSubgroup.IsGeometricUnipotentRadical iU')
    {N : ℕ} {rho : MatrixRepresentation G (Fin N)} {Γ : Subgroup A}
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {φ : A → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ)
    (hΓ : rationalImage F p' ≤ Γ) :
    IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p' iU' l') Kinf rho
      (subgroupConstantTerm F (iU' ≫ p') φ) := by
  obtain ⟨hInv, hSm, hK, hZ, hGr⟩ := hφ
  have hUs := hU'.1.smooth
  have hconn := hU'.1.connectedSpace
  have hu := hU'.1.isUnipotent
  have hinvP : IsLeftInvariantUnder F G (rationalImage F p') φ := fun x hx => hInv x (hΓ hx)
  have hinvU : IsLeftInvariantUnder F G (rationalImage F (iU' ≫ p')) φ :=
    fun x hx => hinvP x (rationalImage_comp_le iU' p' hx)
  obtain ⟨hCont, hRat, hRad⟩ := inducingConstantTermCovariance p' iU' hU' φ hSm.1 hinvP
  obtain ⟨L, hLo, hLfix⟩ := hSm.2.2
  have hreg : IsUnipotentAverageRegular (iU' ≫ p') L φ := ⟨hSm.1, hSm.2.1, hinvU, hLfix⟩
  refine ⟨?_, ⟨hCont, hreg.subgroupConstantTerm_slice_mem hsmooth hUs hconn hu hLo, L, hLo, ?_⟩,
    ?_, ?_, HasModerateGrowthFunction.subgroupConstantTerm (iU' ≫ p') hUs hconn hu hGr hinvU⟩
  · exact IsLeftInvariantUnder.sup hRad (fun x hx => hRat x (rationalImage_comp_le l' p' hx))
  · intro l hl g
    rw [← subgroupConstantTerm_rightTranslate]
    exact congrArg (fun w => subgroupConstantTerm F (iU' ≫ p') w g) (funext (hLfix l hl))
  · let S : Submodule ℂ (A → ℂ) :=
      { carrier := {f | Continuous f ∧ IsLeftInvariantUnder F G (rationalImage F (iU' ≫ p')) f}
        add_mem' := fun {f h} hf hh => ⟨hf.1.add hh.1, fun x hx g => by
          simp only [Pi.add_apply, hf.2 x hx g, hh.2 x hx g]⟩
        zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
        smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun x hx g => by
          simp only [Pi.smul_apply, hf.2 x hx g]⟩ }
    let W := Submodule.span ℂ (Set.range fun k : Kinf =>
      fun g : A => φ (g * ofInfinite F G k))
    have hWS : W ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact ⟨hSm.1.comp (continuous_id.mul continuous_const), fun x hx g => by
        simp only
        rw [mul_assoc]
        exact hinvU x hx _⟩
    let T : W →ₗ[ℂ] (A → ℂ) :=
      { toFun := fun w => subgroupConstantTerm F (iU' ≫ p') w.1
        map_add' := fun v w => subgroupConstantTerm_add (iU' ≫ p') hUs hconn hu
          (hWS v.2).1 (hWS v.2).2 (hWS w.2).1 (hWS w.2).2
        map_smul' := fun c w => subgroupConstantTerm_smul (iU' ≫ p') c w.1 }
    have : FiniteDimensional ℂ W := hK
    apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨⟨_, Submodule.subset_span ⟨k, rfl⟩⟩, ?_⟩
    funext g
    exact subgroupConstantTerm_rightTranslate (iU' ≫ p') φ _ g
  · obtain ⟨J, hJ, hJann⟩ := hZ
    exact ⟨J, hJ, fun z hz b h =>
      hreg.centerAction_subgroupConstantTerm_eq_zero hsmooth hcalc hUs hconn hu hLo z
        (hJann z hz) b h⟩

/-- The nested case: for subgroups `P' ⊆ P` of `G`, with a rational Levi subgroup `l : M → P` and a
geometric unipotent radical `iU : U → P`, the constant term along `U'` of an automorphic function
on `U(𝔸)M(F) \ G(𝔸)` is automorphic on `U'(𝔸)M'(F) \ G(𝔸)`. -/
theorem IsAutomorphicFunctionOn.subgroupConstantTerm_of_range_le
    {P M U : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (hl : IsRationalLeviSubgroup l)
    (hU' : LeviSubgroup.IsGeometricUnipotentRadical iU')
    (hle : SubgroupFunctor.range p' ≤ SubgroupFunctor.range p)
    {N : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {φ : A → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l) Kinf rho φ) :
    IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p' iU' l') Kinf rho
      (subgroupConstantTerm F (iU' ≫ p') φ) :=
  IsAutomorphicFunctionOn.subgroupConstantTerm_of_rationalImage_le p' iU' l' hcalc hU' hφ
    ((rationalImage_le_of_range_le p' p hle).trans
      (rationalImage_le_parabolicQuotientSubgroup p iU l hl hU))

end Parabolic

/-- **Constant terms along parabolic subgroups preserve automorphy** (Mœglin–Waldspurger I.2.6
and I.2.17; Bernstein–Lapid §6.2). Let `G` be an affine group scheme, locally of finite type,
over a number field `F`, let `p' : P' → G` be a subgroup with geometric unipotent radical
`iU' : U' → P'` (`iU' ≫ p'` a closed immersion) and let `l' : M' → P'` be a homomorphism. If
`φ : G(𝔸) → ℂ` is automorphic on `Γ \ G(𝔸)` for a subgroup `Γ` of `G(𝔸)` containing the rational
points `P'(F)`, then its constant term `C_{U'}φ = subgroupConstantTerm F (iU' ≫ p') φ` is
automorphic on `U'(𝔸)M'(F) \ G(𝔸)`, for the same infinite subgroup `Kinf` and the same matrix
representation `rho`. -/
def ParabolicConstantTermAutomorphyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine U'.X.left]
    (p' : P' ⟶ G) (iU' : U' ⟶ P') (l' : M' ⟶ P') [IsClosedImmersion (iU' ≫ p').hom.hom.left],
    LeviSubgroup.IsGeometricUnipotentRadical iU' →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (Γ : Subgroup (AdelicGroupPoints F G)) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
      (φ : AdelicGroupPoints F G → ℂ),
      rationalImage F p' ≤ Γ →
      IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p' iU' l') Kinf rho
        (subgroupConstantTerm F (iU' ≫ p') φ)

theorem parabolicConstantTermAutomorphy : ParabolicConstantTermAutomorphyStatement.{u} := by
  intro F _ _ G P' M' U' _ _ _ p' iU' l' _ hU' N d rho hsmooth hcalc Γ Kinf φ hΓ hφ
  exact IsAutomorphicFunctionOn.subgroupConstantTerm_of_rationalImage_le p' iU' l' hcalc hU' hφ hΓ

end Langlands.Global
