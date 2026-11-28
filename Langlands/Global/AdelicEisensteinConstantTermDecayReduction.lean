import Langlands.Global.AdelicEisensteinConstantTermDecayStatement
import Langlands.Global.AdelicEisensteinUnitaryGrowthStatement
import Langlands.Global.AdelicEisensteinUnitaryExponentStatement
import Langlands.Global.AdelicUniformTemperednessCriterionProof
import Langlands.Global.AdelicShiftedMaximalDecay
import Langlands.Global.AdelicEisensteinCentralCovariance
import Langlands.Global.AdelicSiegelNormOne
import Langlands.Global.AdelicHalfModulusRootProductProof
import Langlands.GroupScheme.Rational.NestedSplitComponentFactorization

/-! # Decay of Eisenstein series minus their constant term, from uniform growth and exponents

Delorme 2023, Lemma 3.1 (Mœglin–Waldspurger 1995, Lemma I.2.10, for a standard parabolic `Q`),
applied to the Eisenstein series `E(φ, λ)` uniformly for `λ` in a compact subset of `i𝔞_P^*`
(`EisensteinConstantTermDecayStatement`), is derived from the uniform moderate growth of the
continued series (`EisensteinUnitaryUniformGrowthStatement`) and the subunitary exponents of its
constant terms (`EisensteinUnitaryExponentStatement`): `eisensteinConstantTermDecayReduction`.

The bounds of Delorme's Proposition 4.1 for the derivatives of `E` come from the Library's
chamber bound `StandardParabolicFamily.constantTerm_chamber_bound`, applied to the family of
derivative words of `E` (`derivative_chamber_bound`); its exponent `2m` does not depend on the
order of differentiation. The decay of `E − E_Q` is the sum, along a chain of standard indices
from `Δ` down to `J`, of the steps `C_{J''} E − C_{J'' ∖ α} E`, each bounded by the Library's
estimate of Mœglin–Waldspurger I.2.10, `StandardParabolicFamily.exists_constantTermStep_decay`
(`step_decay_bound`, `sub_constantTerm_bound`). The split component `A_G` acts on `E(λ)` and on
its constant terms by a unitary character for imaginary `λ`
(`eisensteinContinuation_splitCentre_mul`). -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry NumberField Set
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

namespace ConstantTermDecay

section Words

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {d : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)

/-- Right invariance under a subgroup of the finite points passes to derivative words. -/
theorem adelicIteratedDirectionalValue_mul_ofFinite {L : Subgroup Gf} {f : A → ℂ}
    (hf : ∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x) (s : List W) :
    ∀ l ∈ L, ∀ x, adelicIteratedDirectionalValue hG s f (x * ofFinite F G l) =
      adelicIteratedDirectionalValue hG s f x := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  induction s with
  | nil => exact hf
  | cons X s ih =>
    intro l hl x
    simp only [adelicIteratedDirectionalValue_cons]
    unfold adelicDirectionalValue
    apply congrArg (fun w : G∞ → ℂ => mvfderiv IG w 1 X)
    funext t
    rw [mul_assoc, ← (factors_commute F G t l).eq, ← mul_assoc, ih l hl]

/-- Left translation commutes with derivative words. -/
theorem adelicIteratedDirectionalValue_leftMul (s : List W) (f : A → ℂ) (c x : A) :
    adelicIteratedDirectionalValue hG s (fun y => f (c * y)) x =
      adelicIteratedDirectionalValue hG s f (c * x) := by
  induction s generalizing x with
  | nil => rfl
  | cons X s ih =>
    simp only [adelicIteratedDirectionalValue_cons]
    have h : adelicIteratedDirectionalValue hG s (fun y => f (c * y)) =
        fun y => adelicIteratedDirectionalValue hG s f (c * y) := funext ih
    rw [h]
    unfold adelicDirectionalValue
    simp only [mul_assoc]

/-- Derivative words of a function smooth on the archimedean slices are smooth on the slices. -/
theorem contMDiff_adelicIteratedDirectionalValue (f : A → ℂ) (s : List W) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    (∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f (pair F G y b))) →
    ∀ b : Gf, ContMDiff IG IC ∞
      (fun y : G∞ => adelicIteratedDirectionalValue hG s f (pair F G y b)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  intro hf b
  induction s with
  | nil => exact hf b
  | cons X s ih =>
    simp only [adelicIteratedDirectionalValue_cons, adelicDirectionalValue_pair]
    exact contMDiff_groupDirectionalValue IG X ih

/-- Left translates of a function smooth on the archimedean slices are smooth on the slices. -/
theorem contMDiff_leftMul (f : A → ℂ) (c : A) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    (∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f (pair F G y b))) →
    ∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f (c * pair F G y b)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  intro hf b
  have h : (fun y : G∞ => f (c * pair F G y b)) =
      (fun y => f (pair F G y (finite F G c * b))) ∘ (fun y => infinite F G c * y) := by
    funext y
    simp only [Function.comp]
    conv_lhs => rw [← pair_projections F G c]
    rw [pair_mul]
  rw [h]
  exact (hf _).comp contMDiff_mul_left

/-- Derivative words are linear on finite combinations of functions smooth on the archimedean
slices. -/
theorem adelicIteratedDirectionalValue_sum {Ix : Type*} (S : Finset Ix) (c : Ix → ℂ)
    (f : Ix → A → ℂ) (s : List W) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    (∀ i (b : Gf), ContMDiff IG IC ∞ (fun y : G∞ => f i (pair F G y b))) →
    adelicIteratedDirectionalValue hG s (fun x => ∑ i ∈ S, c i * f i x) =
      fun x => ∑ i ∈ S, c i * adelicIteratedDirectionalValue hG s (f i) x := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  intro hf
  let B := manifoldSmoothFunctions F G hG
  let d₀ (X : W) : Module.End ℂ B :=
    { toFun := fun h => ⟨groupDirectionalValue IG X h.val,
        contMDiff_groupDirectionalValue IG X h.prop⟩
      map_add' := fun h k => Subtype.ext (funext fun x =>
        groupDirectionalValue_add IG X h.prop k.prop x)
      map_smul' := fun c h => Subtype.ext (funext fun x =>
        groupDirectionalValue_const_smul IG X c h.prop x) }
  let D (s : List W) : Module.End ℂ B := s.foldr (fun X g => (d₀ X).comp g) LinearMap.id
  funext x
  rw [← pair_projections F G x]
  set b := finite F G x
  set a := infinite F G x
  have hslice (s : List W) (g : A → ℂ) (h : B) (heq : h.val = fun y => g (pair F G y b)) :
      (D s h).val = fun y => adelicIteratedDirectionalValue hG s g (pair F G y b) := by
    induction s with
    | nil => exact heq
    | cons X s ih =>
      funext y
      change groupDirectionalValue IG X (D s h).val y = _
      rw [adelicIteratedDirectionalValue_cons, adelicDirectionalValue_pair, ih]
  let fs (i : Ix) : B := ⟨fun y => f i (pair F G y b), hf i b⟩
  have htot : (∑ i ∈ S, c i • fs i).val =
      fun y => (fun x => ∑ i ∈ S, c i * f i x) (pair F G y b) := by
    funext y
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [← show (D s (∑ i ∈ S, c i • fs i)).val a = _ from congrFun (hslice s _ _ htot) a,
    map_sum, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    congrFun (hslice s (f i) (fs i) rfl) a]

/-- Derivative words preserve solutions of left translation equations. -/
theorem isTranslationPolynomialSolution_adelicIteratedDirectionalValue {a : A}
    {D : Polynomial ℂ} {φ : A → ℂ} (hsol : IsTranslationPolynomialSolution a D φ)
    (hφ : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hG
      ∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => φ (pair F G y b))) (s : List W) :
    IsTranslationPolynomialSolution a D (adelicIteratedDirectionalValue hG s φ) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  intro g
  have hsum := adelicIteratedDirectionalValue_sum hG (Finset.range (D.natDegree + 1))
    (fun k => D.coeff k) (fun k x => φ (a ^ k * x)) s
    (fun k => contMDiff_leftMul hG φ (a ^ k) hφ)
  have h0 : (fun x => ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * φ (a ^ k * x)) =
      fun _ => (0 : ℂ) := funext hsol
  have hz := congrFun hsum g
  rw [h0] at hz
  have hzero : adelicIteratedDirectionalValue hG s (fun _ => (0 : ℂ)) g = 0 := by
    have := congrFun (adelicIteratedDirectionalValue_sum hG (∅ : Finset ℕ) (fun _ => 0)
      (fun _ _ => 0) s (fun _ _ => contMDiff_const)) g
    simpa using this
  rw [hzero] at hz
  simp only [adelicIteratedDirectionalValue_leftMul] at hz
  exact hz.symm

end Words

section ConstantTerm

variable {F : Type} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  {d : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)

/-- **Derivative words commute with unipotent constant terms.** For a continuous function smooth
on the archimedean slices, left invariant under `U(F)` and right invariant under an open finite
level, every derivative word has the same properties and
`CT_U (D_s f) = D_s (CT_U f)`. -/
theorem subgroupConstantTerm_adelicIteratedDirectionalValue (hUs : Smooth U.X.hom)
    (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U) {L : Subgroup Gf}
    (hL : IsOpen (L : Set Gf)) (f : A → ℂ) (hf : Continuous f)
    (hfS : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hG
      ∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => f (pair F G y b)))
    (hfR : ∀ (q : RationalGroupPoints F U) x, f (map F U G j (rational F U q) * x) = f x)
    (hfL : ∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x) (s : List W) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    (Continuous (adelicIteratedDirectionalValue hG s f) ∧
      (∀ b : Gf, ContMDiff IG IC ∞
        (fun y : G∞ => adelicIteratedDirectionalValue hG s f (pair F G y b))) ∧
      (∀ (q : RationalGroupPoints F U) x, adelicIteratedDirectionalValue hG s f
        (map F U G j (rational F U q) * x) = adelicIteratedDirectionalValue hG s f x) ∧
      (∀ l ∈ L, ∀ x, adelicIteratedDirectionalValue hG s f (x * ofFinite F G l) =
        adelicIteratedDirectionalValue hG s f x)) ∧
    subgroupConstantTerm F j (adelicIteratedDirectionalValue hG s f) =
      adelicIteratedDirectionalValue hG s (subgroupConstantTerm F j f) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  induction s with
  | nil => exact ⟨⟨hf, hfS, hfR, hfL⟩, rfl⟩
  | cons X s ih =>
    obtain ⟨⟨h1, h2, h3, h4⟩, hct⟩ := ih
    obtain ⟨hX, hCT⟩ := adelicUnipotentConstantTermDifferentiation j hG hUs hconn hu L hL _
      h1 h2 h3 h4
    refine ⟨hX X, ?_⟩
    simp only [adelicIteratedDirectionalValue_cons]
    rw [← hct]
    funext x
    rw [← pair_projections F G x, adelicDirectionalValue_pair]
    exact ((hCT (finite F G x)).2 X (infinite F G x)).symm

end ConstantTerm

section DerivativeFamily

open StandardParabolicFamily PositiveRealTorus AdelicSiegelFactors RepresentationGrowth

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {𝓕 : StandardParabolicFamily F G}
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hG : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hG)

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "Jw" => Fin (Module.finrank ℝ W)
local notation "basisG" => Module.finBasis ℝ W
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν

local instance : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ


/-- The family of derivative words `u_s f_x` of a family `f`, indexed by pairs `(x, s)` of an
index and a word `s` of archimedean tangent directions. -/
def wordFamily {Ix : Type} (f : Ix → FinitePlotSmoothRationalFunctions F G)
    (p : Ix × List W) : FinitePlotSmoothRationalFunctions F G :=
  adelicEnvelopingAction F G hG hcalc (adelicDirectionalWordEnveloping hG p.2) (f p.1)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem evaluate_wordFamily {Ix : Type} (f : Ix → FinitePlotSmoothRationalFunctions F G)
    (p : Ix × List W) :
    evaluate F G (wordFamily hG hcalc f p).val =
      adelicIteratedDirectionalValue hG p.2 (evaluate F G (f p.1).val) :=
  evaluate_adelicDirectionalWordEnveloping hG hcalc _ _

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The derivative words in a finite set of words of a family with uniform moderate growth
form a family with uniform moderate growth, with the same exponent and level. -/
theorem isUniformGrowthFamily_wordFamily (hN : 0 < N) {Ix : Type}
    {f : Ix → FinitePlotSmoothRationalFunctions F G} {S : Set Ix} {L : Subgroup Gf} {R : ℝ}
    (hgrowth : IsUniformGrowthFamily rho hG hcalc L R f S) {Sw : Set (List W)}
    (hfin : Sw.Finite) :
    IsUniformGrowthFamily rho hG hcalc L R (wordFamily hG hcalc f) (S ×ˢ Sw) := by
  refine ⟨fun p hp l hl => ?_, fun u => ?_⟩
  · change finitePlotSmoothRightAction F G (ofFinite F G l)
      (finitePlotSmoothEnvelopingAction F G hG hcalc _ (f p.1)) = _
    rw [← finitePlotSmoothEnvelopingAction_finiteRightAction F G hG hcalc _ l (f p.1),
      hgrowth.1 p.1 hp.1 l hl]
    rfl
  · choose M hM using fun s : List W =>
      hgrowth.2 (u * adelicDirectionalWordEnveloping hG s)
    refine ⟨∑ s ∈ hfin.toFinset, |M s|, fun p hp g => ?_⟩
    have h1 := hM p.2 p.1 hp.1 g
    rw [map_mul, Module.End.mul_apply] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_
      (Real.rpow_nonneg (adelicSourceNorm_pos F G rho hN g).le _))
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun s => |M s|)
      (fun _ _ => abs_nonneg _) (hfin.mem_toFinset.mpr hp.2))

/-- Derivative words preserve subunitary shift equations. -/
theorem hasSubunitaryShiftEquations_adelicIteratedDirectionalValue {J : Idx} {m : ℕ}
    {φ : A → ℂ} (h : 𝓕.HasSubunitaryShiftEquations J m φ)
    (hφ : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hG
      ∀ b : Gf, ContMDiff IG IC ∞ (fun y : G∞ => φ (pair F G y b))) (s : List W) :
    𝓕.HasSubunitaryShiftEquations J m (adelicIteratedDirectionalValue hG s φ) := by
  intro t ht
  obtain ⟨w, hw, hsol⟩ := h t ht
  exact ⟨w, hw, isTranslationPolynomialSolution_adelicIteratedDirectionalValue hG hsol hφ s⟩

/-- Regularity of a family with uniform moderate growth and of its constant terms, and the
commutation of derivative words with the constant terms. -/
theorem family_regularity {Ix : Type} (f : Ix → FinitePlotSmoothRationalFunctions F G)
    (S : Set Ix) (L : Subgroup Gf) (R : ℝ) (hL : IsOpen (L : Set Gf))
    (hgrowth : IsUniformGrowthFamily rho hG hcalc L R f S) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    (∀ x, ∀ c : Gf, ContMDiff IG IC ∞
      (fun y : G∞ => evaluate F G (f x).val (pair F G y c))) ∧
    (∀ x ∈ S, ∀ l ∈ L, ∀ y,
      evaluate F G (f x).val (y * ofFinite F G l) = evaluate F G (f x).val y) ∧
    (∀ Q : Idx, ∀ x ∈ S, ∀ c : Gf, ContMDiff IG IC ∞
      (fun y : G∞ => 𝓕.constantTerm Q (evaluate F G (f x).val) (pair F G y c))) ∧
    (∀ Q : Idx, ∀ x ∈ S, ∀ s : List W,
      𝓕.constantTerm Q (adelicIteratedDirectionalValue hG s (evaluate F G (f x).val)) =
        adelicIteratedDirectionalValue hG s (𝓕.constantTerm Q (evaluate F G (f x).val))) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  have hfS (x : Ix) : ∀ c : Gf, ContMDiff IG IC ∞
      (fun y : G∞ => evaluate F G (f x).val (pair F G y c)) :=
    ((mem_finitePlotSmoothRationalSubrepresentation_iff_contMDiff F G hG (f x).val).mp
      (f x).prop).1
  have hfL : ∀ x ∈ S, ∀ l ∈ L, ∀ y,
      evaluate F G (f x).val (y * ofFinite F G l) = evaluate F G (f x).val y :=
    fun x hx l hl y => congrArg (fun z : FinitePlotSmoothRationalFunctions F G =>
      evaluate F G z.val y) (hgrowth.1 x hx l hl)
  have hinv (Q : Idx) (x : Ix) (q : RationalGroupPoints F (𝓕.U Q)) (y : A) :
      evaluate F G (f x).val (map F (𝓕.U Q) G (𝓕.iU Q ≫ 𝓕.p Q) (rational F (𝓕.U Q) q) * y) =
        evaluate F G (f x).val y := by
    rw [map_rational]
    exact evaluate_rational_mul F G (f x).val _ y
  refine ⟨hfS, hfL, fun Q x hx c => ?_, fun Q x hx s => ?_⟩
  · have hU := (𝓕.isUnipotentRadical Q).isGeometricUnipotentRadical
    exact ((adelicUnipotentConstantTermDifferentiation (𝓕.iU Q ≫ 𝓕.p Q) hG hU.2.1 hU.2.2.1
      hU.2.2.2.1 L hL (evaluate F G (f x).val) (f x).val.property (hfS x) (hinv Q x)
      (hfL x hx)).2 c).1
  · have hU := (𝓕.isUnipotentRadical Q).isGeometricUnipotentRadical
    exact (subgroupConstantTerm_adelicIteratedDirectionalValue (𝓕.iU Q ≫ 𝓕.p Q) hG hU.2.1
      hU.2.2.1 hU.2.2.2.1 hL (evaluate F G (f x).val) (f x).val.property (hfS x) (hinv Q x)
      (hfL x hx) s).2

/-- **The chamber bound for derivatives of constant terms.** For a family with uniform moderate
growth whose constant terms satisfy subunitary shift equations of order `m`, every derivative
word of length `n` of every constant term is bounded at `u ϖ` by
`C (2m ‖u‖ + 3)^{2m} δ_T(u)^{1/2}` on every chamber `{u : all root coordinates ≥ -θ}`. The
exponent `2m` does not depend on `n`. -/
theorem derivative_chamber_bound (hHM : HalfModulusRootProductStatement.{0}) [Fintype Δ]
    (Fr : TorusFrame 𝓕) (hN : 0 < N) {Ix : Type}
    (f : Ix → FinitePlotSmoothRationalFunctions F G) (S : Set Ix) (L : Subgroup Gf) (R : ℝ)
    (m : ℕ) (hL : IsOpen (L : Set Gf)) (hgrowth : IsUniformGrowthFamily rho hG hcalc L R f S)
    (hexp : ∀ J : Idx, ∀ x ∈ S,
      𝓕.HasSubunitaryShiftEquations J m (𝓕.constantTerm J (evaluate F G (f x).val)))
    (n : ℕ) (J : Idx) (Ω : Set A) (hΩ : IsCompact Ω) (θ : ℝ) (hθ : 0 ≤ θ) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ s : List Jw, s.length = n →
      ∀ u ∈ intrinsicSubgroup F 𝓕.T, (∀ α : Δ, -θ ≤ (Fr.crd u).1 α) → ∀ ϖ ∈ Ω,
        ‖adelicIteratedDirectionalValue hG (s.map basisG)
          (𝓕.constantTerm J (evaluate F G (f x).val)) (torusPoint (𝓕 := 𝓕) u * ϖ)‖ ≤
          C * (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) * Real.sqrt (torusModulus 𝓕 u) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  obtain ⟨-, -, hCTsm, hcomm⟩ := family_regularity rho hG hcalc (𝓕 := 𝓕) f S L R hL hgrowth
  set Sw : Set (List W) := (fun s : List Jw => s.map basisG) '' {s : List Jw | s.length = n}
    with hSw
  have hSwf : Sw.Finite := (List.finite_length_eq Jw n).image _
  have hgrowth' := isUniformGrowthFamily_wordFamily rho hG hcalc hN hgrowth hSwf
  have hexp' : ∀ J : Idx, ∀ y ∈ S ×ˢ Sw,
      𝓕.HasSubunitaryShiftEquations J m
        (𝓕.constantTerm J (evaluate F G (wordFamily hG hcalc f y).val)) := by
    intro J y hy
    rw [evaluate_wordFamily, hcomm J y.1 hy.1]
    exact hasSubunitaryShiftEquations_adelicIteratedDirectionalValue hG (hexp J y.1 hy.1)
      (hCTsm J y.1 hy.1) _
  obtain ⟨hgr, hdgr⟩ := family_growth_bounds rho hG hcalc Fr hN (wordFamily hG hcalc f)
    (S ×ˢ Sw) L R hL hgrowth'
  have hsm' : ∀ y ∈ S ×ˢ Sw, ∀ c : Gf, ContMDiff IG IC ∞
      (fun z : G∞ => evaluate F G (wordFamily hG hcalc f y).val (pair F G z c)) :=
    fun y _ c => ((mem_finitePlotSmoothRationalSubrepresentation_iff_contMDiff F G hG
      (wordFamily hG hcalc f y).val).mp (wordFamily hG hcalc f y).prop).1 c
  have hlev' : ∀ y ∈ S ×ˢ Sw, ∀ l ∈ L, ∀ z,
      evaluate F G (wordFamily hG hcalc f y).val (z * ofFinite F G l) =
        evaluate F G (wordFamily hG hcalc f y).val z :=
    fun y hy l hl z => congrArg (fun w : FinitePlotSmoothRationalFunctions F G =>
      evaluate F G w.val z) (hgrowth'.1 y hy l hl)
  have hsh' : ∀ J J' : Idx, J'.1 ⊆ J.1 → ∀ y ∈ S ×ˢ Sw,
      HasTorusShiftEquations 𝓕 J.1 m
        (𝓕.constantTerm J' (evaluate F G (wordFamily hG hcalc f y).val)) :=
    fun J J' hJ y hy => hasTorusShiftEquations_of_le hHM hJ (hexp' J' y hy)
  obtain ⟨C, hC0, hC⟩ := constantTerm_chamber_bound Fr hG
    (fun y => (wordFamily hG hcalc f y).val) (S ×ˢ Sw) m L hL
    hsm' hlev' hsh' hgr hdgr J Ω hΩ θ hθ
  refine ⟨C, hC0, fun x hx s hs u hu hθu ϖ hϖ => ?_⟩
  have h := hC (x, s.map basisG) ⟨hx, s, hs, rfl⟩ u hu hθu ϖ hϖ
  rw [evaluate_wordFamily, hcomm J x hx] at h
  exact h

/-- **Decay of one constant-term step at the Siegel points.** Let `j : T₀ → T` map a split
torus into the maximal split torus so that the positive points of `T₀` map to norm-one points.
For a family with uniform moderate growth whose constant terms satisfy subunitary shift
equations of order `m`, a standard index `J`, a simple root `α`, a threshold `t`, a compact `Ω`
and `k : ℕ`, there is `B` with
`‖(C_J f_x − C_{J ∖ α} f_x)(b ϖ)‖ ≤ B δ(b)^{1/2} (1 + R')^{2m} e^{−k s}` whenever `b` lies in the
weak chamber of threshold `t`, `ϖ ∈ Ω`, `|log |β(b)|| ≤ R'` for every simple root `β` and
`s ≤ log |α(b)|`. -/
theorem step_decay_bound (hHM : HalfModulusRootProductStatement.{0}) [Fintype Δ]
    (Fr : TorusFrame 𝓕) (hN : 0 < N) {Ix : Type}
    (f : Ix → FinitePlotSmoothRationalFunctions F G) (S : Set Ix) (L : Subgroup Gf) (R : ℝ)
    (m : ℕ) (hL : IsOpen (L : Set Gf)) (hgrowth : IsUniformGrowthFamily rho hG hcalc L R f S)
    (hexp : ∀ J : Idx, ∀ x ∈ S,
      𝓕.HasSubunitaryShiftEquations J m (𝓕.constantTerm J (evaluate F G (f x).val)))
    {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ 𝓕.T)
    (hT₀ : IsSplitTorus T₀.toGrp)
    (hnorm : ∀ b : intrinsicSubgroup F T₀,
      positiveMap F G 𝓕.T 𝓕.i T₀ j b ∈ normOneSubgroup F G)
    (J : Idx) {α : characterLattice 𝓕.T} (hα : α ∈ Δ) (t : ℝ≥0ˣ) (Ω : Set A)
    (hΩ : IsCompact Ω) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ∀ b ∈ weakSimpleRootChamber F T₀ 𝓕.T j G 𝓕.i 𝓕.ν t, ∀ ϖ ∈ Ω,
      ∀ R' s : ℝ, (∀ β ∈ Δ, |logNormHom F T₀ b.val (j ≫ β)| ≤ R') →
        s ≤ logNormHom F T₀ b.val (j ≫ α) →
        ‖𝓕.constantTermStep J α (evaluate F G (f x).val)
            (positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ)‖ ≤
          B * Real.sqrt (siegelModulus F G 𝓕.T 𝓕.i 𝓕.ν T₀ j b) * (1 + R') ^ (2 * m) *
            Real.exp (-(k * s)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  obtain ⟨hfS, hfL, hCTsm, -⟩ := family_regularity rho hG hcalc (𝓕 := 𝓕) f S L R hL hgrowth
  set dF : ℕ := Module.finrank ℚ F with hdF
  have hdF0 : (0 : ℝ) < dF := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  set n₀ : ℕ := k * dF with hn₀
  have hYf : IsCompact (finite F G '' Ω) := hΩ.image (finite F G).continuous
  obtain ⟨K', hK', -, Cdec, hCdec, hdec⟩ :=
    exists_constantTermStep_decay 𝓕 hG j J hα L hL t n₀ Ω hΩ (finite F G '' Ω) hYf
  set σ : ℝ := ∑ β : Δ, (Fr.step β)⁻¹ with hσdef
  have hσ : 0 ≤ σ := Finset.sum_nonneg fun β _ => (inv_pos.mpr (Fr.step_pos β)).le
  have hσβ : ∀ β : Δ, (Fr.step β)⁻¹ ≤ σ := fun β => Finset.single_le_sum
    (f := fun β => (Fr.step β)⁻¹) (fun β _ => (inv_pos.mpr (Fr.step_pos β)).le)
    (Finset.mem_univ β)
  set lt : ℝ := Real.log ((t : ℝ≥0) : ℝ) with hlt
  set θ : ℝ := |lt| * σ with hθdef
  have hθ : 0 ≤ θ := mul_nonneg (abs_nonneg _) hσ
  obtain ⟨C₁, hC₁0, hC₁⟩ := derivative_chamber_bound rho hG hcalc hHM Fr hN f S L R m hL
    hgrowth hexp n₀ J K' hK' θ hθ
  obtain ⟨C₂, hC₂0, hC₂⟩ := derivative_chamber_bound rho hG hcalc hHM Fr hN f S L R m hL
    hgrowth hexp n₀ (𝓕.removeSimpleRoot J α) K' hK' θ hθ
  refine ⟨Cdec * (C₁ + C₂) * (2 * (m : ℝ) * σ + 3) ^ (2 * m), by positivity, ?_⟩
  intro x hx b hb ϖ hϖ R' s hR' hs
  set u : AdelicGroupPoints F 𝓕.T.toGrp :=
    map F T₀.toGrp 𝓕.T.toGrp (CommGroupScheme.groupHom j) b.val with hudef
  have hu : u ∈ intrinsicSubgroup F 𝓕.T :=
    map_intrinsicSubgroup_le F T₀ 𝓕.T j ⟨b.val, b.prop, rfl⟩
  have hpt : torusPoint (𝓕 := 𝓕) u = positiveMap F G 𝓕.T 𝓕.i T₀ j b := by
    show map F 𝓕.T.toGrp G 𝓕.i u = _
    rfl
  have hroot : ∀ β, normCharacter F 𝓕.T β u = normCharacter F T₀ (j ≫ β) b := by
    intro β
    rw [normCharacter_pullback]
    rfl
  have hcrd : ∀ β : Δ, Fr.step β * (Fr.crd u).1 β = logNormHom F T₀ b.val (j ≫ β.val) := by
    intro β
    rw [← Fr.characterLog_root, ← log_normCharacter, hroot]
    rfl
  have hcentral : (Fr.crd u).2 = 0 := by
    show (Fr.e (characterLog F 𝓕.T.toGrp u)).2 = 0
    apply (Fr.central (characterLog F 𝓕.T.toGrp u)).mpr
    rw [← characterLog_map, characterLog_eq_zero_iff]
    rw [show map F 𝓕.T.toGrp G 𝓕.i u = positiveMap F G 𝓕.T 𝓕.i T₀ j b from hpt]
    exact hnorm b
  have hchamber : ∀ β : Δ, -θ ≤ (Fr.crd u).1 β := by
    intro β
    have hstep := Fr.step_pos β
    have h1 := hcrd β
    have h2 : lt ≤ logNormHom F T₀ b.val (j ≫ β.val) := by
      have h := hb β.val β.prop
      have htpos : (0 : ℝ) < ((t : ℝ≥0) : ℝ) := by exact_mod_cast (Units.ne_zero t).bot_lt
      change Real.log ((t : ℝ≥0) : ℝ) ≤
        Real.log ((normCharacter F T₀ (j ≫ β.val) b.val : ℝ≥0) : ℝ)
      exact Real.log_le_log htpos (by exact_mod_cast Units.val_le_val.mpr h)
    have h4 : |lt| * (Fr.step β)⁻¹ ≤ θ := mul_le_mul_of_nonneg_left (hσβ β) (abs_nonneg _)
    have h5 : -(|lt| * (Fr.step β)⁻¹) ≤ (Fr.crd u).1 β := by
      have e : -(|lt| * (Fr.step β)⁻¹) = (-|lt|) / Fr.step β := by ring
      rw [e, div_le_iff₀ hstep]
      have := neg_abs_le lt
      nlinarith
    linarith
  have hR0 : 0 ≤ R' := (abs_nonneg _).trans (hR' α hα)
  have hcrd_le : ‖Fr.crd u‖ ≤ R' * σ := by
    refine (Fr.norm_crd_le u (a := R' * σ) (b := 0) (by positivity)
      (by rw [hcentral, norm_zero]) fun β => ?_).trans (max_le le_rfl (by positivity))
    have hstep := Fr.step_pos β
    have h1 : |(Fr.crd u).1 β| * Fr.step β = |logNormHom F T₀ b.val (j ≫ β.val)| := by
      rw [← hcrd β, abs_mul, abs_of_pos hstep, mul_comm]
    have h2 := hR' β.val β.prop
    have h3 : 1 ≤ σ * Fr.step β := by
      have := mul_le_mul_of_nonneg_right (hσβ β) hstep.le
      rwa [inv_mul_cancel₀ hstep.ne'] at this
    nlinarith [mul_le_mul_of_nonneg_left h3 (abs_nonneg ((Fr.crd u).1 β)),
      mul_le_mul_of_nonneg_left h2 hσ]
  have hpoly : 2 * (m : ℝ) * ‖Fr.crd u‖ + 3 ≤ (2 * (m : ℝ) * σ + 3) * (1 + R') := by
    have hm0 : (0 : ℝ) ≤ 2 * (m : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hcrd_le hm0, mul_nonneg hm0 hσ]
  have hmod : torusModulus 𝓕 u = siegelModulus F G 𝓕.T 𝓕.i 𝓕.ν T₀ j b := by
    unfold torusModulus siegelModulus
    refine finprod_congr fun β => finprod_congr fun _ => ?_
    rw [hroot β]
  set M : ℝ := (C₁ + C₂) * (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) *
    Real.sqrt (torusModulus 𝓕 u) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hfin : finite F G (positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ) ∈ finite F G '' Ω := by
    rw [map_mul, finite_positiveMap F G 𝓕.T 𝓕.i T₀ j hT₀, one_mul]
    exact ⟨ϖ, hϖ, rfl⟩
  have hd := hdec (f x).val (hfS x) (hfL x hx) b hb ϖ hϖ hfin M hM0 (by
    intro k' hk' _ s' hs'
    have hsub := adelicIteratedDirectionalValue_sub hG (s'.map basisG)
      (𝓕.constantTerm J (evaluate F G (f x).val))
      (𝓕.constantTerm (𝓕.removeSimpleRoot J α) (evaluate F G (f x).val))
      (hCTsm J x hx) (hCTsm _ x hx)
    change ‖adelicIteratedDirectionalValue hG (s'.map basisG)
      (𝓕.constantTerm J (evaluate F G (f x).val) -
        𝓕.constantTerm (𝓕.removeSimpleRoot J α) (evaluate F G (f x).val))
      (positiveMap F G 𝓕.T 𝓕.i T₀ j b * k')‖ ≤ M
    rw [hsub, Pi.sub_apply, ← hpt]
    have e1 := hC₁ x hx s' hs' u hu hchamber k' hk'
    have e2 := hC₂ x hx s' hs' u hu hchamber k' hk'
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ _ := add_le_add e1 e2
      _ = M := by rw [hMdef]; ring)
  have hnc : (0 : ℝ) < ((normCharacter F T₀ (j ≫ α) b : ℝ≥0) : ℝ) := by
    exact_mod_cast pos_iff_ne_zero.mpr (normCharacter F T₀ (j ≫ α) b).ne_zero
  have hrel : relativeCharacterDecay j α b ^ n₀ =
      Real.exp (-(k * logNormHom F T₀ b.val (j ≫ α))) := by
    rw [relativeCharacterDecay, ← Real.rpow_natCast, ← Real.rpow_mul hnc.le,
      Real.rpow_def_of_pos hnc]
    congr 1
    change Real.log _ * _ = -(k * Real.log _)
    rw [hn₀]
    push_cast
    rw [← hdF]
    have := hdF0.ne'
    field_simp
  have hexp_le : Real.exp (-(k * logNormHom F T₀ b.val (j ≫ α))) ≤ Real.exp (-(k * s)) :=
    Real.exp_le_exp.mpr (by nlinarith [hs, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hP : (2 * (m : ℝ) * ‖Fr.crd u‖ + 3) ^ (2 * m) ≤
      ((2 * (m : ℝ) * σ + 3) * (1 + R')) ^ (2 * m) :=
    pow_le_pow_left₀ (by positivity) hpoly _
  calc _ ≤ Cdec * relativeCharacterDecay j α b ^ n₀ * M := hd
    _ ≤ Cdec * Real.exp (-(k * s)) * ((C₁ + C₂) * ((2 * (m : ℝ) * σ + 3) * (1 + R')) ^ (2 * m) *
          Real.sqrt (siegelModulus F G 𝓕.T 𝓕.i 𝓕.ν T₀ j b)) := by
        rw [hrel, hMdef, hmod]
        gcongr
    _ = _ := by rw [mul_pow]; ring

/-- **Decay of the difference from a constant term at the Siegel points.** Under the hypotheses
of `step_decay_bound`, for a standard index `J` there is `B` with
`‖(f_x − C_J f_x)(b ϖ)‖ ≤ B δ(b)^{1/2} (1 + R')^{2m} e^{−k s}` whenever `|log |β(b)|| ≤ R'` for
every simple root `β` and `s ≤ log |α(b)|` for every simple root `α ∉ J`. The difference is the
sum of the steps `C_{J''} f_x − C_{J'' ∖ α} f_x` along a chain of standard indices from `Δ` down
to `J`, removing one root `α ∉ J` at a time. -/
theorem sub_constantTerm_bound (hHM : HalfModulusRootProductStatement.{0}) [Fintype Δ]
    (Fr : TorusFrame 𝓕) (hN : 0 < N) {Ix : Type}
    (f : Ix → FinitePlotSmoothRationalFunctions F G) (S : Set Ix) (L : Subgroup Gf) (R : ℝ)
    (m : ℕ) (hL : IsOpen (L : Set Gf)) (hgrowth : IsUniformGrowthFamily rho hG hcalc L R f S)
    (hexp : ∀ J : Idx, ∀ x ∈ S,
      𝓕.HasSubunitaryShiftEquations J m (𝓕.constantTerm J (evaluate F G (f x).val)))
    {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ 𝓕.T)
    (hT₀ : IsSplitTorus T₀.toGrp)
    (hnorm : ∀ b : intrinsicSubgroup F T₀,
      positiveMap F G 𝓕.T 𝓕.i T₀ j b ∈ normOneSubgroup F G)
    (J : Idx) (t : ℝ≥0ˣ) (Ω : Set A) (hΩ : IsCompact Ω) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ∀ b ∈ weakSimpleRootChamber F T₀ 𝓕.T j G 𝓕.i 𝓕.ν t, ∀ ϖ ∈ Ω,
      ∀ R' s : ℝ, (∀ β ∈ Δ, |logNormHom F T₀ b.val (j ≫ β)| ≤ R') →
        (∀ α ∈ Δ, α ∉ J.1 → s ≤ logNormHom F T₀ b.val (j ≫ α)) →
        ‖evaluate F G (f x).val (positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ) -
            𝓕.constantTerm J (evaluate F G (f x).val) (positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ)‖ ≤
          B * Real.sqrt (siegelModulus F G 𝓕.T 𝓕.i 𝓕.ν T₀ j b) * (1 + R') ^ (2 * m) *
            Real.exp (-(k * s)) := by
  have hΔf : (Δ : Set (characterLattice 𝓕.T)).Finite := Set.toFinite _
  suffices H : ∀ n : ℕ, ∀ J' : Idx, J.1 ⊆ J'.1 → (Δ \ J'.1).ncard = n →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ∀ b ∈ weakSimpleRootChamber F T₀ 𝓕.T j G 𝓕.i 𝓕.ν t, ∀ ϖ ∈ Ω,
        ∀ R' s : ℝ, (∀ β ∈ Δ, |logNormHom F T₀ b.val (j ≫ β)| ≤ R') →
          (∀ α ∈ Δ, α ∉ J.1 → s ≤ logNormHom F T₀ b.val (j ≫ α)) →
          ‖evaluate F G (f x).val (positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ) -
              𝓕.constantTerm J' (evaluate F G (f x).val)
                (positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ)‖ ≤
            B * Real.sqrt (siegelModulus F G 𝓕.T 𝓕.i 𝓕.ν T₀ j b) * (1 + R') ^ (2 * m) *
              Real.exp (-(k * s)) from H _ J subset_rfl rfl
  intro n
  induction n with
  | zero =>
    intro J' _ hn
    have hJ' : J' = 𝓕.top := by
      apply Subtype.ext
      have h0 : Δ \ J'.1 = ∅ := (Set.ncard_eq_zero (hΔf.subset fun y hy => hy.1)).mp hn
      exact Set.Subset.antisymm J'.2 (Set.sdiff_eq_empty.mp h0)
    refine ⟨0, le_rfl, fun x _ b _ ϖ _ R' s _ _ => ?_⟩
    rw [hJ', constantTerm_top, sub_self, norm_zero]
    simp only [zero_mul, le_refl]
  | succ n ih =>
    intro J' hJJ' hn
    have hne : (Δ \ J'.1).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hn]; omega)
    obtain ⟨α, hαΔ, hαJ'⟩ := hne
    let Jp : Idx := ⟨insert α J'.1, Set.insert_subset hαΔ J'.2⟩
    have hn' : (Δ \ Jp.1).ncard = n := by
      have e : Δ \ Jp.1 = (Δ \ J'.1) \ {α} := by
        ext y
        simp only [Jp, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        tauto
      rw [e, Set.ncard_sdiff_singleton_of_mem (show α ∈ Δ \ J'.1 from ⟨hαΔ, hαJ'⟩), hn]
      rfl
    obtain ⟨B₁, hB₁0, hB₁⟩ := ih Jp (hJJ'.trans (Set.subset_insert _ _)) hn'
    obtain ⟨B₂, hB₂0, hB₂⟩ := step_decay_bound rho hG hcalc hHM Fr hN f S L R m hL hgrowth
      hexp j hT₀ hnorm Jp hαΔ t Ω hΩ k
    have hrem : 𝓕.removeSimpleRoot Jp α = J' := by
      apply Subtype.ext
      change insert α J'.1 ∩ (Δ \ {α}) = J'.1
      ext y
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h | h, -, hne⟩
        · exact absurd h hne
        · exact h
      · intro h
        exact ⟨Or.inr h, J'.2 h, fun e => hαJ' (e ▸ h)⟩
    refine ⟨B₁ + B₂, add_nonneg hB₁0 hB₂0, fun x hx b hb ϖ hϖ R' s hR' hs => ?_⟩
    have hαJ : α ∉ J.1 := fun h => hαJ' (hJJ' h)
    have e1 := hB₁ x hx b hb ϖ hϖ R' s hR' hs
    have e2 := hB₂ x hx b hb ϖ hϖ R' s hR' (hs α hαΔ hαJ)
    have hsplit : evaluate F G (f x).val (positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ) -
          𝓕.constantTerm J' (evaluate F G (f x).val) (positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ) =
        (evaluate F G (f x).val (positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ) -
          𝓕.constantTerm Jp (evaluate F G (f x).val) (positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ)) +
        𝓕.constantTermStep Jp α (evaluate F G (f x).val)
          (positiveMap F G 𝓕.T 𝓕.i T₀ j b * ϖ) := by
      simp only [constantTermStep, Pi.sub_apply, hrem]
      ring
    rw [hsplit]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add e1 e2
      _ = _ := by ring

end DerivativeFamily

section Assembly

open StandardParabolicFamily PositiveRealTorus AdelicSiegelFactors RestrictionSplitCentre
  MeasureTheory

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G

/-- Constant terms along equal closed subgroups agree. -/
theorem subgroupConstantTerm_eq_of_eq {U : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine U.X.left] (j₁ j₂ : U ⟶ G) (h : j₁ = j₂) [IsClosedImmersion j₁.hom.hom.left]
    [IsClosedImmersion j₂.hom.hom.left] (f : A → ℂ) :
    subgroupConstantTerm F j₁ f = subgroupConstantTerm F j₂ f := by
  subst h
  rfl

/-- If `z` is central and `f (z y) = c f(y)` for all `y`, the constant term along any closed
subgroup has the same covariance. -/
theorem subgroupConstantTerm_central_mul {U : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine U.X.left] (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left] (f : A → ℂ) {z : A}
    (hz : ∀ y, Commute z y) {c : ℂ} (hf : ∀ y, f (z * y) = c * f y) (g : A) :
    subgroupConstantTerm F j f (z * g) = c * subgroupConstantTerm F j f g := by
  unfold subgroupConstantTerm
  rw [← integral_const_mul]
  congr 1
  funext q
  rw [← mul_assoc, ← (hz _).eq, mul_assoc, hf]

/-- On a group `G(𝔸)` with one point every constant term along a standard parabolic is the
function itself. -/
theorem constantTerm_eq_of_subsingleton [IsAffineHom G.X.hom] [Subsingleton A]
    (𝓕 : StandardParabolicFamily F G) (Q : StandardIndex F G 𝓕.i 𝓕.ν) (φ : A → ℂ) (y : A) :
    𝓕.constantTerm Q φ y = φ y := by
  let := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let := 𝓕.compactSpace_radicalRationalQuotient Q
  let : IsProbabilityMeasure (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G
      (SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q))) :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G _
  have h : ∀ q : AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q)),
      φ (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (𝓕.iU Q ≫ 𝓕.p Q))) : A) * y) = φ y :=
    fun q => congrArg φ (Subsingleton.elim _ _)
  unfold StandardParabolicFamily.constantTerm subgroupConstantTerm
  simp only [h]
  simp

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [NumberField F] in
/-- The pairing of an imaginary parameter `i x` with a real functional `y` is `i ⟨x, y⟩`. -/
theorem complexParameterPairing_imaginaryParameter {H : GroupScheme (Spec (CommRingCat.of F))}
    (x : RealCharacterParameter F H) (y : RealCharacterDual F H) :
    complexParameterPairing F H (imaginaryParameter F H x) y =
      Complex.I * (realParameterPairing F H x y : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    change complexParameterPairing F H (((r : ℂ) * Complex.I) ⊗ₜ[ℤ] χ) y = _
    simp only [complexParameterPairing_tmul, realParameterPairing_tmul, Complex.ofReal_mul]
    ring
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', Complex.ofReal_add, mul_add]

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Imaginary parameters give characters of modulus one. -/
theorem norm_parameterPower_imaginaryParameter {H : GroupScheme (Spec (CommRingCat.of F))}
    (x : RealCharacterParameter F H) (g : AdelicGroupPoints F H) :
    ‖parameterPower F H (imaginaryParameter F H x) g‖ = 1 := by
  rw [parameterPower, complexParameterPairing_imaginaryParameter, Complex.norm_exp]
  simp [Complex.mul_re]

end Assembly

end ConstantTermDecay

/-- `EisensteinConstantTermDecayStatement` follows from the uniform moderate growth of the
Eisenstein series on compact sets of unitary parameters and from the subunitary exponents of
their constant terms. -/
def EisensteinConstantTermDecayReductionStatement : Prop :=
  EisensteinUnitaryUniformGrowthStatement → EisensteinUnitaryExponentStatement →
    EisensteinConstantTermDecayStatement

open StandardParabolicFamily PositiveRealTorus AdelicSiegelFactors RestrictionSplitCentre
  ConstantTermDecay in
/-- **Delorme 2023, Lemma 3.1 for Eisenstein series, from uniform growth and exponents.** The
exponent of the conclusion is `2m`, where `m` is the order of the shift equations given by
`EisensteinUnitaryExponentStatement`. -/
theorem eisensteinConstantTermDecayReduction : EisensteinConstantTermDecayReductionStatement := by
  intro hgrowth hexp F _ _ G P M U A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho
    hsmooth hcalc φ hKmax hrho hφ E D hD hmero hreg n e C hC T i ν T₀ j hset hK0 J hJ hJne
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : IsClosedImmersion (Standard.unipotentHom i ν J).hom.hom.left :=
    Standard.isClosedSubgroup_unipotentHom i ν J
  have : IsAffineHom (Standard.unipotentScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_unipotentHom i ν J).isAffineHom
  have : IsAffine (Standard.unipotentScheme i ν J).X.left :=
    isAffine_of_isAffineHom (Standard.unipotentScheme i ν J).X.hom
  obtain ⟨L, R, f, hL, hfE, hfam⟩ :=
    hgrowth F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ E D hD
      hmero hreg n e C hC
  obtain ⟨m, hm⟩ :=
    hexp F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ E D hD
      hmero hreg n e C hC
  refine ⟨2 * m, fun t Ω hΩ k => ?_⟩
  obtain ⟨hi, hν, -, -, -, -, -, ⟨D₀, d₀, t₀, -, ht₀, -⟩, -⟩ := id hset
  have hT₀ : IsSplitTorus T₀.toGrp := ht₀.isSplitSubtorus.1
  let 𝓕 : StandardParabolicFamily F G :=
    StandardParabolicFamily.ofMaximalSplitTorus hG i hi ν hν
  let : Fintype (simpleRelativeRoots 𝓕.i 𝓕.ν) :=
    (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  let Jidx : StandardIndex F G 𝓕.i 𝓕.ν := ⟨J, hJ⟩
  have hjJ : 𝓕.iU Jidx ≫ 𝓕.p Jidx = Standard.unipotentHom i ν J := by
    change Standard.unipotentToParabolic i ν J ≫ Standard.parabolicHom i ν J = _
    exact Standard.unipotentToParabolic_comp i ν J
  have hCT : ∀ ψ : AdelicGroupPoints F G → ℂ,
      subgroupConstantTerm F (Standard.unipotentHom i ν J) ψ = 𝓕.constantTerm Jidx ψ :=
    fun ψ => (subgroupConstantTerm_eq_of_eq _ _ hjJ ψ).symm
  -- covariance under `A_G`
  have hcov : ∀ v : RealCharacterParameter F P, ∀ z ∈ canonicalSubgroup F G,
      ∀ y : AdelicGroupPoints F G,
      ‖E (imaginaryParameter F P v) (z * y) -
          subgroupConstantTerm F (Standard.unipotentHom i ν J) (E (imaginaryParameter F P v))
            (z * y)‖ =
        ‖E (imaginaryParameter F P v) y -
          subgroupConstantTerm F (Standard.unipotentHom i ν J) (E (imaginaryParameter F P v))
            y‖ := by
    intro v z hz y
    rw [canonicalSubgroup_eq_imageSubgroup] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hid : IsClosedSubgroup (𝟙 G) := by
      change IsClosedImmersion (𝟙 G.X.left)
      infer_instance
    have hZG := isSplitComponent_canonicalComponent F G
    have hc₀ : IsCentral (canonicalComponent F G) :=
      IsCentralSplitTorus.isCentral (IsSplitComponent.isCentralSplitTorus hZG)
    let j₀ : (canonicalTorus F G).toGrp ⟶ M := r.intermediateCentralFactor (𝟙 G) hid (l ≫ p)
      (Category.comp_id _) (canonicalComponent F G) hc₀
    have hj₀ : j₀ ≫ l ≫ p = canonicalComponent F G :=
      r.intermediateCentralFactor_comp (𝟙 G) hid (l ≫ p) (Category.comp_id _)
        (canonicalComponent F G) hc₀
    have hZ := hZG.isCentralSplitTorus.isSplitSubtorus.1
    set c : ℂ := parameterPower F (canonicalTorus F G).toGrp
      (parameterRestrict (j₀ ≫ l) (imaginaryParameter F P v)) z' with hcdef
    have hc : ‖c‖ = 1 := by
      rw [hcdef, parameterPower_parameterRestrict]
      exact norm_parameterPower_imaginaryParameter v _
    have hEz : ∀ g, E (imaginaryParameter F P v)
        (pointMap F (canonicalTorus F G).toGrp G (Adeles F) (canonicalComponent F G) z' * g) =
          c * E (imaginaryParameter F P v) g := fun g =>
      eisensteinContinuation_splitCentre_mul hK r hA hT hG hφ.2.1 hmero hreg hZ hc₀ j₀ hj₀
        ⟨z', hz'⟩ (hD ⟨v, rfl⟩) g
    have hcomm : ∀ g, Commute
        (pointMap F (canonicalTorus F G).toGrp G (Adeles F) (canonicalComponent F G) z') g :=
      fun g =>
      positivePointMap_commute F G (canonicalTorus F G) (canonicalComponent F G) hc₀ ⟨z', hz'⟩ g
    rw [subgroupConstantTerm_central_mul _ _ hcomm hEz, hEz, ← mul_sub, norm_mul, hc, one_mul]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- `G(𝔸)` is a point
    subst hN
    have : Subsingleton (AdelicGL F 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    have hsub : Subsingleton (AdelicGroupPoints F G) :=
      (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective.subsingleton
    refine ⟨0, fun x _ z _ b _ ϖ _ R' s _ _ => ?_⟩
    rw [hCT, constantTerm_eq_of_subsingleton, sub_self, norm_zero]
    simp only [zero_mul, le_refl]
  · obtain ⟨Fr⟩ := StandardParabolicFamily.TorusFrame.nonempty (𝓕 := 𝓕)
    have hexp' : ∀ J' : StandardIndex F G 𝓕.i 𝓕.ν, ∀ x ∈ C,
        𝓕.HasSubunitaryShiftEquations J' m (𝓕.constantTerm J' (evaluate F G (f x).val)) :=
      fun J' x hx => by rw [hfE x hx]; exact hm 𝓕 J' x hx
    have hnorm : ∀ b : intrinsicSubgroup F T₀,
        positiveMap F G 𝓕.T 𝓕.i T₀ j b ∈ normOneSubgroup F G :=
      fun b => (hset.positiveNormOneMap F G T i ν T₀ j b).prop
    obtain ⟨B, -, hB⟩ := sub_constantTerm_bound rho hsmooth hcalc halfModulusRootProduct.{0} Fr
      hN f C L R m hL hfam hexp' j hT₀ hnorm Jidx t Ω hΩ k
    refine ⟨B, fun x hx z hz b hb ϖ hϖ R' s hR' hs => ?_⟩
    rw [mul_assoc z (positiveMap F G T i T₀ j b) ϖ, hcov (e x) z hz, hCT, ← hfE x hx]
    exact hB x hx b hb ϖ hϖ R' s hR' hs

end Langlands.Global
