import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthReductionStatement
import Langlands.Automorphic.GroupSchemeInfiniteTranslation
import Langlands.Automorphic.GroupSchemeManifoldSmooth
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Uniform growth of adelic automorphic forms from an elliptic estimate and a Casimir -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter Topology
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Word operators on a Lie group -/

namespace Langlands.Geometry.Manifold

section Words

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] [ChartedSpace E H] [Group H]
  [LieGroup 𝓘(ℝ, E) ∞ H] {n : ℕ}

theorem lieWordDerivative_one (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H) (φ : H → ℂ) :
    (lieWordDerivative X 1 : (H → ℂ) → H → ℂ) φ = φ := by
  rw [map_one]
  rfl

theorem lieWordDerivative_of_mul (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H) (i : Fin n)
    (w : FreeMonoid (Fin n)) (φ : H → ℂ) :
    (lieWordDerivative X (FreeMonoid.of i * w) : (H → ℂ) → H → ℂ) φ =
      groupDirectionalValue 𝓘(ℝ, E) (X i) ((lieWordDerivative X w : (H → ℂ) → H → ℂ) φ) := by
  rw [map_mul]
  rfl

/-- Word derivatives commute with left translation. -/
theorem lieWordDerivative_leftTranslation (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H)
    (w : FreeMonoid (Fin n)) (a : H) (φ : H → ℂ) :
    (lieWordDerivative X w : (H → ℂ) → H → ℂ) (fun x => φ (a * x)) =
      fun x => (lieWordDerivative X w : (H → ℂ) → H → ℂ) φ (a * x) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [lieWordDerivative_one]
  | of_mul i w ih =>
    rw [lieWordDerivative_of_mul, lieWordDerivative_of_mul, ih]
    funext x
    exact groupDirectionalValue_leftTranslation _ (X i) a _ x

/-- Word combinations commute with left translation. -/
theorem lieWordAction_leftTranslation (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H)
    (P : MonoidAlgebra ℂ (FreeMonoid (Fin n))) (a : H) (φ : H → ℂ) (x : H) :
    lieWordAction X P (fun y => φ (a * y)) x = lieWordAction X P φ (a * x) := by
  unfold lieWordAction
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, lieWordDerivative_leftTranslation]

end Words

end Langlands.Geometry.Manifold

/-! ## Homogeneous word combinations -/

namespace Langlands.Automorphic.UniformGrowthReduction

section Homogeneous

variable {α : Type*}

/-- Every word of the support has length `s`. -/
def IsHomogeneous (a : MonoidAlgebra ℂ (FreeMonoid α)) (s : ℕ) : Prop :=
  ∀ w ∈ a.coeff.support, w.length = s

theorem isHomogeneous_one : IsHomogeneous (1 : MonoidAlgebra ℂ (FreeMonoid α)) 0 := by
  intro w hw
  classical
  have hsub : (1 : MonoidAlgebra ℂ (FreeMonoid α)).coeff.support ⊆ {1} := by
    rw [MonoidAlgebra.one_def]
    exact Finsupp.support_single_subset
  have := Finset.mem_singleton.mp (hsub hw)
  subst this
  rfl

theorem IsHomogeneous.mul {a b : MonoidAlgebra ℂ (FreeMonoid α)} {s t : ℕ}
    (ha : IsHomogeneous a s) (hb : IsHomogeneous b t) : IsHomogeneous (a * b) (s + t) := by
  classical
  intro w hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_coeff_mul_subset a b hw)
  rw [FreeMonoid.length_mul, ha x hx, hb y hy]

theorem IsHomogeneous.pow {a : MonoidAlgebra ℂ (FreeMonoid α)} {s : ℕ}
    (ha : IsHomogeneous a s) (k : ℕ) : IsHomogeneous (a ^ k) (s * k) := by
  induction k with
  | zero => simpa using isHomogeneous_one
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ]
    exact ih.mul ha

theorem IsHomogeneous.smul {a : MonoidAlgebra ℂ (FreeMonoid α)} {s : ℕ}
    (ha : IsHomogeneous a s) (c : ℂ) : IsHomogeneous (c • a) s := by
  intro w hw
  rw [MonoidAlgebra.coeff_smul] at hw
  exact ha w (Finsupp.support_smul hw)

/-- Every word of the support has length less than `r`. -/
def IsLower (a : MonoidAlgebra ℂ (FreeMonoid α)) (r : ℕ) : Prop :=
  ∀ w ∈ a.coeff.support, w.length < r

theorem isLower_sum {Idx : Type*} (s : Finset Idx) (a : Idx → MonoidAlgebra ℂ (FreeMonoid α)) (r : ℕ)
    (h : ∀ i ∈ s, IsLower (a i) r) : IsLower (∑ i ∈ s, a i) r := by
  classical
  intro w hw
  rw [MonoidAlgebra.coeff_sum] at hw
  obtain ⟨i, hi, hwi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw)
  exact h i hi w hwi

theorem IsHomogeneous.isLower {a : MonoidAlgebra ℂ (FreeMonoid α)} {s r : ℕ}
    (ha : IsHomogeneous a s) (hsr : s < r) : IsLower a r :=
  fun w hw => (ha w hw).symm ▸ hsr

end Homogeneous

/-! ## Two finite-dimensional lemmas -/

section FiniteDimensional

/-- A vector which is the pointwise derivative at `0` of a curve in a finite-dimensional subspace
of a space of functions lies in that subspace. -/
theorem mem_of_hasDerivAt {X V : Type*} [AddCommGroup V] [Module ℂ V]
    (ev : V →ₗ[ℂ] (X → ℂ)) (hev : Function.Injective ev) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (c : ℝ → V) (hc : ∀ t, c t ∈ W) (u : V)
    (hd : ∀ p, HasDerivAt (fun t => ev (c t) p) (ev u p) 0) : u ∈ W := by
  let W' : Submodule ℂ (X → ℂ) := W.map ev
  have hclosed : IsClosed (W' : Set (X → ℂ)) := Submodule.closed_of_finiteDimensional W'
  have hmem : ∀ t : ℝ, ((t : ℂ)⁻¹ • (ev (c t) - ev (c 0))) ∈ W' := fun t =>
    W'.smul_mem _ (W'.sub_mem (Submodule.mem_map_of_mem (hc t)) (Submodule.mem_map_of_mem (hc 0)))
  have htend : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (ev (c t) - ev (c 0))) (𝓝[≠] 0) (𝓝 (ev u)) := by
    rw [tendsto_pi_nhds]
    intro p
    have h := (hasDerivAt_iff_tendsto_slope.mp (hd p))
    refine h.congr' (Eventually.of_forall fun t => ?_)
    simp only [slope_def_module, sub_zero, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Complex.real_smul, Complex.ofReal_inv]
  have hcl : ev u ∈ closure (W' : Set (X → ℂ)) :=
    mem_closure_of_tendsto htend (Eventually.of_forall hmem)
  rw [hclosed.closure_eq] at hcl
  obtain ⟨v, hv, hvu⟩ := Submodule.mem_map.mp hcl
  rwa [← hev hvu]

theorem restrict_aeval_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (U : Submodule ℂ V) (hU : ∀ u ∈ U, T u ∈ U) (q : Polynomial ℂ)
    (u : U) :
    ((Polynomial.aeval (T.restrict hU) q u : U) : V) = Polynomial.aeval T q (u : V) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul]
    congr 1
    induction k generalizing u with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl

/-- A vector in a finite-dimensional `T`-stable subspace is killed by a monic polynomial in
`T`. -/
theorem exists_monic_aeval_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (U : Submodule ℂ V) [FiniteDimensional ℂ U]
    (hU : ∀ u ∈ U, T u ∈ U) (f : V) (hf : f ∈ U) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval T p f = 0 := by
  let S : Module.End ℂ U := T.restrict hU
  refine ⟨minpoly ℂ S, minpoly.monic (Algebra.IsIntegral.isIntegral S), ?_⟩
  have h := restrict_aeval_apply T U hU (minpoly ℂ S) ⟨f, hf⟩
  rw [minpoly.aeval] at h
  rw [← h]
  rfl


/-- A finite-dimensional space of vectors that are all finite for a monoid action `ρ` lies in a
finite-dimensional `ρ`-stable subspace which is also stable under every operator of a family that
commutes with `ρ` and preserves the original space. -/
theorem exists_stable_finite {V : Type*} [AddCommGroup V] [Module ℂ V] {M : Type*} [Monoid M]
    (ρ : Representation ℂ M V) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hW : ∀ w ∈ W, Langlands.FiniteVectors.IsFiniteVector ρ w)
    (D : Set (Module.End ℂ V)) (hD : ∀ T ∈ D, ∀ w ∈ W, T w ∈ W)
    (hcomm : ∀ T ∈ D, ∀ m, T * ρ m = ρ m * T) :
    ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ W ≤ U ∧ (∀ m, ∀ u ∈ U, ρ m u ∈ U) ∧
      (∀ T ∈ D, ∀ u ∈ U, T u ∈ U) := by
  let b := Module.finBasis ℂ W
  let U : Submodule ℂ V := ⨆ l, Langlands.FiniteVectors.orbitSpan ρ (b l : V)
  have hfin : ∀ l, FiniteDimensional ℂ (Langlands.FiniteVectors.orbitSpan ρ (b l : V)) :=
    fun l => hW _ (b l).property
  have hstab : ∀ m, ∀ u ∈ U, ρ m u ∈ U := by
    intro m u hu
    refine Submodule.iSup_induction _ (motive := fun u => ρ m u ∈ U) hu ?_ ?_ ?_
    · intro l v hv
      exact (le_iSup (fun l => Langlands.FiniteVectors.orbitSpan ρ (b l : V)) l)
        ((Langlands.FiniteVectors.orbitSubrepresentation ρ (b l : V)).apply_mem_toSubmodule m hv)
    · simp
    · intro x y hx hy
      rw [map_add]
      exact U.add_mem hx hy
  have hbU : ∀ l, (b l : V) ∈ U := fun l =>
    (le_iSup (fun l => Langlands.FiniteVectors.orbitSpan ρ (b l : V)) l)
      (Langlands.FiniteVectors.self_mem_orbitSpan ρ (b l : V))
  have hWU : W ≤ U := by
    intro w hw
    have hsum := b.sum_repr ⟨w, hw⟩
    have hw' : w = ∑ l, (b.repr ⟨w, hw⟩ l) • (b l : V) := by
      have := congrArg (fun x : W => (x : V)) hsum
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
    rw [hw']
    exact U.sum_mem fun l _ => U.smul_mem _ (hbU l)
  refine ⟨U, inferInstance, hWU, hstab, ?_⟩
  intro T hT u hu
  refine Submodule.iSup_induction _ (motive := fun u => T u ∈ U) hu ?_ ?_ ?_
  · intro l v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      have h := congrArg (fun S : Module.End ℂ V => S (b l : V)) (hcomm T hT m)
      simp only [Module.End.mul_apply] at h
      rw [h]
      exact hstab m _ (hWU (hD T hT _ (b l).property))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact U.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact U.smul_mem c hx
  · simp
  · intro x y hx hy
    rw [map_add]
    exact U.add_mem hx hy

end FiniteDimensional

end Langlands.Automorphic.UniformGrowthReduction

/-! ## Word combinations on the actual infinite adelic points -/

namespace Langlands.Geometry.Manifold

section WordAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] [ChartedSpace E H] [Group H]
  [LieGroup 𝓘(ℝ, E) ∞ H] {n : ℕ}

theorem lieWordAction_zero (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H) (φ : H → ℂ) :
    lieWordAction X 0 φ = 0 := by
  simp [lieWordAction]

theorem lieWordAction_add (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H)
    (P Q : MonoidAlgebra ℂ (FreeMonoid (Fin n))) (φ : H → ℂ) :
    lieWordAction X (P + Q) φ = lieWordAction X P φ + lieWordAction X Q φ := by
  unfold lieWordAction
  rw [MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem lieWordAction_single (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H)
    (w : FreeMonoid (Fin n)) (c : ℂ) (φ : H → ℂ) :
    lieWordAction X (MonoidAlgebra.single w c) φ =
      c • (lieWordDerivative X w : (H → ℂ) → H → ℂ) φ := by
  unfold lieWordAction
  rw [MonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (zero_smul _ _)

end WordAlgebra

end Langlands.Geometry.Manifold

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.Geometry.Manifold
open Langlands.Automorphic.UniformGrowthReduction

section Adelic

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local instance reductionAddCommGroup : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- The algebra homomorphism from word combinations to the actual enveloping algebra: the letter
`i` goes to `ι (1 ⊗ X i)`. -/
def wordHom {n : ℕ} (X : Fin n → smoothModel F d) :
    MonoidAlgebra ℂ (FreeMonoid (Fin n)) →ₐ[ℂ] AdelicEnvelopingAlgebra F G hsmooth := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  exact MonoidAlgebra.lift ℂ (AdelicEnvelopingAlgebra F G hsmooth) (FreeMonoid (Fin n))
    (FreeMonoid.lift fun i => UniversalEnvelopingAlgebra.ι ℂ
      (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
      ((1 : ℂ) ⊗ₜ[ℝ] X i))

theorem wordHom_of {n : ℕ} (X : Fin n → smoothModel F d) (i : Fin n) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    wordHom F G hsmooth X (MonoidAlgebra.single (FreeMonoid.of i) 1) =
      UniversalEnvelopingAlgebra.ι ℂ
        (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
        ((1 : ℂ) ⊗ₜ[ℝ] X i) := by
  simp only [wordHom, MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_eval_of]

/-- The slices of a word derivative are the word derivatives of the slices. -/
theorem slice_wordHom_single (hcalc : AdelicDifferentialCommutator F G hsmooth) {n : ℕ}
    (X : Fin n → smoothModel F d) (w : FreeMonoid (Fin n)) (b : FiniteAdelicGroupPoints F G)
    (f : FinitePlotSmoothRationalFunctions F G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    (finitePlotSmoothSlice F G b (adelicEnvelopingAction F G hsmooth hcalc
        (wordHom F G hsmooth X (MonoidAlgebra.single w 1)) f)).val =
      (lieWordDerivative (E := smoothModel F d) X w :
        (InfiniteAdelicGroupPoints F G → ℂ) → InfiniteAdelicGroupPoints F G → ℂ)
        (finitePlotSmoothSlice F G b f).val := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  induction w using FreeMonoid.inductionOn' generalizing f with
  | one =>
    rw [← MonoidAlgebra.one_def, map_one, map_one, Module.End.one_apply, lieWordDerivative_one]
  | of_mul i w ih =>
    have hsplit : (MonoidAlgebra.single (FreeMonoid.of i * w) (1 : ℂ)) =
        MonoidAlgebra.single (FreeMonoid.of i) 1 * MonoidAlgebra.single w 1 := by
      rw [MonoidAlgebra.single_mul_single, mul_one]
    rw [hsplit, map_mul, map_mul, Module.End.mul_apply, wordHom_of, lieWordDerivative_of_mul,
      ← ih]
    have hgen := finitePlotSmoothEnvelopingAction_real_generator F G hsmooth hcalc (X i)
    have hslice := finitePlotSmoothSlice_differentialAction F G hsmooth (X i)
      (adelicEnvelopingAction F G hsmooth hcalc (wordHom F G hsmooth X
        (MonoidAlgebra.single w 1)) f) b
    change (finitePlotSmoothSlice F G b (finitePlotSmoothEnvelopingAction F G hsmooth hcalc
      (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X i)) _)).val = _
    rw [hgen, hslice]
    rfl

/-- The slices of the action of a word combination are given by `lieWordAction`. -/
theorem slice_wordHom (hcalc : AdelicDifferentialCommutator F G hsmooth) {n : ℕ}
    (X : Fin n → smoothModel F d) (P : MonoidAlgebra ℂ (FreeMonoid (Fin n)))
    (b : FiniteAdelicGroupPoints F G) (f : FinitePlotSmoothRationalFunctions F G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    (finitePlotSmoothSlice F G b (adelicEnvelopingAction F G hsmooth hcalc
        (wordHom F G hsmooth X P) f)).val =
      lieWordAction (E := smoothModel F d) X P (finitePlotSmoothSlice F G b f).val := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  induction P using MonoidAlgebra.induction_linear with
  | zero =>
    rw [map_zero, map_zero, LinearMap.zero_apply, map_zero, lieWordAction_zero]
    rfl
  | add P Q hP hQ =>
    rw [map_add, map_add, LinearMap.add_apply, map_add, lieWordAction_add, ← hP, ← hQ]
    rfl
  | single w c =>
    have hs : MonoidAlgebra.single w c = c • MonoidAlgebra.single w (1 : ℂ) := by
      rw [MonoidAlgebra.smul_single', mul_one]
    rw [lieWordAction_single, ← slice_wordHom_single F G hsmooth hcalc X w b f, hs, map_smul,
      map_smul, LinearMap.smul_apply, map_smul]
    rfl


/-- If the tangent vectors `X i` span, every element of the actual enveloping algebra is the image
of a word combination. -/
theorem wordHom_surjective {n : ℕ} (X : Fin n → smoothModel F d) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    Submodule.span ℝ (Set.range X) = ⊤ → Function.Surjective (wordHom F G hsmooth X) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  intro hX
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  have hgen : ∀ Y : smoothModel F d, ∀ z : ℂ, ∃ P, wordHom F G hsmooth X P =
      UniversalEnvelopingAlgebra.ι ℂ
        (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
        (z ⊗ₜ[ℝ] Y) := by
    intro Y
    have hY : Y ∈ Submodule.span ℝ (Set.range X) := hX ▸ Submodule.mem_top
    induction hY using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro z
      refine ⟨z • MonoidAlgebra.single (FreeMonoid.of i) 1, ?_⟩
      rw [map_smul, wordHom_of, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | zero =>
      intro z
      exact ⟨0, by rw [map_zero, TensorProduct.tmul_zero, map_zero]⟩
    | add x y _ _ hx hy =>
      intro z
      obtain ⟨P, hP⟩ := hx z
      obtain ⟨Q, hQ⟩ := hy z
      exact ⟨P + Q, by rw [map_add, hP, hQ, TensorProduct.tmul_add, map_add]⟩
    | smul r x _ hx =>
      intro z
      obtain ⟨P, hP⟩ := hx (r • z)
      exact ⟨P, by rw [hP, TensorProduct.tmul_smul, TensorProduct.smul_tmul']⟩
  intro a
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ
      (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))) a
  change ∃ P, wordHom F G hsmooth X P = UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    exact ⟨algebraMap ℂ _ z, by rw [AlgHom.commutes, AlgHom.commutes]⟩
  | «ι» Z =>
    change ∃ P, wordHom F G hsmooth X P = UniversalEnvelopingAlgebra.ι ℂ Z
    induction Z using TensorProduct.inductionOn with
    | tmul z Y => exact hgen Y z
    | add U V hU hV =>
      obtain ⟨P, hP⟩ := hU
      obtain ⟨Q, hQ⟩ := hV
      exact ⟨P + Q, by rw [map_add, hP, hQ, map_add]⟩
  | mul x y hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P * Q, by rw [map_mul, hP, hQ, map_mul]⟩
  | add x y hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P + Q, by rw [map_add, hP, hQ, map_add]⟩

/-- A derivative along the velocity of a smooth curve in `Kinf` keeps a `Kinf`-finite function
inside its finite-dimensional `Kinf`-orbit span. -/
theorem differentialAction_mem_orbitSpan (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (f : FinitePlotSmoothRationalFunctions F G)
    [FiniteDimensional ℂ (Langlands.FiniteVectors.orbitSpan
      (finitePlotSmoothInfiniteSubgroupAction F G Kinf) f)]
    (X : smoothModel F d) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    (∃ c : ℝ → InfiniteAdelicGroupPoints F G,
      ContMDiff 𝓘(ℝ) 𝓘(ℝ, smoothModel F d) ∞ c ∧ c 0 = 1 ∧ (∀ t : ℝ, c t ∈ Kinf) ∧
        mfderiv 𝓘(ℝ) 𝓘(ℝ, smoothModel F d) c 0 1 = X) →
    ∀ w ∈ Langlands.FiniteVectors.orbitSpan (finitePlotSmoothInfiniteSubgroupAction F G Kinf) f,
      finitePlotSmoothDifferentialAction F G hsmooth X w ∈
        Langlands.FiniteVectors.orbitSpan (finitePlotSmoothInfiniteSubgroupAction F G Kinf) f := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  rintro ⟨c, hc, hc0, hcK, hcX⟩ w hw
  let ρK := finitePlotSmoothInfiniteSubgroupAction F G Kinf
  let ev : FinitePlotSmoothRationalFunctions F G →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
    { toFun := fun g p => evaluate F G g.val p
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    intro g h hgh
    apply finitePlotSmoothSlice_injective F G
    funext b
    apply Subtype.ext
    funext a
    exact congrFun hgh (AdelicGroupPoints.pair F G a b)
  refine mem_of_hasDerivAt ev hev (Langlands.FiniteVectors.orbitSpan ρK f)
    (fun t => ρK ⟨c t, hcK t⟩ w)
    (fun t => (Langlands.FiniteVectors.orbitSubrepresentation ρK f).apply_mem_toSubmodule _ hw)
    _ ?_
  intro p
  obtain ⟨a, b, rfl⟩ : ∃ a b, p = AdelicGroupPoints.pair F G a b :=
    ⟨_, _, (AdelicGroupPoints.pair_projections F G p).symm⟩
  have hψ : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (finitePlotSmoothSlice F G b w).val :=
    (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (finitePlotSmoothSlice F G b w).property
  let g : InfiniteAdelicGroupPoints F G → ℂ := fun h => (finitePlotSmoothSlice F G b w).val (a * h)
  have hg : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ g :=
    hψ.comp (contMDiff_const.mul contMDiff_id)
  have hfun : (fun t => ev (ρK ⟨c t, hcK t⟩ w) (AdelicGroupPoints.pair F G a b)) = g ∘ c := by
    funext t
    change evaluate F G w.val (AdelicGroupPoints.pair F G a b *
      AdelicGroupPoints.ofInfinite F G (c t)) = _
    rw [AdelicGroupPoints.ofInfinite_eq_pair, AdelicGroupPoints.pair_mul, mul_one]
    rfl
  rw [hfun]
  have hgc : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) ∞ (g ∘ c) := hg.comp hc
  have hdiff : HasDerivAt (g ∘ c) (fderiv ℝ (g ∘ c) 0 1) 0 :=
    ((contMDiff_iff_contDiff.mp hgc).differentiable (by simp) 0).hasFDerivAt.hasDerivAt
  have h1 : mvfderiv 𝓘(ℝ) (g ∘ c) 0 = fderiv ℝ (g ∘ c) 0 := mvfderiv_eq_fderiv
  have heq : fderiv ℝ (g ∘ c) 0 1 =
      ev (finitePlotSmoothDifferentialAction F G hsmooth X w) (AdelicGroupPoints.pair F G a b) := by
    rw [← h1]
    refine (mvfderiv_comp_apply_of_eq 0 (hg.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp)) hc0 1).trans ?_
    refine (congrArg (mvfderiv 𝓘(ℝ, smoothModel F d) g 1) hcX).trans ?_
    exact (evaluate_finitePlotSmoothDifferentialAction F G hsmooth X w a b).symm
  rw [← heq]
  exact hdiff

end Adelic


/-- The interior estimate for elliptic left-invariant word operators and the adapted Casimir
element imply uniform moderate growth of every actual adelic automorphic form. -/
theorem adelicAutomorphicUniformGrowthReduction :
    AdelicAutomorphicUniformGrowthReductionStatement.{u} := by
  intro h12 h3 F _ _ G _ Kinf N d rho hsmooth hG _hrho hK hN f hf
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨n, X, J, hspan, hcurve, hcent⟩ := h3 F G Kinf hsmooth hG hK
  obtain ⟨hKfin, hZfin, hgrowth⟩ := hf
  obtain ⟨Cf, hCf, e, hfe⟩ := (hasAdelicModerateGrowth_iff F G rho hN f.val).mp hgrowth
  let hcalc := adelicDifferentialCommutator_of_smooth F G hsmooth
  let Act := adelicEnvelopingAction F G hsmooth hcalc
  let ρK := finitePlotSmoothInfiniteSubgroupAction F G Kinf
  let W := Langlands.FiniteVectors.orbitSpan ρK f
  haveI hWfin : FiniteDimensional ℂ W := hKfin
  let ρZ := (adelicCenterAction F G hsmooth hcalc).toMonoidHom
  -- every vector of the `Kinf`-orbit span is centre-finite
  have hWZ : ∀ w ∈ W, Langlands.FiniteVectors.IsFiniteVector ρZ w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact IsAdelicCenterFinite.infiniteRightAction F G hsmooth hcalc hZfin k.val
    | zero => exact Langlands.FiniteVectors.isFiniteVector_zero _
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.smul c
  let ιX : Fin n → AdelicEnvelopingAlgebra F G hsmooth := fun i =>
    UniversalEnvelopingAlgebra.ι ℂ
      (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
      ((1 : ℂ) ⊗ₜ[ℝ] X i)
  have hgen : ∀ i, Act (ιX i) = finitePlotSmoothDifferentialAction F G hsmooth (X i) :=
    fun i => finitePlotSmoothEnvelopingAction_real_generator F G hsmooth hcalc (X i)
  let D : Set (Module.End ℂ (FinitePlotSmoothRationalFunctions F G)) :=
    {T | ∃ j ∈ J, T = Act (ιX j)}
  have hD : ∀ T ∈ D, ∀ w ∈ W, T w ∈ W := by
    rintro T ⟨j, hj, rfl⟩ w hw
    rw [hgen]
    exact differentialAction_mem_orbitSpan F G hsmooth Kinf f (X j) (hcurve j hj) w hw
  have hcomm : ∀ T ∈ D, ∀ z, T * ρZ z = ρZ z * T := by
    rintro T ⟨j, hj, rfl⟩ z
    change Act (ιX j) * Act z.val = Act z.val * Act (ιX j)
    rw [← map_mul, ← map_mul, Subalgebra.mem_center_iff.mp z.property (ιX j)]
  obtain ⟨U, hUfin, hWU, hUZ, hUD⟩ :=
    Langlands.Automorphic.UniformGrowthReduction.exists_stable_finite ρZ W hWZ D hD hcomm
  haveI := hUfin
  -- the sum of squares preserves `U`
  let Ωe : AdelicEnvelopingAlgebra F G hsmooth := ∑ i, ιX i ^ 2
  let zΩ : AdelicEnvelopingCenter F G hsmooth := ⟨_, hcent⟩
  have hΩ : Ωe = zΩ.val + (2 : ℂ) • ∑ j ∈ J, ιX j ^ 2 := by
    change Ωe = (∑ i, ιX i ^ 2 - (2 : ℂ) • ∑ j ∈ J, ιX j ^ 2) + (2 : ℂ) • ∑ j ∈ J, ιX j ^ 2
    rw [sub_add_cancel]
  have hTU : ∀ u ∈ U, Act Ωe u ∈ U := by
    intro u hu
    rw [hΩ, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_sum,
      LinearMap.sum_apply]
    refine U.add_mem (hUZ zΩ u hu) (U.smul_mem _ (U.sum_mem fun j hj => ?_))
    rw [map_pow, pow_two, Module.End.mul_apply]
    exact hUD _ ⟨j, hj, rfl⟩ _ (hUD _ ⟨j, hj, rfl⟩ u hu)
  obtain ⟨p, hpm, hp⟩ := Langlands.Automorphic.UniformGrowthReduction.exists_monic_aeval_eq_zero
    (Act Ωe) U hTU f (hWU (Langlands.FiniteVectors.self_mem_orbitSpan ρK f))
  -- the corresponding word combinations
  let wsq : MonoidAlgebra ℂ (FreeMonoid (Fin n)) :=
    ∑ i, MonoidAlgebra.single (FreeMonoid.of i * FreeMonoid.of i) 1
  have hΨsq : wordHom F G hsmooth X wsq = Ωe := by
    simp only [wsq, Ωe, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_one (1 : ℂ), ← MonoidAlgebra.single_mul_single, map_mul, wordHom_of, pow_two]
  have hsqhom : Langlands.Automorphic.UniformGrowthReduction.IsHomogeneous wsq 2 := by
    classical
    intro w hw
    rw [MonoidAlgebra.coeff_sum] at hw
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw)
    rw [MonoidAlgebra.coeff_single] at hwi
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hwi), FreeMonoid.length_mul,
      FreeMonoid.length_of]
  let m := p.natDegree
  let Ptop : MonoidAlgebra ℂ (FreeMonoid (Fin n)) := wsq ^ m
  let Plow : MonoidAlgebra ℂ (FreeMonoid (Fin n)) := ∑ k ∈ Finset.range m, p.coeff k • wsq ^ k
  have hPsum : Ptop + Plow = Polynomial.aeval wsq p := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, one_smul,
      add_comm]
  have hkill : Act (wordHom F G hsmooth X (Ptop + Plow)) f = 0 := by
    rw [hPsum, ← Polynomial.aeval_algHom_apply, hΨsq, ← Polynomial.aeval_algHom_apply]
    exact hp
  have htop : ∀ w ∈ Ptop.coeff.support, w.length = 2 * m := hsqhom.pow m
  have hlow : ∀ w ∈ Plow.coeff.support, w.length < 2 * m :=
    Langlands.Automorphic.UniformGrowthReduction.isLower_sum _ _ _ fun k hk =>
      ((hsqhom.pow k).smul _).isLower (by have := Finset.mem_range.mp hk; omega)
  have hsym : ∀ ξ : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →ₗ[ℝ] ℝ,
      ξ ≠ 0 → lieWordSymbol X ξ Ptop ≠ 0 := by
    intro ξ hξ
    have hω : lieWordSymbol X ξ wsq = ((∑ i, ξ (X i) ^ 2 : ℝ) : ℂ) := by
      simp only [wsq, map_sum, lieWordSymbol, MonoidAlgebra.lift_single, one_smul, map_mul,
        FreeMonoid.lift_eval_of]
      push_cast
      simp only [pow_two]
    have hex : ∃ i, ξ (X i) ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      apply hξ
      have hle : Submodule.span ℝ (Set.range X) ≤ LinearMap.ker ξ := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hne i
      rw [hspan, top_le_iff, LinearMap.ker_eq_top] at hle
      exact hle
    obtain ⟨i, hi⟩ := hex
    have hpos : 0 < ∑ i, ξ (X i) ^ 2 :=
      Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩
    rw [map_pow, hω]
    exact pow_ne_zero _ (by exact_mod_cast hpos.ne')
  -- the uniform bound
  rw [hasAdelicUniformModerateGrowth_iff F G rho hsmooth hcalc hN]
  refine ⟨e, fun a => ?_⟩
  obtain ⟨Q, rfl⟩ := wordHom_surjective F G hsmooth X hspan a
  obtain ⟨V, C, hV, hC, hest⟩ := h12 (smoothModel F d) (InfiniteAdelicGroupPoints F G) n (2 * m)
    X Ptop Plow htop hlow hsym Q
  have hcont : Continuous fun y : InfiniteAdelicGroupPoints F G =>
      RepresentationGrowth.adelicHeight F G rho (AdelicGroupPoints.ofInfinite F G y) :=
    (RepresentationGrowth.continuous_adelicHeight F G rho hN).comp
      (AdelicGroupPoints.ofInfinite F G).continuous
  obtain ⟨B, hB⟩ := hV.bddAbove_image hcont.continuousOn
  let B' := max B 1
  have hB'0 : 0 ≤ B' := zero_le_one.trans (le_max_right _ _)
  refine ⟨C * (Cf * B' ^ e), by positivity, fun g => ?_⟩
  obtain ⟨a', b, rfl⟩ : ∃ a' b, g = AdelicGroupPoints.pair F G a' b :=
    ⟨_, _, (AdelicGroupPoints.pair_projections F G g).symm⟩
  have hH0 : ∀ x, 0 ≤ RepresentationGrowth.adelicHeight F G rho x := fun x =>
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN x)
  let ψ := (finitePlotSmoothSlice F G b f).val
  have hψ : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ ψ :=
    (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (finitePlotSmoothSlice F G b f).property
  let φ : InfiniteAdelicGroupPoints F G → ℂ := fun y => ψ (a' * y)
  have hφ : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ φ :=
    hψ.comp (contMDiff_const.mul contMDiff_id)
  have heqn : ∀ x, lieWordAction X (Ptop + Plow) φ x = 0 := by
    intro x
    rw [lieWordAction_leftTranslation, ← slice_wordHom F G hsmooth hcalc X (Ptop + Plow) b f]
    change (finitePlotSmoothSlice F G b (Act (wordHom F G hsmooth X (Ptop + Plow)) f)).val _ = 0
    rw [hkill, map_zero]
    rfl
  have hbound : ∀ y ∈ V, ‖φ y‖ ≤
      Cf * B' ^ e * RepresentationGrowth.adelicHeight F G rho (AdelicGroupPoints.pair F G a' b) ^ e := by
    intro y hy
    have h1 : φ y = evaluate F G f.val
        (AdelicGroupPoints.pair F G a' b * AdelicGroupPoints.ofInfinite F G y) := by
      rw [AdelicGroupPoints.ofInfinite_eq_pair, AdelicGroupPoints.pair_mul, mul_one]
      rfl
    have hy' : RepresentationGrowth.adelicHeight F G rho (AdelicGroupPoints.ofInfinite F G y) ≤ B' :=
      le_max_of_le_left (hB ⟨y, hy, rfl⟩)
    rw [h1]
    calc ‖evaluate F G f.val
          (AdelicGroupPoints.pair F G a' b * AdelicGroupPoints.ofInfinite F G y)‖
        ≤ Cf * RepresentationGrowth.adelicHeight F G rho
            (AdelicGroupPoints.pair F G a' b * AdelicGroupPoints.ofInfinite F G y) ^ e := hfe _
      _ ≤ Cf * (RepresentationGrowth.adelicHeight F G rho (AdelicGroupPoints.pair F G a' b) *
            RepresentationGrowth.adelicHeight F G rho (AdelicGroupPoints.ofInfinite F G y)) ^ e :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hH0 _)
            (RepresentationGrowth.adelicHeight_mul_le F G rho hN _ _) e) hCf
      _ ≤ Cf * (RepresentationGrowth.adelicHeight F G rho (AdelicGroupPoints.pair F G a' b) *
            B') ^ e :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (hH0 _) (hH0 _))
            (mul_le_mul_of_nonneg_left hy' (hH0 _)) e) hCf
      _ = Cf * B' ^ e * RepresentationGrowth.adelicHeight F G rho
            (AdelicGroupPoints.pair F G a' b) ^ e := by ring
  have hval : evaluate F G (Act (wordHom F G hsmooth X Q) f).val
      (AdelicGroupPoints.pair F G a' b) = lieWordAction X Q φ 1 := by
    rw [lieWordAction_leftTranslation, mul_one, ← slice_wordHom F G hsmooth hcalc X Q b f]
    rfl
  calc ‖evaluate F G (adelicEnvelopingAction F G hsmooth
          (adelicDifferentialCommutator_of_smooth F G hsmooth) (wordHom F G hsmooth X Q) f).val
          (AdelicGroupPoints.pair F G a' b)‖
      = ‖lieWordAction X Q φ 1‖ := by rw [← hval]
    _ ≤ C * (Cf * B' ^ e * RepresentationGrowth.adelicHeight F G rho
          (AdelicGroupPoints.pair F G a' b) ^ e) := hest φ hφ heqn _ hbound
    _ = C * (Cf * B' ^ e) * RepresentationGrowth.adelicHeight F G rho
          (AdelicGroupPoints.pair F G a' b) ^ e := by ring

end Langlands.Automorphic.GroupSchemeFunctions
