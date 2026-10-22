import Langlands.Global.AdelicFunctoriality.Extension
import Mathlib.NumberTheory.NumberField.AdeleRing

/-! # Products of actual local norms on adeles -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField RestrictedProduct

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- Actual primes of the extension field lying above a given finite place. -/
abbrev FinitePlacesAbove (L : Type v) [Field L] [NumberField L] [Algebra K L]
    (p : HeightOneSpectrum (𝓞 K)) :=
  {q : HeightOneSpectrum (𝓞 L) // q.asIdeal.LiesOver p.asIdeal}

instance finitePlacesAbove_finite (p : HeightOneSpectrum (𝓞 K)) :
    Finite (FinitePlacesAbove L p) := by
  apply Finite.of_injective
    (fun q : FinitePlacesAbove L p =>
      (⟨q.1.asIdeal, q.1.isPrime, q.2⟩ : p.asIdeal.primesOver (𝓞 L)))
  intro a b h
  apply Subtype.ext
  exact HeightOneSpectrum.ext (congrArg Subtype.val h)

instance finitePlacesAbove_fintype (p : HeightOneSpectrum (𝓞 K)) :
    Fintype (FinitePlacesAbove L p) := Fintype.ofFinite _

instance finitePlacesAbove_liesOver (p : HeightOneSpectrum (𝓞 K))
    (q : FinitePlacesAbove L p) : q.1.asIdeal.LiesOver p.asIdeal := q.2

omit [NumberField K] in
theorem finitePlacesAbove_under (p : HeightOneSpectrum (𝓞 K))
    (q : FinitePlacesAbove L p) : q.1.under (𝓞 K) = p :=
  HeightOneSpectrum.ext (q.1.asIdeal.over_def p.asIdeal).symm

/-- The coordinate formula for the extension norm at one finite place. -/
def finiteNormComponent (p : HeightOneSpectrum (𝓞 K)) :
    ((q : HeightOneSpectrum (𝓞 L)) → q.adicCompletion L) →* p.adicCompletion K where
  toFun a := ∏ q : FinitePlacesAbove L p, FiniteExtension.localNorm p q.1 (a q.1)
  map_one' := by simp
  map_mul' a b := by simp [map_mul, Finset.prod_mul_distrib]

theorem continuous_finiteNormComponent (p : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteNormComponent (L := L) p) :=
  continuous_finsetProd _ fun q _ =>
    (FiniteExtension.continuous_localNorm p q.1).comp (continuous_apply q.1)

theorem finiteNormComponent_integral (p : HeightOneSpectrum (𝓞 K))
    (a : (q : HeightOneSpectrum (𝓞 L)) → q.adicCompletion L)
    (ha : ∀ q : FinitePlacesAbove L p, a q.1 ∈ q.1.adicCompletionIntegers L) :
    finiteNormComponent p a ∈ p.adicCompletionIntegers K :=
  (p.adicCompletionIntegers K).prod_mem fun q _ =>
    FiniteExtension.localNorm_integral p q.1 (ha q)

private theorem finiteNormComponent_eventually_integral
    (a : (q : HeightOneSpectrum (𝓞 L)) → q.adicCompletion L)
    (ha : ∀ᶠ q in Filter.cofinite, a q ∈ q.adicCompletionIntegers L) :
    ∀ᶠ p in Filter.cofinite, finiteNormComponent p a ∈ p.adicCompletionIntegers K := by
  apply Filter.eventually_cofinite.mpr
  have hbad := (Filter.eventually_cofinite.mp ha).image
    (HeightOneSpectrum.under (𝓞 K))
  apply hbad.subset
  intro p hp
  by_contra h
  apply hp
  apply finiteNormComponent_integral
  intro q
  by_contra hq
  exact h ⟨q.1, hq, finitePlacesAbove_under p q⟩

/-- The finite-adele norm, a multiplicative map given by products of genuine local norms. -/
def finiteAdeleNorm : FiniteAdeleRing (𝓞 L) L →* FiniteAdeleRing (𝓞 K) K where
  toFun a := ⟨fun p => finiteNormComponent p a, finiteNormComponent_eventually_integral a a.2⟩
  map_one' := by
    apply FiniteAdeleRing.ext
    intro p
    exact map_one (finiteNormComponent (L := L) p)
  map_mul' a b := by
    apply FiniteAdeleRing.ext
    intro p
    exact map_mul (finiteNormComponent (L := L) p) (fun q => a q) (fun q => b q)

@[simp] theorem finiteAdeleNorm_apply (a : FiniteAdeleRing (𝓞 L) L)
    (p : HeightOneSpectrum (𝓞 K)) :
    finiteAdeleNorm a p =
      ∏ q : FinitePlacesAbove L p, FiniteExtension.localNorm p q.1 (a q.1) := rfl

theorem continuous_finiteAdeleNorm :
    Continuous (finiteAdeleNorm (K := K) (L := L)) := by
  change Continuous (finiteAdeleNorm :
    (Πʳ q : HeightOneSpectrum (𝓞 L), [q.adicCompletion L, q.adicCompletionIntegers L]) →
      FiniteAdeleRing (𝓞 K) K)
  apply RestrictedProduct.continuous_dom.mpr
  intro S hS
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    (HeightOneSpectrum.under (𝓞 K) '' Sᶜ)ᶜ
  have hT : Filter.cofinite ≤ Filter.principal T := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite] at hS ⊢
    simpa [T] using hS.image (HeightOneSpectrum.under (𝓞 K))
  let f : (Πʳ q : HeightOneSpectrum (𝓞 L),
      [q.adicCompletion L, q.adicCompletionIntegers L]_[Filter.principal S]) →
      (Πʳ p : HeightOneSpectrum (𝓞 K),
        [p.adicCompletion K, p.adicCompletionIntegers K]_[Filter.principal T]) :=
    fun a => ⟨fun p => finiteNormComponent p a, by
      intro p hp
      apply finiteNormComponent_integral
      intro q
      apply a.2
      by_contra hq
      exact hp ⟨q.1, hq, finitePlacesAbove_under p q⟩⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi fun p =>
      (continuous_finiteNormComponent p).comp RestrictedProduct.continuous_coe)
  exact (RestrictedProduct.continuous_inclusion hT).comp hf

/-- Actual infinite places lying above a chosen infinite place. -/
abbrev InfinitePlacesAbove (L : Type v) [Field L] [NumberField L] [Algebra K L]
    (p : InfinitePlace K) := {q : InfinitePlace L // q.LiesOver p}

instance infinitePlacesAbove_fintype (p : InfinitePlace K) :
    Fintype (InfinitePlacesAbove L p) := Fintype.ofFinite _

instance infinitePlacesAbove_liesOver (p : InfinitePlace K) (q : InfinitePlacesAbove L p) :
    q.1.LiesOver p := q.2

/-- The infinite-adele norm, taking the product over places above each coordinate. -/
def infiniteAdeleNorm : InfiniteAdeleRing L →* InfiniteAdeleRing K where
  toFun a p := ∏ q : InfinitePlacesAbove L p, InfiniteExtension.localNorm p q.1 (a q.1)
  map_one' := by
    funext p
    change (∏ q : InfinitePlacesAbove L p, InfiniteExtension.localNorm p q.1 1) = 1
    simp only [map_one, Finset.prod_const_one]
  map_mul' a b := by
    funext p
    change (∏ q : InfinitePlacesAbove L p, InfiniteExtension.localNorm p q.1 (a q.1 * b q.1)) =
      (∏ q : InfinitePlacesAbove L p, InfiniteExtension.localNorm p q.1 (a q.1)) *
        (∏ q : InfinitePlacesAbove L p, InfiniteExtension.localNorm p q.1 (b q.1))
    simp only [map_mul, Finset.prod_mul_distrib]

omit [NumberField K] in
theorem continuous_infiniteAdeleNorm :
    Continuous (infiniteAdeleNorm (K := K) (L := L)) :=
  continuous_pi fun p => continuous_finsetProd _ fun q _ =>
    (InfiniteExtension.continuous_localNorm p q.1).comp (continuous_apply q.1)

/-- The actual adelic norm is multiplicative, with the local product formula in both factors. -/
def adeleNorm : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 K) K :=
  infiniteAdeleNorm.prodMap finiteAdeleNorm

theorem continuous_adeleNorm : Continuous (adeleNorm (K := K) (L := L)) :=
  (continuous_infiniteAdeleNorm.comp continuous_fst).prodMk
    (continuous_finiteAdeleNorm.comp continuous_snd)

/-- The induced continuous norm on actual idele units. -/
def ideleNorm : IdeleGroup (𝓞 L) L →ₜ* IdeleGroup (𝓞 K) K where
  __ := Units.map adeleNorm
  continuous_toFun := continuous_adeleNorm.units_map

@[simp] theorem ideleNorm_val (a : IdeleGroup (𝓞 L) L) :
    (ideleNorm (K := K) (L := L) a : AdeleRing (𝓞 K) K) =
      adeleNorm (K := K) (a : AdeleRing (𝓞 L) L) := rfl

open scoped TensorProduct

section FiniteComparison

open scoped FiniteExtension

/-- The canonical comparison to the product of completed fields above a finite place.
Its bijectivity is a separate local/global compatibility obligation. -/
def finiteTensorMap (p : HeightOneSpectrum (𝓞 K)) :
    p.adicCompletion K ⊗[K] L →ₐ[p.adicCompletion K]
      ((q : FinitePlacesAbove L p) → q.1.adicCompletion L) :=
  AlgHom.pi fun q =>
    Algebra.TensorProduct.lift
      (Algebra.algHom (p.adicCompletion K) (p.adicCompletion K) (q.1.adicCompletion L))
      (Algebra.algHom K L (q.1.adicCompletion L)) (fun _ _ => mul_comm ..)

@[simp] theorem finiteTensorMap_tmul (p : HeightOneSpectrum (𝓞 K))
    (x : p.adicCompletion K) (y : L) (q : FinitePlacesAbove L p) :
    finiteTensorMap p (x ⊗ₜ[K] y) q =
      FiniteExtension.completionMap p q.1 x *
        algebraMap L (q.1.adicCompletion L) y := rfl

@[simp] theorem finiteTensorMap_one_tmul (p : HeightOneSpectrum (𝓞 K))
    (y : L) (q : FinitePlacesAbove L p) :
    finiteTensorMap p (1 ⊗ₜ[K] y) q =
      algebraMap L (q.1.adicCompletion L) y := by
  rw [finiteTensorMap_tmul, map_one, one_mul]

end FiniteComparison

section InfiniteComparison

open scoped NumberField.LiesOver InfiniteExtension

local instance (q : InfinitePlace L) : IsScalarTower K L q.Completion :=
  .of_algebraMap_eq fun x => by
    apply InfinitePlace.Completion.ext
    simp [InfinitePlace.Completion.algebraMap_toCompletion,
      UniformSpace.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]

/-- The canonical comparison to the product of completed fields above an infinite place.
Its bijectivity is proved below from weak approximation and the local-degree sum. -/
def infiniteTensorMap (p : InfinitePlace K) :
    p.Completion ⊗[K] L →ₐ[p.Completion]
      ((q : InfinitePlacesAbove L p) → q.1.Completion) :=
  AlgHom.pi fun q =>
    Algebra.TensorProduct.lift
      (Algebra.algHom p.Completion p.Completion q.1.Completion)
      (Algebra.algHom K L q.1.Completion) (fun _ _ => mul_comm ..)

omit [NumberField K] in
@[simp] theorem infiniteTensorMap_tmul (p : InfinitePlace K)
    (x : p.Completion) (y : L) (q : InfinitePlacesAbove L p) :
    infiniteTensorMap p (x ⊗ₜ[K] y) q =
      NumberField.LiesOver.completionMap x *
        algebraMap L q.1.Completion y := rfl

omit [NumberField K] in
@[simp] theorem infiniteTensorMap_one_tmul (p : InfinitePlace K)
    (y : L) (q : InfinitePlacesAbove L p) :
    infiniteTensorMap p (1 ⊗ₜ[K] y) q = algebraMap L q.1.Completion y := by
  rw [infiniteTensorMap_tmul, map_one, one_mul]

omit [NumberField K] in
private theorem denseRange_infiniteAbove (p : InfinitePlace K) :
    DenseRange (fun y : L => fun q : InfinitePlacesAbove L p =>
      algebraMap L q.1.Completion y) := by
  classical
  let r : InfiniteAdeleRing L → ((q : InfinitePlacesAbove L p) → q.1.Completion) :=
    fun a q => a q.1
  have hr : Function.Surjective r := by
    intro a
    refine ⟨fun q => if h : q.LiesOver p then a ⟨q, h⟩ else 0, ?_⟩
    funext q
    exact dite_eq_left q.2
  exact hr.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap L)
    (continuous_pi fun q => continuous_apply q.1)

local instance (p : InfinitePlace K) : NontriviallyNormedField p.Completion :=
  { (inferInstance : NormedField p.Completion) with
    non_trivial := by
      refine ⟨2, ?_⟩
      have h := (InfinitePlace.Completion.isometry_extensionEmbedding p).norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.extensionEmbedding p)) (2 : p.Completion)
      rw [← h]
      norm_num only [map_ofNat, Complex.norm_ofNat] }

/-- Weak approximation and finite-dimensional closedness prove surjectivity at infinity. -/
theorem infiniteTensorMap_surjective (p : InfinitePlace K) :
    Function.Surjective (infiniteTensorMap (L := L) p) := by
  let f := (infiniteTensorMap (L := L) p).toLinearMap
  have hd : DenseRange f := by
    apply (denseRange_infiniteAbove (L := L) p).mono
    rintro _ ⟨y, rfl⟩
    exact ⟨1 ⊗ₜ[K] y, funext (infiniteTensorMap_one_tmul p y)⟩
  change Function.Surjective f
  rw [← Set.range_eq_univ, ← f.coe_range, ← f.range.closed_of_finiteDimensional.closure_eq]
  exact hd.closure_range

/-- The actual infinite local degrees sum to the global extension degree. -/
theorem infiniteLocalDegree_sum (p : InfinitePlace K) :
    (∑ q : InfinitePlacesAbove L p, Module.finrank p.Completion q.1.Completion) =
      Module.finrank K L := by
  classical
  calc
    _ = ∑ q : InfinitePlacesAbove L p, p.inertiaDeg q.1 := by
      apply Finset.sum_congr rfl
      intro q _
      exact (p.inertiaDeg_eq_finrank q.1).symm
    _ = ∑ q ∈ (p.placesOver L).toFinset, p.inertiaDeg q := by
      exact (Finset.sum_subtype (p := fun q : InfinitePlace L => q.LiesOver p)
        (p.placesOver L).toFinset (fun q => Set.mem_toFinset)
        (fun q => p.inertiaDeg q)).symm
    _ = Module.finrank K L := InfinitePlace.sum_inertiaDeg_eq_finrank K L p

/-- The comparison at infinity is bijective by weak approximation and the local-degree sum. -/
theorem infiniteTensorMap_bijective (p : InfinitePlace K) :
    Function.Bijective (infiniteTensorMap (L := L) p) := by
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (infiniteTensorMap (L := L) p).toLinearMap (infiniteTensorMap_surjective p)
  rw [Module.finrank_baseChange, Module.finrank_pi_fintype, infiniteLocalDegree_sum]

/-- The actual completed tensor-product decomposition at an infinite place. -/
def infiniteTensorEquiv (p : InfinitePlace K) :
    p.Completion ⊗[K] L ≃ₐ[p.Completion]
      ((q : InfinitePlacesAbove L p) → q.1.Completion) :=
  AlgEquiv.ofBijective (infiniteTensorMap p) (infiniteTensorMap_bijective p)

@[simp] theorem infiniteTensorEquiv_apply (p : InfinitePlace K)
    (z : p.Completion ⊗[K] L) :
    infiniteTensorEquiv p z = infiniteTensorMap p z := rfl

end InfiniteComparison

end Langlands.Global.AdelicFunctoriality
