import Langlands.Global.AdelicFunctoriality.IntegralTopology
import Langlands.Global.AdelicFunctoriality.NormReduction
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Global.AdelicFunctoriality.NormCompatibilityProof
import Langlands.Global.Adelic
import Langlands.HarmonicAnalysis.Basic

/-!
# Products of local traces on adeles

For a finite extension `L / K` of number fields, the adelic trace `A_L → A_K` has
coordinate `Σ_{q | p} Tr_{L_q / K_p} (a_q)` at each place `p` of `K`.
-/

noncomputable section

open scoped TensorProduct

universe u v w

namespace Langlands.Global.AdelicFunctoriality

/-- Traces commute with scalar extension from a field. -/
theorem trace_baseChange {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Module.Finite K B] (x : B) :
    Algebra.trace A (A ⊗[K] B) (1 ⊗ₜ[K] x) = algebraMap K A (Algebra.trace K B x) := by
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange,
    Algebra.trace_apply]

/-- The trace of an element of a dependent finite product algebra is the sum of its traces. -/
theorem trace_pi (K : Type u) [Field K] (ι : Type v) [Fintype ι]
    (B : ι → Type w) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
    [∀ i, Module.Finite K (B i)] (x : ∀ i, B i) :
    Algebra.trace K (∀ i, B i) x = ∑ i, Algebra.trace K (B i) (x i) := by
  classical
  revert B
  refine Fintype.induction_empty_option (P := fun ι _ =>
    ∀ (B : ι → Type w) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
      [∀ i, Module.Finite K (B i)] (x : ∀ i, B i),
      Algebra.trace K (∀ i, B i) x = ∑ i, Algebra.trace K (B i) (x i)) ?_ ?_ ?_ ι
  · intro α β _ e ih B _ _ _ x
    let : Fintype α := Fintype.ofEquiv β e.symm
    let e' := (AlgEquiv.piCongrLeft K B e).symm
    calc
      Algebra.trace K (∀ i, B i) x = Algebra.trace K _ (e' x) :=
        (Algebra.trace_eq_of_algEquiv e' x).symm
      _ = ∑ i, Algebra.trace K (B (e i)) (x (e i)) := ih _ _
      _ = ∑ i, Algebra.trace K (B i) (x i) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
  · intro B _ _ _ x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  · intro α _ ih B _ _ _ x
    let e : ((i : Option α) → B i) ≃ₐ[K] B none × ((i : α) → B (some i)) :=
      { Equiv.piOptionEquivProd with
        map_add' := fun _ _ => rfl
        map_mul' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    calc
      Algebra.trace K (∀ i, B i) x = Algebra.trace K _ (e x) :=
        (Algebra.trace_eq_of_algEquiv e x).symm
      _ = Algebra.trace K (B none) (x none) +
          Algebra.trace K (∀ i : α, B (some i)) (fun i => x (some i)) :=
        Algebra.trace_prod_apply _
      _ = Algebra.trace K (B none) (x none) + ∑ i, Algebra.trace K (B (some i)) (x (some i)) := by
        rw [ih]
      _ = ∑ i, Algebra.trace K (B i) (x i) :=
        (Fintype.sum_option (fun i => Algebra.trace K (B i) (x i))).symm

/-- A specified tensor decomposition transports the trace to a sum of traces. -/
theorem trace_tensor_pi {K A B : Type*} [Field K] [Field A] [CommRing B]
    [Algebra K A] [Algebra K B] [Module.Finite K B]
    {ι : Type*} [Fintype ι] (C : ι → Type*)
    [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)] [∀ i, Module.Finite A (C i)]
    (e : A ⊗[K] B ≃ₐ[A] ∀ i, C i) (x : B) :
    (∑ i, Algebra.trace A (C i) (e (1 ⊗ₜ[K] x) i)) = algebraMap K A (Algebra.trace K B x) := by
  rw [← trace_pi A ι C, Algebra.trace_eq_of_algEquiv e, trace_baseChange]

namespace FiniteExtension

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Valued

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
  [q.asIdeal.LiesOver p.asIdeal]

/-- The trace of the finite extension `L_q / K_p` of completed fields. -/
def localTrace : q.adicCompletion L →ₗ[p.adicCompletion K] p.adicCompletion K :=
  Algebra.trace (p.adicCompletion K) (q.adicCompletion L)

theorem continuous_localTrace : Continuous (localTrace p q) :=
  (localTrace p q).continuous_of_finiteDimensional

/-- The local trace is linear over the completed base field. -/
theorem localTrace_completionMap_mul (c : p.adicCompletion K) (x : q.adicCompletion L) :
    localTrace p q (completionMap p q c * x) = c * localTrace p q x := by
  have h : completionMap p q c * x = c • x := (Algebra.smul_def c x).symm
  rw [h, map_smul, smul_eq_mul]

/-- The local trace of a base-field element is multiplication by the local degree. -/
theorem localTrace_completionMap (c : p.adicCompletion K) :
    localTrace p q (completionMap p q c) =
      (Module.finrank (p.adicCompletion K) (q.adicCompletion L) : p.adicCompletion K) * c := by
  have h : completionMap p q c = algebraMap (p.adicCompletion K) (q.adicCompletion L) c := rfl
  rw [localTrace, h, Algebra.trace_algebraMap, nsmul_eq_mul]

section Integral

open scoped IntegralTopology

variable (q' : FinitePlacesAbove L p)

/-- The local trace maps completed integers to completed integers: completed integers
are finite over the lower completed integers, so they are integral, and the lower
completed integers are integrally closed in the completed field. -/
theorem localTrace_integral {x : q'.1.adicCompletion L}
    (hx : x ∈ q'.1.adicCompletionIntegers L) :
    localTrace p q'.1 x ∈ p.adicCompletionIntegers K := by
  have : Module.Finite (p.adicCompletionIntegers K) (q'.1.adicCompletionIntegers L) :=
    IntegralTopology.localFinite p q'
  have : IsScalarTower (p.adicCompletionIntegers K) (q'.1.adicCompletionIntegers L)
      (q'.1.adicCompletion L) := .of_algebraMap_eq fun _ => rfl
  let x' : q'.1.adicCompletionIntegers L := ⟨x, hx⟩
  have h1 : IsIntegral (p.adicCompletionIntegers K) x' := Algebra.IsIntegral.isIntegral x'
  have h2 : IsIntegral (p.adicCompletionIntegers K) x :=
    h1.map (IsScalarTower.toAlgHom (p.adicCompletionIntegers K)
      (q'.1.adicCompletionIntegers L) (q'.1.adicCompletion L))
  have h3 := Algebra.isIntegral_trace (L := p.adicCompletion K) h2
  exact (Valuation.Integers.isIntegral_iff_v_le_one
    (Valuation.integer.integers (Valued.v : Valuation (p.adicCompletion K) _))).mp h3

end Integral

end FiniteExtension

namespace InfiniteExtension

open NumberField
open scoped NumberField.LiesOver

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [Algebra K L]
  (p : InfinitePlace K) (q : InfinitePlace L) [q.LiesOver p]

local instance : NontriviallyNormedField p.Completion :=
  { (inferInstance : NormedField p.Completion) with
    non_trivial := by
      refine ⟨2, ?_⟩
      have h := (InfinitePlace.Completion.isometry_extensionEmbedding p).norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.extensionEmbedding p)) (2 : p.Completion)
      rw [← h]
      norm_num only [map_ofNat, Complex.norm_ofNat] }

/-- The trace of the extension `L_q / K_p` of archimedean completions. -/
def localTrace : q.Completion →ₗ[p.Completion] p.Completion :=
  Algebra.trace p.Completion q.Completion

theorem continuous_localTrace : Continuous (localTrace p q) :=
  (localTrace p q).continuous_of_finiteDimensional

end InfiniteExtension

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField RestrictedProduct

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

section FiniteTrace

/-- The coordinate formula for the adelic trace at one finite place. -/
def finiteTraceComponent (p : HeightOneSpectrum (𝓞 K)) :
    ((q : HeightOneSpectrum (𝓞 L)) → q.adicCompletion L) →+ p.adicCompletion K where
  toFun a := ∑ q : FinitePlacesAbove L p, FiniteExtension.localTrace p q.1 (a q.1)
  map_zero' := by simp
  map_add' a b := by simp [map_add, Finset.sum_add_distrib]

theorem continuous_finiteTraceComponent (p : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteTraceComponent (L := L) p) :=
  continuous_finsetSum _ fun q _ =>
    (FiniteExtension.continuous_localTrace p q.1).comp (continuous_apply q.1)

theorem finiteTraceComponent_integral (p : HeightOneSpectrum (𝓞 K))
    (a : (q : HeightOneSpectrum (𝓞 L)) → q.adicCompletion L)
    (ha : ∀ q : FinitePlacesAbove L p, a q.1 ∈ q.1.adicCompletionIntegers L) :
    finiteTraceComponent p a ∈ p.adicCompletionIntegers K :=
  (p.adicCompletionIntegers K).sum_mem fun q _ =>
    FiniteExtension.localTrace_integral p q (ha q)

private theorem finiteTraceComponent_eventually_integral
    (a : (q : HeightOneSpectrum (𝓞 L)) → q.adicCompletion L)
    (ha : ∀ᶠ q in Filter.cofinite, a q ∈ q.adicCompletionIntegers L) :
    ∀ᶠ p in Filter.cofinite, finiteTraceComponent p a ∈ p.adicCompletionIntegers K := by
  apply Filter.eventually_cofinite.mpr
  have hbad := (Filter.eventually_cofinite.mp ha).image
    (HeightOneSpectrum.under (𝓞 K))
  apply hbad.subset
  intro p hp
  by_contra h
  apply hp
  apply finiteTraceComponent_integral
  intro q
  by_contra hq
  exact h ⟨q.1, hq, finitePlacesAbove_under p q⟩

/-- The finite-adele trace, given by sums of local traces. -/
def finiteAdeleTrace : FiniteAdeleRing (𝓞 L) L →+ FiniteAdeleRing (𝓞 K) K where
  toFun a := ⟨fun p => finiteTraceComponent p a, finiteTraceComponent_eventually_integral a a.2⟩
  map_zero' := by
    apply FiniteAdeleRing.ext
    intro p
    exact map_zero (finiteTraceComponent (L := L) p)
  map_add' a b := by
    apply FiniteAdeleRing.ext
    intro p
    exact map_add (finiteTraceComponent (L := L) p) (fun q => a q) (fun q => b q)

@[simp] theorem finiteAdeleTrace_apply (a : FiniteAdeleRing (𝓞 L) L)
    (p : HeightOneSpectrum (𝓞 K)) :
    finiteAdeleTrace a p =
      ∑ q : FinitePlacesAbove L p, FiniteExtension.localTrace p q.1 (a q.1) := rfl

theorem continuous_finiteAdeleTrace :
    Continuous (finiteAdeleTrace (K := K) (L := L)) := by
  change Continuous (finiteAdeleTrace :
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
    fun a => ⟨fun p => finiteTraceComponent p a, by
      intro p hp
      apply finiteTraceComponent_integral
      intro q
      apply a.2
      by_contra hq
      exact hp ⟨q.1, hq, finitePlacesAbove_under p q⟩⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi fun p =>
      (continuous_finiteTraceComponent p).comp RestrictedProduct.continuous_coe)
  exact (RestrictedProduct.continuous_inclusion hT).comp hf

end FiniteTrace

section InfiniteTrace

/-- The infinite-adele trace, summing over the places above each coordinate. -/
def infiniteAdeleTrace : InfiniteAdeleRing L →+ InfiniteAdeleRing K where
  toFun a p := ∑ q : InfinitePlacesAbove L p, InfiniteExtension.localTrace p q.1 (a q.1)
  map_zero' := by
    funext p
    change (∑ q : InfinitePlacesAbove L p, InfiniteExtension.localTrace p q.1 0) = 0
    simp only [map_zero, Finset.sum_const_zero]
  map_add' a b := by
    funext p
    change (∑ q : InfinitePlacesAbove L p,
        InfiniteExtension.localTrace p q.1 (a q.1 + b q.1)) =
      (∑ q : InfinitePlacesAbove L p, InfiniteExtension.localTrace p q.1 (a q.1)) +
        (∑ q : InfinitePlacesAbove L p, InfiniteExtension.localTrace p q.1 (b q.1))
    simp only [map_add, Finset.sum_add_distrib]

omit [NumberField K] in
@[simp] theorem infiniteAdeleTrace_apply (a : InfiniteAdeleRing L) (p : InfinitePlace K) :
    infiniteAdeleTrace a p =
      ∑ q : InfinitePlacesAbove L p, InfiniteExtension.localTrace p q.1 (a q.1) := rfl

omit [NumberField K] in
theorem continuous_infiniteAdeleTrace :
    Continuous (infiniteAdeleTrace (K := K) (L := L)) :=
  continuous_pi fun p => continuous_finsetSum _ fun q _ =>
    (InfiniteExtension.continuous_localTrace p q.1).comp (continuous_apply q.1)

end InfiniteTrace

/-- The adelic trace `A_L → A_K`. -/
def adeleTrace : AdeleRing (𝓞 L) L →+ AdeleRing (𝓞 K) K :=
  infiniteAdeleTrace.prodMap finiteAdeleTrace

@[simp] theorem adeleTrace_fst (a : AdeleRing (𝓞 L) L) :
    (adeleTrace (K := K) a).1 = infiniteAdeleTrace a.1 := rfl

@[simp] theorem adeleTrace_snd (a : AdeleRing (𝓞 L) L) :
    (adeleTrace (K := K) a).2 = finiteAdeleTrace a.2 := rfl

theorem continuous_adeleTrace : Continuous (adeleTrace (K := K) (L := L)) :=
  (continuous_infiniteAdeleTrace.comp continuous_fst).prodMk
    (continuous_finiteAdeleTrace.comp continuous_snd)

section Principal

open scoped NumberField.LiesOver InfiniteExtension FiniteExtension

/-- The sum of the local traces of a global element at the places above an infinite
place is its global trace. -/
theorem infiniteTrace_principal (p : InfinitePlace K) (x : L) :
    (∑ q : InfinitePlacesAbove L p,
      InfiniteExtension.localTrace p q.1 (algebraMap L q.1.Completion x)) =
        algebraMap K p.Completion (Algebra.trace K L x) := by
  simpa only [infiniteTensorEquiv_apply, infiniteTensorMap_one_tmul,
    InfiniteExtension.localTrace] using
    trace_tensor_pi (fun q : InfinitePlacesAbove L p => q.1.Completion)
      (infiniteTensorEquiv p) x

/-- The sum of the local traces of a global element at the places above a finite
place is its global trace. -/
theorem finiteTrace_principal (p : HeightOneSpectrum (𝓞 K)) (x : L) :
    (∑ q : FinitePlacesAbove L p,
      FiniteExtension.localTrace p q.1 (algebraMap L (q.1.adicCompletion L) x)) =
        algebraMap K (p.adicCompletion K) (Algebra.trace K L x) := by
  let e := AlgEquiv.ofBijective (finiteTensorMap (L := L) p)
    ((normCompatibility.{u, v}.1 K L).1 p)
  have he (z) : e z = finiteTensorMap p z := rfl
  simpa only [he, finiteTensorMap_one_tmul, FiniteExtension.localTrace] using
    trace_tensor_pi (fun q : FinitePlacesAbove L p => q.1.adicCompletion L) e x

/-- The adelic trace of a principal adele is the principal adele of the global trace. -/
theorem adeleTrace_principal (x : L) :
    adeleTrace (K := K) (algebraMap L (AdeleRing (𝓞 L) L) x) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.trace K L x) := by
  apply Prod.ext
  · funext p
    exact infiniteTrace_principal p x
  · apply FiniteAdeleRing.ext
    intro p
    exact finiteTrace_principal p x

/-- The finite part of the principal formula. -/
theorem finiteAdeleTrace_principal (x : L) :
    finiteAdeleTrace (K := K) (algebraMap L (FiniteAdeleRing (𝓞 L) L) x) =
      algebraMap K (FiniteAdeleRing (𝓞 K) K) (Algebra.trace K L x) := by
  apply FiniteAdeleRing.ext
  intro p
  exact finiteTrace_principal p x

end Principal

section Linearity

/-- At a place `q` above `p`, the inclusion of finite adeles is the completion map applied
to the coordinate at `p`. -/
theorem finiteAdeleInclusion_apply_above (a : FiniteAdeleRing (𝓞 K) K)
    (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p) :
    finiteAdeleInclusion a q.1 = FiniteExtension.completionMap p q.1 (a p) := by
  obtain ⟨q, hq⟩ := q
  have h : q.under (𝓞 K) = p := finitePlacesAbove_under p ⟨q, hq⟩
  subst h
  rfl

/-- The finite-adele trace is linear over the finite adeles of the base. -/
theorem finiteAdeleTrace_inclusion_mul (a : FiniteAdeleRing (𝓞 K) K)
    (y : FiniteAdeleRing (𝓞 L) L) :
    finiteAdeleTrace (finiteAdeleInclusion a * y) = a * finiteAdeleTrace y := by
  apply FiniteAdeleRing.ext
  intro p
  change (∑ q : FinitePlacesAbove L p, FiniteExtension.localTrace p q.1
      (finiteAdeleInclusion a q.1 * y q.1)) =
    a p * ∑ q : FinitePlacesAbove L p, FiniteExtension.localTrace p q.1 (y q.1)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [finiteAdeleInclusion_apply_above, FiniteExtension.localTrace_completionMap_mul]

end Linearity

section Single

/-- The finite-adele trace of an adele supported at one place `q` above `p` is
supported at `p`, with the local trace there. -/
theorem finiteAdeleTrace_single [DecidableEq (HeightOneSpectrum (𝓞 L))]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p) (x : q.1.adicCompletion L) :
    finiteAdeleTrace (RestrictedProduct.single
        (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L) q.1 x) =
      RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K)
        p (FiniteExtension.localTrace p q.1 x) := by
  apply FiniteAdeleRing.ext
  intro p'
  change (∑ q' : FinitePlacesAbove L p', FiniteExtension.localTrace p' q'.1
      (Pi.single q.1 x q'.1)) = Pi.single p (FiniteExtension.localTrace p q.1 x) p'
  by_cases hp : p' = p
  · subst hp
    rw [Pi.single_eq_same, Finset.sum_eq_single q]
    · rw [Pi.single_eq_same]
    · intro q' _ hq'
      have hne : q'.1 ≠ q.1 := fun h => hq' (Subtype.ext h)
      rw [Pi.single_eq_of_ne hne, map_zero]
    · intro h
      exact absurd (Finset.mem_univ q) h
  · rw [Pi.single_eq_of_ne hp]
    refine Finset.sum_eq_zero fun q' _ => ?_
    have hne : q'.1 ≠ q.1 := by
      intro h
      apply hp
      rw [← finitePlacesAbove_under p' q', ← finitePlacesAbove_under p q, h]
    rw [Pi.single_eq_of_ne hne, map_zero]

end Single

section Character

open Langlands.Global

/-- A nontrivial character of `A_K` trivial on `K` is nontrivial on some adele with zero
infinite part: otherwise it would factor through the infinite adeles, in which `K` is
dense. -/
theorem exists_finiteAdele_ne_one (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hψ : ∀ x : K, ψ (diagonal K x) = 1) :
    ∃ a : Adeles K, a.1 = 0 ∧ ψ a ≠ 1 := by
  by_contra! h
  apply ψ.nontrivial
  let g : InfiniteAdeleRing K → Circle := fun x => ψ ((x, 0) : Adeles K)
  have hg : Continuous g :=
    ψ.continuous_toFun.comp (continuous_id.prodMk continuous_const)
  have hK : ∀ k : K, g (algebraMap K (InfiniteAdeleRing K) k) = 1 := by
    intro k
    let a1 : Adeles K := (algebraMap K (InfiniteAdeleRing K) k, 0)
    let a2 : Adeles K := (0, algebraMap K (FiniteAdeleRing (𝓞 K) K) k)
    have hsplit : diagonal K k = a1 + a2 :=
      Prod.ext (add_zero _).symm (zero_add _).symm
    have h1 := hψ k
    rw [hsplit, AddChar.map_add_eq_mul ψ.toAddChar a1 a2] at h1
    have h2 : ψ a2 = 1 := h a2 rfl
    rw [h2, mul_one] at h1
    exact h1
  have hinf : ∀ x : InfiniteAdeleRing K, g x = 1 := by
    intro x
    have hclosed : IsClosed {x | g x = 1} := isClosed_eq hg continuous_const
    exact (hclosed.closure_subset_iff.mpr (by rintro _ ⟨k, rfl⟩; exact hK k))
      (InfiniteAdeleRing.denseRange_algebraMap K x)
  refine DFunLike.ext _ _ fun a => ?_
  rw [AddChar.one_apply]
  let a1 : Adeles K := (a.1, 0)
  let a2 : Adeles K := (0, a.2)
  have hsplit : a = a1 + a2 := Prod.ext (add_zero _).symm (zero_add _).symm
  have h2 : ψ a2 = 1 := h a2 rfl
  rw [hsplit, AddChar.map_add_eq_mul ψ.toAddChar a1 a2]
  change ψ a1 * ψ a2 = 1
  rw [h2, mul_one]
  exact hinf a.1

/-- Every adele whose infinite part is zero is the adelic trace of an adele. -/
theorem exists_adeleTrace_eq_of_fst_eq_zero (a : AdeleRing (𝓞 K) K) (ha : a.1 = 0) :
    ∃ b : AdeleRing (𝓞 L) L, adeleTrace (K := K) b = a := by
  have hc : Algebra.trace K L (algebraMap K L ((Module.finrank K L : K)⁻¹)) = 1 := by
    rw [Algebra.trace_algebraMap, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
  have h2 : finiteAdeleTrace (K := K) (finiteAdeleInclusion a.2 *
      algebraMap L (FiniteAdeleRing (𝓞 L) L) (algebraMap K L ((Module.finrank K L : K)⁻¹))) =
      a.2 := by
    rw [finiteAdeleTrace_inclusion_mul, finiteAdeleTrace_principal, hc, map_one, mul_one]
  let b : AdeleRing (𝓞 L) L := (0, finiteAdeleInclusion a.2 *
    algebraMap L (FiniteAdeleRing (𝓞 L) L) (algebraMap K L ((Module.finrank K L : K)⁻¹)))
  refine ⟨b, Prod.ext ?_ ?_⟩
  · rw [adeleTrace_fst, ha]
    exact map_zero (infiniteAdeleTrace (K := K) (L := L))
  · rw [adeleTrace_snd]
    exact h2

/-- The character `ψ ∘ Tr_{A_L / A_K}` of `A_L`, for a character `ψ` of `A_K` trivial on
`K`. It is nontrivial, by `exists_finiteAdele_ne_one` and
`exists_adeleTrace_eq_of_fst_eq_zero`. -/
def traceAdditiveCharacter (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hψ : ∀ x : K, ψ (diagonal K x) = 1) :
    HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles L) where
  toAddChar := ψ.toAddChar.compAddMonoidHom adeleTrace
  continuous_toFun := ψ.continuous_toFun.comp continuous_adeleTrace
  nontrivial h := by
    obtain ⟨af, haf0, haf⟩ := exists_finiteAdele_ne_one ψ hψ
    obtain ⟨b, hb⟩ := exists_adeleTrace_eq_of_fst_eq_zero (L := L) af haf0
    apply haf
    have hval := DFunLike.congr_fun h b
    rw [AddChar.compAddMonoidHom_apply, AddChar.one_apply] at hval
    rw [← hb]
    exact hval

@[simp] theorem traceAdditiveCharacter_apply
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hψ : ∀ x : K, ψ (diagonal K x) = 1) (a : Adeles L) :
    traceAdditiveCharacter ψ hψ a = ψ (adeleTrace a) := rfl

/-- `ψ ∘ Tr` is trivial on `L`. -/
theorem traceAdditiveCharacter_diagonal
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hψ : ∀ x : K, ψ (diagonal K x) = 1) (x : L) :
    traceAdditiveCharacter ψ hψ (diagonal L x) = 1 := by
  rw [traceAdditiveCharacter_apply]
  change ψ (adeleTrace (algebraMap L (AdeleRing (𝓞 L) L) x)) = 1
  rw [adeleTrace_principal]
  exact hψ _

/-- The component of `ψ ∘ Tr` at a finite place `q` above `p` is the component of `ψ` at
`p` composed with the local trace. -/
theorem traceAdditiveCharacter_single [DecidableEq (HeightOneSpectrum (𝓞 L))]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hψ : ∀ x : K, ψ (diagonal K x) = 1)
    (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p) (x : q.1.adicCompletion L) :
    traceAdditiveCharacter ψ hψ (((0 : InfiniteAdeleRing L),
        (RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L)
          q.1 x : FiniteAdeleRing (𝓞 L) L)) : Adeles L) =
      ψ (((0 : InfiniteAdeleRing K),
        (RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K)
          p (FiniteExtension.localTrace p q.1 x) : FiniteAdeleRing (𝓞 K) K)) : Adeles K) := by
  let a : AdeleRing (𝓞 L) L := ((0 : InfiniteAdeleRing L),
    (RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L)
      q.1 x : FiniteAdeleRing (𝓞 L) L))
  let a' : AdeleRing (𝓞 K) K := ((0 : InfiniteAdeleRing K),
    (RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K)
      p (FiniteExtension.localTrace p q.1 x) : FiniteAdeleRing (𝓞 K) K))
  have h : adeleTrace (K := K) a = a' := by
    refine Prod.ext ?_ ?_
    · rw [adeleTrace_fst]
      exact map_zero (infiniteAdeleTrace (K := K) (L := L))
    · rw [adeleTrace_snd]
      exact finiteAdeleTrace_single p q x
  change ψ (adeleTrace (K := K) a) = ψ a'
  rw [h]

end Character

end Langlands.Global.AdelicFunctoriality
