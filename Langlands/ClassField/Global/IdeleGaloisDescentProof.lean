import Langlands.ClassField.Global.IdeleGaloisDescentStatement
import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.RingTheory.Trace.Basic

/-! # Proof of Galois descent for the actual idele inclusion -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct
open Langlands.Global.AdelicFunctoriality

universe u v

namespace IdeleGaloisDescentProof

section TensorInvariants

variable {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
  {A : Type*} [AddCommGroup A] [Module K A]

/-- Summing the automorphisms on the second tensor factor applies the trace. -/
theorem sum_lTensor_aut [FiniteDimensional K E] [IsGalois K E] (t : A ⊗[K] E) :
    ∑ σ : E ≃ₐ[K] E, LinearMap.lTensor A σ.toLinearMap t =
      LinearMap.lTensor A ((Algebra.linearMap K E) ∘ₗ Algebra.trace K E) t := by
  induction t with
  | tmul x y =>
    simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply, Algebra.linearMap_apply,
      trace_eq_sum_automorphisms, TensorProduct.tmul_sum]
    rfl
  | add s t hs ht => simp only [map_add, Finset.sum_add_distrib, hs, ht]

omit [Field E] [Algebra K E] in
/-- Extending scalars along `K → E` sends `A ⊗[K] K` into pure tensors with `1`. -/
theorem lTensor_algebraMap_eq {E : Type v} [Field E] [Algebra K E] (w : A ⊗[K] K) :
    LinearMap.lTensor A (Algebra.linearMap K E) w = (TensorProduct.rid K A w) ⊗ₜ[K] (1 : E) := by
  induction w with
  | tmul x k =>
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.linearMap_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add s t hs ht => rw [map_add, map_add, hs, ht, TensorProduct.add_tmul]

/-- A tensor fixed by all automorphisms acting on the second factor is a pure tensor `x ⊗ 1`. -/
theorem exists_tmul_one_of_lTensor_aut_eq [FiniteDimensional K E] [IsGalois K E] [CharZero K]
    (t : A ⊗[K] E) (ht : ∀ σ : E ≃ₐ[K] E, LinearMap.lTensor A σ.toLinearMap t = t) :
    ∃ x : A, x ⊗ₜ[K] (1 : E) = t := by
  have hsum := sum_lTensor_aut t
  simp only [ht, Finset.sum_const, Finset.card_univ] at hsum
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank] at hsum
  rw [LinearMap.lTensor_comp_apply, lTensor_algebraMap_eq] at hsum
  set n := Module.finrank K E
  have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  refine ⟨(n : K)⁻¹ • TensorProduct.rid K A (LinearMap.lTensor A (Algebra.trace K E) t), ?_⟩
  rw [← TensorProduct.smul_tmul', ← hsum, ← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ hn, one_smul]

/-- Descent through a bijective comparison that intertwines the second-factor action. -/
theorem exists_tmul_one_of_comparison [FiniteDimensional K E] [IsGalois K E] [CharZero K]
    {B : Type*} (T : A ⊗[K] E → B) (hT : Function.Bijective T)
    (act : (E ≃ₐ[K] E) → B → B)
    (hact : ∀ σ t, T (LinearMap.lTensor A σ.toLinearMap t) = act σ (T t))
    (c : B) (hc : ∀ σ, act σ c = c) :
    ∃ x : A, T (x ⊗ₜ[K] (1 : E)) = c := by
  obtain ⟨t, rfl⟩ := hT.2 c
  obtain ⟨x, hx⟩ := exists_tmul_one_of_lTensor_aut_eq t fun σ =>
    hT.1 ((hact σ t).trans (hc σ))
  exact ⟨x, congrArg T hx⟩

end TensorInvariants

section Finite

variable {K : Type u} {E : Type v} [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]

omit [NumberField K] [NumberField E] in
/-- A relative automorphism preserves the finite place of `K` below a finite place of `E`. -/
theorem finitePlaceEquiv_under (σ : E ≃ₐ[K] E) (q : HeightOneSpectrum (𝓞 E)) :
    (finitePlaceEquiv σ.toRingEquiv q).under (𝓞 K) = q.under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  ext x
  change RingOfIntegers.mapRingEquiv σ.toRingEquiv (algebraMap (𝓞 K) (𝓞 E) x) ∈ q.asIdeal ↔
    algebraMap (𝓞 K) (𝓞 E) x ∈ q.asIdeal
  have hx : RingOfIntegers.mapRingEquiv σ.toRingEquiv (algebraMap (𝓞 K) (𝓞 E) x) =
      algebraMap (𝓞 K) (𝓞 E) x := RingOfIntegers.ext (σ.commutes (x : K))
  rw [hx]

omit [NumberField K] in
theorem liesOver_finitePlaceEquiv (σ : E ≃ₐ[K] E) (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 E)) [q.asIdeal.LiesOver p.asIdeal] :
    (finitePlaceEquiv σ.toRingEquiv q).asIdeal.LiesOver p.asIdeal := by
  have h := liesOver_under (K := K) (finitePlaceEquiv σ.toRingEquiv q)
  rwa [finitePlaceEquiv_under, finitePlacesAbove_under p ⟨q, inferInstance⟩] at h

/-- The completed transport along `σ` fixes the completed embedding of `K_p`. -/
theorem finiteCompletionEquiv_completionMap (σ : E ≃ₐ[K] E) (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 E)) [q.asIdeal.LiesOver p.asIdeal]
    [(finitePlaceEquiv σ.toRingEquiv q).asIdeal.LiesOver p.asIdeal] (x : p.adicCompletion K) :
    finiteCompletionEquiv σ.toRingEquiv q
        (FiniteExtension.completionMap p (finitePlaceEquiv σ.toRingEquiv q) x) =
      FiniteExtension.completionMap p q x := by
  refine congrFun ((p.denseRange_algebraMap K).equalizer
    ((continuous_finiteCompletionEquiv σ.toRingEquiv q).comp
      (FiniteExtension.continuous_completionMap p _))
    (FiniteExtension.continuous_completionMap p q) ?_) x
  funext a
  simp only [Function.comp_apply, FiniteExtension.completionMap_coe, finiteCompletionEquiv_coe]
  exact congrArg _ (σ.commutes a)

/-- The finite adele inclusion at a place above `p`, read from the coordinate at `p`. -/
theorem finiteAdeleInclusion_apply_of_liesOver (x : FiniteAdeleRing (𝓞 K) K)
    (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 E)) [q.asIdeal.LiesOver p.asIdeal] :
    finiteAdeleInclusion x q = FiniteExtension.completionMap p q (x p) := by
  obtain rfl : q.under (𝓞 K) = p := finitePlacesAbove_under p ⟨q, inferInstance⟩
  rfl

theorem finiteAdeleInclusion_injective :
    Function.Injective (finiteAdeleInclusion (K := K) (L := E)) := by
  intro x y h
  apply FiniteAdeleRing.ext
  intro p
  obtain ⟨q⟩ := finitePlacesAbove_nonempty (L := E) p
  have hq := congrArg (fun z : FiniteAdeleRing (𝓞 E) E => z q.1) h
  simp only [finiteAdeleInclusion_apply_of_liesOver _ p q.1] at hq
  exact (FiniteExtension.completionMap p q.1).injective hq

theorem finiteAdeleEquiv_finiteAdeleInclusion (σ : E ≃ₐ[K] E) (x : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleEquiv σ.toRingEquiv (finiteAdeleInclusion x) = finiteAdeleInclusion x := by
  apply FiniteAdeleRing.ext
  intro q
  have := liesOver_finitePlaceEquiv σ (q.under (𝓞 K)) q
  rw [finiteAdeleEquiv_apply,
    finiteAdeleInclusion_apply_of_liesOver x (q.under (𝓞 K)) (finitePlaceEquiv σ.toRingEquiv q),
    finiteCompletionEquiv_completionMap, finiteAdeleInclusion_apply]

/-- The action of `σ` on the coordinates above `p`. -/
def finiteAboveAction (σ : E ≃ₐ[K] E) (p : HeightOneSpectrum (𝓞 K))
    (c : (q : FinitePlacesAbove E p) → q.1.adicCompletion E) :
    (q : FinitePlacesAbove E p) → q.1.adicCompletion E :=
  fun q => finiteCompletionEquiv σ.toRingEquiv q.1
    (c ⟨finitePlaceEquiv σ.toRingEquiv q.1, liesOver_finitePlaceEquiv σ p q.1⟩)

theorem finiteTensorMap_lTensor (σ : E ≃ₐ[K] E) (p : HeightOneSpectrum (𝓞 K))
    (t : p.adicCompletion K ⊗[K] E) :
    finiteTensorMap p (LinearMap.lTensor _ σ.toLinearMap t) =
      finiteAboveAction σ p (finiteTensorMap p t) := by
  induction t with
  | tmul x y =>
    funext q
    have := liesOver_finitePlaceEquiv σ p q.1
    change FiniteExtension.completionMap p q.1 x * algebraMap E (q.1.adicCompletion E) (σ y) =
      finiteCompletionEquiv σ.toRingEquiv q.1
        (FiniteExtension.completionMap p (finitePlaceEquiv σ.toRingEquiv q.1) x *
          algebraMap E ((finitePlaceEquiv σ.toRingEquiv q.1).adicCompletion E) y)
    rw [map_mul, finiteCompletionEquiv_completionMap, finiteCompletionEquiv_coe]
    rfl
  | add s t hs ht =>
    rw [map_add, map_add, hs, ht]
    funext q
    simp [finiteAboveAction]

variable [IsGalois K E]

theorem exists_finite_descent (a : FiniteAdeleRing (𝓞 E) E)
    (ha : ∀ σ : E ≃ₐ[K] E, finiteAdeleEquiv σ.toRingEquiv a = a) (p : HeightOneSpectrum (𝓞 K)) :
    ∃ x : p.adicCompletion K,
      ∀ q : FinitePlacesAbove E p, FiniteExtension.completionMap p q.1 x = a q.1 := by
  obtain ⟨x, hx⟩ := exists_tmul_one_of_comparison (finiteTensorMap (L := E) p)
    ((completedTensorComparison K E).1 p) (fun σ => finiteAboveAction σ p)
    (fun σ t => finiteTensorMap_lTensor σ p t) (fun q => a q.1) (fun σ => by
      funext q
      exact congrArg (fun b : FiniteAdeleRing (𝓞 E) E => b q.1) (ha σ))
  refine ⟨x, fun q => ?_⟩
  have hq := congrFun hx q
  rwa [finiteTensorMap_tmul, map_one, mul_one] at hq

theorem exists_finiteAdele_descent (a : FiniteAdeleRing (𝓞 E) E)
    (ha : ∀ σ : E ≃ₐ[K] E, finiteAdeleEquiv σ.toRingEquiv a = a) :
    ∃ b : FiniteAdeleRing (𝓞 K) K, finiteAdeleInclusion b = a := by
  choose x hx using fun p => exists_finite_descent a ha p
  have hint : ∀ᶠ p in Filter.cofinite, x p ∈ p.adicCompletionIntegers K := by
    have hbad := (Filter.eventually_cofinite.mp a.2).image (HeightOneSpectrum.under (𝓞 K))
    apply Filter.eventually_cofinite.mpr
    apply hbad.subset
    intro p hp
    obtain ⟨q⟩ := finitePlacesAbove_nonempty (L := E) p
    refine ⟨q.1, ?_, finitePlacesAbove_under p q⟩
    intro hq
    apply hp
    have hq' : a q.1 ∈ q.1.adicCompletionIntegers E := hq
    rw [← hx p q] at hq'
    exact (FiniteExtension.completionMap_mem_integers_iff p q.1 (x p)).mp hq'
  refine ⟨(⟨x, hint⟩ : FiniteAdeleRing (𝓞 K) K), ?_⟩
  apply FiniteAdeleRing.ext
  intro q
  exact (finiteAdeleInclusion_apply _ q).trans (hx _ ⟨q, liesOver_under q⟩)

end Finite

section Infinite

open scoped NumberField.LiesOver

variable {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]

theorem liesOver_of_comap_eq {q : InfinitePlace E} {p : InfinitePlace K}
    (h : q.comap (algebraMap K E) = p) : q.LiesOver p := by
  constructor
  rw [← h]
  ext x
  rfl

theorem liesOver_infinitePlaceEquiv (σ : E ≃ₐ[K] E) (p : InfinitePlace K)
    (q : InfinitePlace E) [q.LiesOver p] : (infinitePlaceEquiv σ.toRingEquiv q).LiesOver p := by
  apply liesOver_of_comap_eq
  change (q.comap σ.toRingEquiv.toRingHom).comap (algebraMap K E) = p
  rw [← InfinitePlace.comap_comp]
  have hc : σ.toRingEquiv.toRingHom.comp (algebraMap K E) = algebraMap K E := by
    ext a
    exact σ.commutes a
  rw [hc]
  exact InfinitePlace.LiesOver.comap_eq q p

theorem completionMap_algebraMap (p : InfinitePlace K) (q : InfinitePlace E) [q.LiesOver p]
    (x : K) :
    NumberField.LiesOver.completionMap (v := p) (w := q) (algebraMap K p.Completion x) =
      algebraMap E q.Completion (algebraMap K E x) :=
  NumberField.LiesOver.completionMap_coe (WithAbs.toAbs p.1 x)

variable [NumberField K] [NumberField E]

omit [NumberField K] [NumberField E] in
theorem infiniteAdeleMap_apply_of_liesOver (x : InfiniteAdeleRing K) (p : InfinitePlace K)
    (q : InfinitePlace E) [q.LiesOver p] :
    infiniteAdeleMap (algebraMap K E) x q =
      NumberField.LiesOver.completionMap (v := p) (w := q) (x p) := by
  have h := InfinitePlace.LiesOver.comap_eq q p
  subst h
  refine congrFun ((InfinitePlace.Completion.denseRange_coe _).equalizer
    (continuous_infiniteCompletionMap (algebraMap K E) q)
    NumberField.LiesOver.continuous_completionMap (funext fun w => ?_)) (x _)
  change infiniteCompletionMap (algebraMap K E) q
      (algebraMap K (q.comap (algebraMap K E)).Completion (WithAbs.ofAbs w)) =
    NumberField.LiesOver.completionMap
      (algebraMap K (q.comap (algebraMap K E)).Completion (WithAbs.ofAbs w))
  rw [infiniteCompletionMap_coe, completionMap_algebraMap]

theorem infiniteAdeleMap_injective :
    Function.Injective (infiniteAdeleMap (algebraMap K E)) := by
  intro x y h
  funext p
  obtain ⟨q, hq⟩ := InfinitePlace.comap_surjective (k := K) (K := E) p
  have := liesOver_of_comap_eq hq
  have hxy := congrFun h q
  simp only [infiniteAdeleMap_apply_of_liesOver _ p q] at hxy
  exact (NumberField.LiesOver.completionMap (v := p) (w := q)).injective hxy

theorem infiniteAdeleEquiv_infiniteAdeleMap (σ : E ≃ₐ[K] E)
    (x : InfiniteAdeleRing K) :
    infiniteAdeleEquiv σ.toRingEquiv (infiniteAdeleMap (algebraMap K E) x) =
      infiniteAdeleMap (algebraMap K E) x := by
  have hc : σ.toRingEquiv.toRingHom.comp (algebraMap K E) = algebraMap K E := by
    ext a
    exact σ.commutes a
  change infiniteAdeleMap σ.toRingEquiv.toRingHom (infiniteAdeleMap (algebraMap K E) x) = _
  rw [← RingHom.comp_apply, ← infiniteAdeleMap_comp, hc]

/-- The completed transport along `σ`, with its source written through `infinitePlaceEquiv`. -/
def infiniteTransport (σ : E ≃ₐ[K] E) (q : InfinitePlace E) :
    (infinitePlaceEquiv σ.toRingEquiv q).Completion ≃+* q.Completion :=
  infiniteCompletionEquiv σ.toRingEquiv q

omit [NumberField K] [NumberField E] in
theorem infiniteTransport_coe (σ : E ≃ₐ[K] E) (q : InfinitePlace E) (y : E) :
    infiniteTransport σ q (algebraMap E (infinitePlaceEquiv σ.toRingEquiv q).Completion y) =
      algebraMap E q.Completion (σ y) :=
  infiniteCompletionMap_coe σ.toRingEquiv.toRingHom q y

omit [NumberField K] [NumberField E] in
/-- The completed transport along `σ` fixes the completed embedding of `K_p`. -/
theorem infiniteTransport_completionMap (σ : E ≃ₐ[K] E) (p : InfinitePlace K)
    (q : InfinitePlace E) [q.LiesOver p] [(infinitePlaceEquiv σ.toRingEquiv q).LiesOver p]
    (x : p.Completion) :
    infiniteTransport σ q
        (NumberField.LiesOver.completionMap (v := p)
          (w := infinitePlaceEquiv σ.toRingEquiv q) x) =
      NumberField.LiesOver.completionMap (v := p) (w := q) x := by
  refine congrFun ((InfinitePlace.Completion.denseRange_coe p).equalizer
    ((continuous_infiniteCompletionMap σ.toRingEquiv.toRingHom q).comp
      (NumberField.LiesOver.continuous_completionMap (v := p)
        (w := infinitePlaceEquiv σ.toRingEquiv q)))
    (NumberField.LiesOver.continuous_completionMap (v := p) (w := q)) (funext fun w => ?_)) x
  change infiniteTransport σ q
      (NumberField.LiesOver.completionMap (v := p) (w := infinitePlaceEquiv σ.toRingEquiv q)
        (algebraMap K p.Completion (WithAbs.ofAbs w))) =
    NumberField.LiesOver.completionMap (algebraMap K p.Completion (WithAbs.ofAbs w))
  rw [completionMap_algebraMap, completionMap_algebraMap, infiniteTransport_coe]
  exact congrArg _ (σ.commutes _)

/-- The action of `σ` on the coordinates above an infinite place `p`. -/
def infiniteAboveAction (σ : E ≃ₐ[K] E) (p : InfinitePlace K)
    (c : (q : InfinitePlacesAbove E p) → q.1.Completion) :
    (q : InfinitePlacesAbove E p) → q.1.Completion :=
  fun q => infiniteTransport σ q.1
    (c ⟨infinitePlaceEquiv σ.toRingEquiv q.1, liesOver_infinitePlaceEquiv σ p q.1⟩)

omit [NumberField K] in
theorem infiniteTensorMap_lTensor (σ : E ≃ₐ[K] E) (p : InfinitePlace K)
    (t : p.Completion ⊗[K] E) :
    infiniteTensorMap p (LinearMap.lTensor _ σ.toLinearMap t) =
      infiniteAboveAction σ p (infiniteTensorMap p t) := by
  induction t with
  | tmul x y =>
    funext q
    have := liesOver_infinitePlaceEquiv σ p q.1
    change NumberField.LiesOver.completionMap (v := p) (w := q.1) x *
        algebraMap E q.1.Completion (σ y) =
      infiniteTransport σ q.1
        (NumberField.LiesOver.completionMap (v := p) (w := infinitePlaceEquiv σ.toRingEquiv q.1) x *
          algebraMap E (infinitePlaceEquiv σ.toRingEquiv q.1).Completion y)
    rw [map_mul, infiniteTransport_completionMap, infiniteTransport_coe]
  | add s t hs ht =>
    rw [map_add, map_add, hs, ht]
    funext q
    simp [infiniteAboveAction]

variable [IsGalois K E]

theorem exists_infinite_descent (a : InfiniteAdeleRing E)
    (ha : ∀ σ : E ≃ₐ[K] E, infiniteAdeleEquiv σ.toRingEquiv a = a) (p : InfinitePlace K) :
    ∃ x : p.Completion, ∀ q : InfinitePlacesAbove E p,
      NumberField.LiesOver.completionMap (v := p) (w := q.1) x = a q.1 := by
  obtain ⟨x, hx⟩ := exists_tmul_one_of_comparison (infiniteTensorMap (L := E) p)
    ((completedTensorComparison K E).2 p) (fun σ => infiniteAboveAction σ p)
    (fun σ t => infiniteTensorMap_lTensor σ p t) (fun q => a q.1) (fun σ => by
      funext q
      exact congrFun (ha σ) q.1)
  refine ⟨x, fun q => ?_⟩
  have hq := congrFun hx q
  rwa [infiniteTensorMap_tmul, map_one, mul_one] at hq

theorem exists_infiniteAdele_descent (a : InfiniteAdeleRing E)
    (ha : ∀ σ : E ≃ₐ[K] E, infiniteAdeleEquiv σ.toRingEquiv a = a) :
    ∃ b : InfiniteAdeleRing K, infiniteAdeleMap (algebraMap K E) b = a := by
  choose x hx using fun p => exists_infinite_descent a ha p
  refine ⟨x, funext fun q => ?_⟩
  have hq : q.LiesOver (q.comap (algebraMap K E)) := liesOver_of_comap_eq rfl
  rw [infiniteAdeleMap_apply_of_liesOver x (q.comap (algebraMap K E)) q]
  exact hx _ ⟨q, hq⟩

end Infinite

section Adele

variable {K : Type u} {E : Type v} [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]

theorem adeleInclusion_injective : Function.Injective (adeleInclusion (K := K) (L := E)) :=
  fun _ _ h => Prod.ext (infiniteAdeleMap_injective (congrArg Prod.fst h))
    (finiteAdeleInclusion_injective (congrArg Prod.snd h))

theorem adeleEquiv_adeleInclusion (σ : E ≃ₐ[K] E) (x : AdeleRing (𝓞 K) K) :
    adeleEquiv σ.toRingEquiv (adeleInclusion x) = adeleInclusion x :=
  Prod.ext (infiniteAdeleEquiv_infiniteAdeleMap σ x.1)
    (finiteAdeleEquiv_finiteAdeleInclusion σ x.2)

theorem exists_adele_descent [IsGalois K E] (a : AdeleRing (𝓞 E) E)
    (ha : ∀ σ : E ≃ₐ[K] E, adeleEquiv σ.toRingEquiv a = a) :
    ∃ b : AdeleRing (𝓞 K) K, adeleInclusion b = a := by
  obtain ⟨b₁, h₁⟩ := exists_infiniteAdele_descent a.1 fun σ => congrArg Prod.fst (ha σ)
  obtain ⟨b₂, h₂⟩ := exists_finiteAdele_descent a.2 fun σ => congrArg Prod.snd (ha σ)
  exact ⟨(b₁, b₂), Prod.ext h₁ h₂⟩

end Adele

end IdeleGaloisDescentProof

open IdeleGaloisDescentProof in
/-- Galois descent for the actual idele inclusion. -/
theorem ideleGaloisDescent : IdeleGaloisDescent.{u, v} := by
  intro K E _ _ _ _ _ _
  refine ⟨fun a b h => Units.ext (adeleInclusion_injective (congrArg Units.val h)),
    fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨b, hb⟩ := exists_adele_descent (a : AdeleRing (𝓞 E) E)
      fun σ => congrArg Units.val (ha σ)
    obtain ⟨b', hb'⟩ := exists_adele_descent ((a⁻¹ : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E)
      fun σ : E ≃ₐ[K] E => congrArg Units.val
        (show ideleEquiv σ.toRingEquiv a⁻¹ = a⁻¹ by rw [map_inv, ha σ])
    refine ⟨⟨b, b', adeleInclusion_injective (E := E) ?_, adeleInclusion_injective (E := E) ?_⟩,
      Units.ext hb⟩
    · rw [map_mul, map_one, hb, hb', Units.mul_inv]
    · rw [map_mul, map_one, hb, hb', Units.inv_mul]
  · rintro ⟨b, rfl⟩ σ
    exact Units.ext (adeleEquiv_adeleInclusion σ b)

end Langlands.ClassField.Global
