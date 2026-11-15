import Langlands.CommutativeAlgebra.Popescu.SequenceDimZeroResolutionStatement
import Langlands.CommutativeAlgebra.Popescu.LocalDimZeroResolutionStatement
import Langlands.CommutativeAlgebra.Popescu.LocalDimZeroResolutionProof
import Langlands.CommutativeAlgebra.Popescu.LocalLifting
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardDesingularizationProof

/-! # Proof of the sequence form of Stacks Lemmas 9.2 and 9.4 -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open TensorProduct

namespace SequenceDimZero

/-- The bottom hypothesis of `SequenceDimZeroResolutionStatement` for an ideal `K`. -/
def Bottom (R A Λ : Type u) [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]
    (f : A →ₐ[R] Λ) (q : Ideal Λ) (K : Ideal R) : Prop :=
  ∀ (R₁ Λ₁ : Type u) [CommRing R₁] [CommRing Λ₁] [Algebra R₁ Λ₁] (σ : R →+* R₁)
    (τ : Λ →+* Λ₁), Function.Surjective σ → Function.Surjective τ →
    RingHom.ker σ = K → RingHom.ker τ = K.map (algebraMap R Λ) →
    (∀ x, τ (algebraMap R Λ x) = algebraMap R₁ Λ₁ (σ x)) →
    ∀ (Q : Ideal Λ₁) [Q.IsPrime], Q.comap τ = q →
      Q ∈ minimalPrimes Λ₁ ∧
      ∃ (T : Type u) (_ : CommRing T)
        (_ : Algebra (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T)
        (u : A →+* T) (v : T →+* Localization.AtPrime Q),
        Algebra.Smooth (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T ∧
        u.comp (algebraMap R A) =
          (algebraMap (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T).comp
            ((algebraMap R₁ (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁)))).comp σ) ∧
        v.comp u = (algebraMap Λ₁ (Localization.AtPrime Q)).comp (τ.comp f.toRingHom)

theorem resolve (h6 : StrictlyStandardDesingularizationStatement.{u})
    (h2 : LocalDimZeroResolutionStatement.{u}) (r : ℕ) :
    ∀ (R A Λ : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing Λ]
      [IsNoetherianRing Λ] [Algebra R A] [Algebra R Λ] [Algebra.FinitePresentation R A]
      (f : A →ₐ[R] Λ) (q : Ideal Λ) [q.IsPrime] (π : Fin r → R),
      (∀ i, algebraMap R Λ (π i) ∈ q) →
      (∀ i (x : R), π i ^ 2 * x ∈ Ideal.span ((fun j => π j ^ 8) '' {j | j < i}) →
        π i * x ∈ Ideal.span ((fun j => π j ^ 8) '' {j | j < i})) →
      (∀ i (y : Λ), algebraMap R Λ (π i) ^ 2 * y ∈
          Ideal.span ((fun j => algebraMap R Λ (π j) ^ 8) '' {j | j < i}) →
        algebraMap R Λ (π i) * y ∈
          Ideal.span ((fun j => algebraMap R Λ (π j) ^ 8) '' {j | j < i})) →
      (∀ i, IsStrictlyStandard R (algebraMap R A (π i))) →
      Bottom R A Λ f q (Ideal.span (Set.range fun i => π i ^ 8)) →
      CanBeResolved R f q := by
  induction r with
  | zero =>
    intro R A Λ _ _ _ _ _ _ _ _ f q _ π _ _ _ _ hbot
    obtain ⟨hmin, T, _, _, u, v, hT, hu, hv⟩ := hbot R Λ (RingHom.id R) (RingHom.id Λ)
      Function.surjective_id Function.surjective_id
      (by rw [Set.range_eq_empty, Ideal.span_empty]
          exact (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id)
      (by rw [Set.range_eq_empty, Ideal.span_empty, Ideal.map_bot]
          exact (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id)
      (fun _ => rfl) q (Ideal.comap_id q)
    by_cases hle : singularRadical R f ≤ q
    · rw [RingHom.comp_id] at hu
      rw [RingHom.id_comp] at hv
      exact h2 R A Λ f q hle hmin T u v hu hv
    · exact ⟨A, inferInstance, inferInstance, inferInstance, AlgHom.id R A, f, rfl, le_rfl, hle⟩
  | succ r ih =>
    intro R A Λ _ _ _ _ _ _ _ _ f q _ π hq hR hΛ hss hbot
    set π₀ := π 0
    have hR0 : ∀ x : R, π₀ ^ 2 * x = 0 → π₀ * x = 0 := fun x hx => by
      have := hR 0 x (by rw [span_image_lt_zero, hx]; exact Ideal.zero_mem _)
      rwa [span_image_lt_zero, Ideal.mem_bot] at this
    have hΛ0 : ∀ y : Λ, algebraMap R Λ π₀ ^ 2 * y = 0 → algebraMap R Λ π₀ * y = 0 := fun y hy => by
      have := hΛ 0 y (by rw [span_image_lt_zero, hy]; exact Ideal.zero_mem _)
      rwa [span_image_lt_zero, Ideal.mem_bot] at this
    refine canBeResolved_of_quot h6 f q π₀ hR0 hΛ0 (hss 0) (hq 0) ?_
    let := isPrime_map_quot q (hq 0)
    set K := Ideal.span {π₀ ^ 8} with hK
    set KΛ := K.map (algebraMap R Λ) with hKΛ
    have hKΛ' : KΛ = Ideal.span {algebraMap R Λ π₀ ^ 8} := by
      rw [hKΛ, hK, Ideal.map_span, Set.image_singleton, map_pow]
    have hcompat : ∀ x : R, algebraMap (R ⧸ K) (Λ ⧸ KΛ) (Ideal.Quotient.mk K x) =
        Ideal.Quotient.mk KΛ (algebraMap R Λ x) := fun x => rfl
    refine ih (R ⧸ K) ((R ⧸ K) ⊗[R] A) (Λ ⧸ KΛ) (quotMap f π₀) (q.map (Ideal.Quotient.mk KΛ))
      (fun i => Ideal.Quotient.mk K (π i.succ)) ?_ ?_ ?_ ?_ ?_
    · intro i
      rw [hcompat]
      exact Ideal.mem_map_of_mem _ (hq i.succ)
    · intro i x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hset : (fun j => Ideal.Quotient.mk K (π j.succ) ^ 8) '' {j | j < i} =
          Ideal.Quotient.mk K '' ((fun j => π j.succ ^ 8) '' {j | j < i}) := by
        rw [Set.image_image]; simp only [map_pow]
      have hspan : Ideal.span ((fun j => π j.succ ^ 8) '' {j | j < i}) ⊔ K =
          Ideal.span ((fun j => π j ^ 8) '' {j | j < i.succ}) :=
        (span_image_lt_succ (fun j => π j ^ 8) i).symm
      rw [hset, ← Ideal.map_span, ← map_pow, ← map_mul, ← Ideal.mem_comap, comap_mk_map_mk,
        hspan] at hx
      rw [hset, ← Ideal.map_span, ← map_mul, ← Ideal.mem_comap, comap_mk_map_mk, hspan]
      exact hR i.succ x hx
    · intro i y hy
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hset : (fun j => algebraMap (R ⧸ K) (Λ ⧸ KΛ) (Ideal.Quotient.mk K (π j.succ)) ^ 8) ''
          {j | j < i} = Ideal.Quotient.mk KΛ ''
            ((fun j => algebraMap R Λ (π j.succ) ^ 8) '' {j | j < i}) := by
        rw [Set.image_image]; simp only [hcompat, map_pow]
      have hspan : Ideal.span ((fun j => algebraMap R Λ (π j.succ) ^ 8) '' {j | j < i}) ⊔ KΛ =
          Ideal.span ((fun j => algebraMap R Λ (π j) ^ 8) '' {j | j < i.succ}) := by
        rw [hKΛ']
        exact (span_image_lt_succ (fun j => algebraMap R Λ (π j) ^ 8) i).symm
      rw [hset, ← Ideal.map_span, hcompat, ← map_pow, ← map_mul, ← Ideal.mem_comap,
        comap_mk_map_mk, hspan] at hy
      rw [hset, ← Ideal.map_span, hcompat, ← map_mul, ← Ideal.mem_comap, comap_mk_map_mk, hspan]
      exact hΛ i.succ y hy
    · intro i
      rw [algebraMap_quot_tensor]
      exact (hss i.succ).baseChange
    · intro R₁ Λ₁ _ _ _ σ τ hσ hτ hkσ hkτ hστ Q _ hQ
      have hspanK : Ideal.span (Set.range fun i : Fin r => Ideal.Quotient.mk K (π i.succ) ^ 8) =
          (Ideal.span (Set.range fun i : Fin r => π i.succ ^ 8)).map (Ideal.Quotient.mk K) := by
        rw [Ideal.map_span, ← Set.range_comp]; simp only [Function.comp_def, map_pow]
      have hcomp : (algebraMap (R ⧸ K) (Λ ⧸ KΛ)).comp (Ideal.Quotient.mk K) =
          (Ideal.Quotient.mk KΛ).comp (algebraMap R Λ) := RingHom.ext hcompat
      obtain ⟨hmin, T, _, _, u, v, hT, hu, hv⟩ := hbot R₁ Λ₁ (σ.comp (Ideal.Quotient.mk K))
        (τ.comp (Ideal.Quotient.mk KΛ))
        (hσ.comp Ideal.Quotient.mk_surjective) (hτ.comp Ideal.Quotient.mk_surjective)
        (by rw [← RingHom.comap_ker, hkσ, hspanK, comap_mk_map_mk,
              span_range_succ (fun i => π i ^ 8)])
        (by rw [← RingHom.comap_ker, hkτ, hspanK, Ideal.map_map, hcomp, ← Ideal.map_map,
              comap_mk_map_mk, span_range_succ (fun i => π i ^ 8), Ideal.map_sup])
        (fun x => hστ (Ideal.Quotient.mk K x)) Q
        (by rw [← Ideal.comap_comap, hQ, comap_mk_map_mk,
              sup_eq_left.mpr (span_pow_map_le (hq 0))])
      refine ⟨hmin, T, inferInstance, inferInstance, ?_⟩
      -- transport `u` to `(R/π₀⁸) ⊗ A`
      set Rp := Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))
      let ιT : R ⧸ K →+* T := (algebraMap Rp T).comp ((algebraMap R₁ Rp).comp σ)
      let _ : Algebra R T := ((ιT).comp (algebraMap R (R ⧸ K))).toAlgebra
      let uA : A →ₐ[R] T := { u with commutes' := fun x => RingHom.congr_fun hu x }
      let uR : R ⧸ K →ₐ[R] T := { ιT with commutes' := fun x => rfl }
      let u' : (R ⧸ K) ⊗[R] A →ₐ[R] T := Algebra.TensorProduct.lift uR uA fun _ _ => .all _ _
      refine ⟨u'.toRingHom, v, hT, ?_, ?_⟩
      · ext x
        show u' (x ⊗ₜ 1) = ιT x
        simp [u', uR, uA]
      · apply RingHom.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul x a =>
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          have hux : u (algebraMap R A x) = ιT (Ideal.Quotient.mk K x) := RingHom.congr_fun hu x
          have h3 : v (ιT (Ideal.Quotient.mk K x)) =
              algebraMap Λ₁ _ (τ (Ideal.Quotient.mk KΛ (algebraMap R Λ x))) := by
            rw [← hux]
            have := RingHom.congr_fun hv (algebraMap R A x)
            simp only [RingHom.coe_comp, Function.comp_apply] at this
            rw [this]
            congr 3
            exact f.commutes x
          have h2 := RingHom.congr_fun hv a
          simp only [RingHom.coe_comp, Function.comp_apply] at h2
          show v (u' (Ideal.Quotient.mk K x ⊗ₜ a)) =
            algebraMap Λ₁ _ (τ (quotMap f π₀ (Ideal.Quotient.mk K x ⊗ₜ a)))
          simp only [u', Algebra.TensorProduct.lift_tmul, uR, uA, map_mul, quotMap, AlgHom.coe_mk]
          rw [h2, h3]
          rfl
        | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

end SequenceDimZero

/-- The sequence form of Stacks Lemmas 9.2 (07F8) and 9.4 (07FA). -/
theorem sequenceDimZeroResolution_of (h6 : StrictlyStandardDesingularizationStatement.{u})
    (h2 : LocalDimZeroResolutionStatement.{u}) : SequenceDimZeroResolutionStatement.{u} := by
  intro R A Λ _ _ _ _ _ _ _ _ f q _ r π hq hR hΛ hss hbot
  exact SequenceDimZero.resolve h6 h2 r R A Λ f q π hq hR hΛ hss hbot

/-- Stacks Lemmas 16.9.2 and 16.9.4 (07F8, 07FA): `SequenceDimZeroResolutionStatement` holds in
every universe. -/
theorem sequenceDimZeroResolution : SequenceDimZeroResolutionStatement.{u} :=
  sequenceDimZeroResolution_of Desing.strictlyStandardDesingularization localDimZeroResolution

end Langlands.CommutativeAlgebra.Popescu
