/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoverStalkRamification

/-!
# Counting the geometric points of an unramified fibre of a finite flat cover

Let `p : C ⟶ Y` be a finite morphism, `Y₀ ⊆ Y` an affine open with `A = Γ(Y, Y₀)` a domain and
`B = Γ(C, p⁻¹ Y₀)` flat over `A`, and `y : Spec k ⟶ Y` a `k`-rational point (a section of a
morphism `Y ⟶ Spec k`, `k` algebraically closed) in `Y₀` over which `p` is unramified. Then the
number of geometric points of `C` over `y` is the rank of `B` over `A`
(`AlgebraicGeometry.Scheme.Hom.natCard_geometricFiber_eq_finrank`): the sum of the products of
ramification indices and inertia degrees over `y` equals the rank, and both are `1`.

This is used in the covering step of blueprint `lemma-tangent-cones-on-cover` to identify the
degree of a finite étale cover with the rank of its normalization.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace RingHom.PointsOver

variable {A B Ω : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field Ω] {φ : A →+* Ω}

/-- If `φ : A →+* Ω` is surjective, a point of `B` over `φ` is determined by its kernel. -/
lemma ker_injective_of_surjective (hφ : Function.Surjective φ) :
    Function.Injective fun t : PointsOver φ B ↦ RingHom.ker t.1 := by
  intro t t' h
  ext b
  obtain ⟨a, ha⟩ := hφ (t b)
  have hb : b - algebraMap A B a ∈ RingHom.ker t'.1 := by
    rw [← show RingHom.ker t.1 = RingHom.ker t'.1 from h, RingHom.mem_ker, map_sub,
      apply_algebraMap, ha, sub_self]
  rw [RingHom.mem_ker, map_sub, apply_algebraMap, sub_eq_zero] at hb
  rw [hb, ha]

/-- If `φ : A →+* Ω` is surjective, the kernel of a point `t` of `B` over `φ` is a maximal ideal
with inertia degree `1` over `A`. -/
lemma inertiaDeg_ker_eq_one_of_surjective (hφ : Function.Surjective φ) (t : PointsOver φ B) :
    (RingHom.ker t.1).inertiaDeg A = 1 := by
  have ht : Function.Surjective t.1 := fun z ↦ by
    obtain ⟨a, rfl⟩ := hφ z
    exact ⟨algebraMap A B a, apply_algebraMap t a⟩
  have := RingHom.ker_isMaximal_of_surjective φ hφ
  have := RingHom.ker_isMaximal_of_surjective t.1 ht
  have := t.ker_liesOver
  rw [Ideal.inertiaDeg_eq_of_isMaximal (RingHom.ker φ)]
  let : Field (A ⧸ RingHom.ker φ) := Ideal.Quotient.field _
  let : Field (B ⧸ RingHom.ker t.1) := Ideal.Quotient.field _
  refine Subalgebra.bot_eq_top_iff_finrank_eq_one.mp (eq_top_iff.mpr fun x _ ↦ ?_)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, ha⟩ := hφ (t b)
  refine Algebra.mem_bot.mpr ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq, RingHom.mem_ker, map_sub,
    apply_algebraMap, ha, sub_self]

variable [IsAlgClosed Ω] [Algebra.IsIntegral A B]

/-- If `φ : A →+* Ω` is surjective onto an algebraically closed field and `B` is integral over
`A`, the points of `B` over `φ` correspond to the primes of `B` over `ker φ`. -/
lemma natCard_eq_natCard_primesOver_of_surjective (hφ : Function.Surjective φ) :
    Nat.card (PointsOver φ B) = Nat.card ((RingHom.ker φ).primesOver B) := by
  refine Nat.card_congr (Equiv.ofBijective (fun t ↦ ⟨RingHom.ker t.1, inferInstance,
    t.ker_liesOver⟩) ⟨fun t t' h ↦ ker_injective_of_surjective hφ congr($h.1), ?_⟩)
  rintro ⟨q, hq, hqp⟩
  obtain ⟨t, ht⟩ := exists_ker_eq (φ := φ) q
  exact ⟨t, Subtype.ext ht⟩

end RingHom.PointsOver

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] affineAlgebra

variable {k : Type u} [Field k] {C Y : Scheme.{u}} {Y₀ : Y.Opens} (hY₀ : IsAffineOpen Y₀)
  (y : Spec (.of k) ⟶ Y) (hy : y default ∈ Y₀)

/-- The point `Γ(Y, Y₀) →+* k` given by a `k`-rational point `y` of `Y` (a section of some
`sY : Y ⟶ Spec k`) is surjective. -/
lemma affinePoint_surjective (sY : Y ⟶ Spec (.of k)) (hys : y ≫ sY = 𝟙 _) :
    Function.Surjective (affinePoint y hY₀ hy) := by
  let σ : CommRingCat.of k ⟶ Γ(Y, Y₀) := Spec.preimage (hY₀.fromSpec ≫ sY)
  have h : σ ≫ CommRingCat.ofHom (affinePoint y hY₀ hy) = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc, SpecMap_affinePoint_fromSpec, hys,
      Spec.map_id]
  intro z
  refine ⟨σ z, ?_⟩
  have := congrArg (fun g ↦ g.hom z) h
  simpa using this

/-- The prime ideal of the image point of the geometric point attached to a point `t` of
`Γ(C, p⁻¹ Y₀)` over `y` is `ker t`. -/
lemma primeIdealOf_geometricFiberEquivPointsOver_symm (p : C ⟶ Y) [IsAffineHom p]
    (t : RingHom.PointsOver (affinePoint y hY₀ hy) Γ(C, p ⁻¹ᵁ Y₀))
    (hmem : ((geometricFiberEquivPointsOver p y hY₀ hy).symm t).1 default ∈ p ⁻¹ᵁ Y₀) :
    (hY₀.preimage p).primeIdealOf ⟨_, hmem⟩ = ⟨RingHom.ker t.1, inferInstance⟩ := by
  rw [IsAffineOpen.primeIdealOf_eq_iff]
  exact (geometricFiberEquivPointsOver_symm_apply_default p y hY₀ hy t).symm

/-- **The number of geometric points in an unramified fibre of a finite flat cover is the
rank.** Let `p : C ⟶ Y` be finite, `Y₀ ⊆ Y` an affine open with `Γ(Y, Y₀)` a domain over which
`Γ(C, p⁻¹ Y₀)` is flat, and `y` a `k`-rational point of `Y₀` (`k` algebraically closed) such that
`𝔪_{Y,y} 𝒪_{C,c} = 𝔪_{C,c}` at every point `c` over `y`. Then the geometric fibre of `p` over
`y` has `rank_{Γ(Y, Y₀)} Γ(C, p⁻¹ Y₀)` points (blueprint `lemma-tangent-cones-on-cover`). -/
theorem natCard_geometricFiber_eq_finrank [IsAlgClosed k] (p : C ⟶ Y) [IsFinite p]
    (hY₀ : IsAffineOpen Y₀) (y : Spec (.of k) ⟶ Y) (hy : y default ∈ Y₀)
    (sY : Y ⟶ Spec (.of k)) (hys : y ≫ sY = 𝟙 _) [IsDomain Γ(Y, Y₀)]
    [Module.Flat Γ(Y, Y₀) Γ(C, p ⁻¹ᵁ Y₀)]
    (hun : ∀ c : C, p c = y default → (maximalIdeal (Y.presheaf.stalk (p c))).map
      (p.stalkMap c).hom = maximalIdeal (C.presheaf.stalk c)) :
    Nat.card (p.GeometricFiber y) = Module.finrank Γ(Y, Y₀) Γ(C, p ⁻¹ᵁ Y₀) := by
  classical
  have := finite_affineAlgebra p hY₀
  have hφ := affinePoint_surjective hY₀ y hy sY hys
  let P := RingHom.ker (affinePoint y hY₀ hy)
  have : Finite (P.primesOver Γ(C, p ⁻¹ᵁ Y₀)) :=
    (Algebra.QuasiFinite.finite_primesOver P).to_subtype
  let := Fintype.ofFinite (P.primesOver Γ(C, p ⁻¹ᵁ Y₀))
  rw [Nat.card_congr (geometricFiberEquivPointsOver p y hY₀ hy),
    RingHom.PointsOver.natCard_eq_natCard_primesOver_of_surjective hφ,
    ← Ideal.sum_ramification_inertia_eq_finrank P, Nat.card_eq_fintype_card,
    Fintype.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have := q.2.1
  have := q.2.2
  obtain ⟨t, ht⟩ := RingHom.PointsOver.exists_ker_eq (φ := affinePoint y hY₀ hy) q.1
  let x := (geometricFiberEquivPointsOver p y hY₀ hy).symm t
  have hpx : p (x.1 default) = y default := by
    rw [← Scheme.Hom.comp_apply, x.2]
  have hmem : x.1 default ∈ p ⁻¹ᵁ Y₀ := by
    rw [Scheme.Hom.mem_preimage, hpx]
    exact hy
  have hq : (hY₀.preimage p).primeIdealOf ⟨x.1 default, hmem⟩ = ⟨q.1, q.2.1⟩ := by
    rw [primeIdealOf_geometricFiberEquivPointsOver_symm hY₀ y hy p t hmem]
    exact PrimeSpectrum.ext ht
  have he := ramificationIdx_primeIdealOf_eq_one p hY₀ (x.1 default) hmem (hun _ hpx)
  rw [hq] at he
  rw [he, ← ht, RingHom.PointsOver.inertiaDeg_ker_eq_one_of_surjective hφ t]

end AlgebraicGeometry.Scheme.Hom
