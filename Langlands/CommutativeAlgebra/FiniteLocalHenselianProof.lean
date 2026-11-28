import Langlands.CommutativeAlgebra.FiniteLocalHenselianStatement
import StacksFrontier.RingTheory.Henselian.FiniteType.Basic.ProductOfLocalRings
import Mathlib.RingTheory.AdjoinRoot

/-!
# Finite local algebras over Henselian local rings are Henselian

Let `R` be a Henselian local ring and `S` a local ring that is module-finite over `R`. To lift a
simple residue root `a₀` of a monic `f ∈ S[X]`, put `A = S[X]/(f)`, finite free over `S`.

* Idempotents of `A/𝔪_S A` lift to `A`: those of `A/𝔪_R A` lift by
  `henselian_lift_single_idem`, and `A/𝔪_R A → A/𝔪_S A` has nil kernel because `𝔪_S` lies in
  the radical of `𝔪_R S`.
* Writing `f = f(a₀) + (X - a₀) g`, the element `g(a₀)⁻¹ g(x)` is idempotent modulo `𝔪_S A` and
  is killed by `x - a₀` modulo `𝔪_S A`; lift it to an idempotent `e`.
* Nakayama's lemma shows that `S → A/(1 - e)` is surjective, and power-basis coordinates show it
  is injective. The image of `x` is then a root of `f` lifting `a₀`.
-/

open Polynomial IsLocalRing

universe u v w

namespace Langlands.CommutativeAlgebra

namespace FiniteLocalHenselian

/-- Idempotents lift modulo `𝔪_R A` for a module-finite algebra `A`, in any universe. -/
theorem exists_isIdempotentElem_sub_mem_map_maximalIdeal
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {A : Type w} [CommRing A] [Algebra R A] [Module.Finite R A]
    (x : A) (hx : x * x - x ∈ (maximalIdeal R).map (algebraMap R A)) :
    ∃ e : A, IsIdempotentElem e ∧ e - x ∈ (maximalIdeal R).map (algebraMap R A) := by
  have : Module.Finite R (ULift.{u} A) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := R)).symm
  let g : ULift.{u} A ≃ₐ[R] A := ULift.algEquiv
  set I' : Ideal (ULift.{u} A) := (maximalIdeal R).map (algebraMap R (ULift.{u} A)) with hI'
  set I : Ideal A := (maximalIdeal R).map (algebraMap R A) with hI
  have hgI : ∀ z ∈ I', g z ∈ I := by
    intro z hz
    have h1 : I'.map (g : ULift.{u} A →+* A) = I := by
      rw [hI', hI, Ideal.map_map]
      congr 1
    rw [← h1]
    exact Ideal.mem_map_of_mem _ hz
  have hgI' : ∀ z ∈ I, g.symm z ∈ I' := by
    intro z hz
    have h1 : I.map (g.symm : A →+* ULift.{u} A) = I' := by
      rw [hI', hI, Ideal.map_map]
      congr 1
    rw [← h1]
    exact Ideal.mem_map_of_mem _ hz
  obtain ⟨e', he', hmk⟩ := henselian_lift_single_idem.{u, w} R (ULift.{u} A)
    (Ideal.Quotient.mk I' (g.symm x)) (by
      rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
      have := hgI' _ hx
      simpa using this)
  refine ⟨g e', ?_, ?_⟩
  · rw [IsIdempotentElem, ← map_mul, he'.eq]
  · rw [Ideal.Quotient.eq] at hmk
    have := hgI _ hmk
    simpa using this

/-- For a local ring `S` module-finite over a local ring `R`, the maximal ideal of `S` lies in the
radical of `𝔪_R S`: every prime of `S` containing `𝔪_R S` is maximal by integrality, hence equals
`𝔪_S`. -/
theorem maximalIdeal_le_radical_map_maximalIdeal
    (R : Type u) [CommRing R] [IsLocalRing R]
    (S : Type v) [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    maximalIdeal S ≤ ((maximalIdeal R).map (algebraMap R S)).radical := by
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun P ⟨hle, hP⟩ => ?_
  have hcomap : P.comap (algebraMap R S) = maximalIdeal R := by
    have h1 : maximalIdeal R ≤ P.comap (algebraMap R S) := Ideal.map_le_iff_le_comap.mp hle
    exact ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_isPrime _ P).ne_top h1).symm
  have hmax : P.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R S)
      (Algebra.IsIntegral.isIntegral (R := R) (A := S) ·) P ?_
    rw [hcomap]
    exact maximalIdeal.isMaximal R
  exact (eq_maximalIdeal hmax).ge

/-- Idempotents lift modulo `𝔪_S A` for a module-finite algebra `A` over a local ring `S` that is
module-finite over a Henselian local ring `R`. The quotient map `A/𝔪_R A → A/𝔪_S A` has nil kernel,
so an idempotent of `A/𝔪_S A` lifts to one of `A/𝔪_R A`, which lifts to `A` by Henselianity. -/
theorem exists_isIdempotentElem_sub_mem_map_maximalIdeal_of_finite
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S]
    {A : Type w} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [Module.Finite S A]
    (x : A) (hx : x * x - x ∈ (maximalIdeal S).map (algebraMap S A)) :
    ∃ e : A, IsIdempotentElem e ∧ e - x ∈ (maximalIdeal S).map (algebraMap S A) := by
  have : Module.Finite R A := Module.Finite.trans S A
  set IR : Ideal A := (maximalIdeal R).map (algebraMap R A) with hIR
  set IS : Ideal A := (maximalIdeal S).map (algebraMap S A) with hIS
  have hIR' : IR = ((maximalIdeal R).map (algebraMap R S)).map (algebraMap S A) := by
    rw [hIR, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hRS : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap]
    have : ((maximalIdeal S).comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
        (Algebra.IsIntegral.isIntegral (R := R) (A := S) ·) _
    exact (eq_maximalIdeal this).ge
  have hle : IR ≤ IS := by
    rw [hIR', hIS]
    exact Ideal.map_mono hRS
  have hnil : IS ≤ IR.radical := by
    rw [hIS, hIR']
    exact (Ideal.map_mono (maximalIdeal_le_radical_map_maximalIdeal R S)).trans
      (Ideal.map_radical_le _)
  let F : A ⧸ IR →+* A ⧸ IS := Ideal.Quotient.factor hle
  have hker : ∀ z ∈ RingHom.ker F, IsNilpotent z := by
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
    obtain ⟨n, hn⟩ := hnil hz
    exact ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩
  obtain ⟨e', he', hFe'⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent F hker
    (Ideal.Quotient.mk IS x) ⟨Ideal.Quotient.mk IR x, Ideal.Quotient.factor_mk hle x⟩
    (by rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]; exact hx)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective e'
  obtain ⟨e, he, hey⟩ := exists_isIdempotentElem_sub_mem_map_maximalIdeal R (A := A) y
    (by rw [← Ideal.Quotient.eq, map_mul]; exact he'.eq)
  refine ⟨e, he, ?_⟩
  have hyx : y - x ∈ IS := by
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.factor_mk hle]
    exact hFe'
  have : e - x = (e - y) + (y - x) := by ring
  rw [this]
  exact add_mem (hle hey) hyx

/-- Hensel lifting over a local ring `S` module-finite over a Henselian local ring `R`: a monic
`f ∈ S[X]` with `f(a₀) ∈ 𝔪_S` and `f'(a₀)` a unit has a root `a ∈ S` with `a - a₀ ∈ 𝔪_S`. -/
theorem exists_isRoot_sub_mem_maximalIdeal
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S]
    (f : S[X]) (hf : f.Monic) (a₀ : S) (h₁ : f.eval a₀ ∈ maximalIdeal S)
    (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : S, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal S := by
  classical
  have hAfin : Module.Finite S (AdjoinRoot f) := hf.finite_adjoinRoot
  set x : AdjoinRoot f := AdjoinRoot.root f with hx
  set J : Ideal (AdjoinRoot f) := (maximalIdeal S).map (algebraMap S (AdjoinRoot f)) with hJ
  -- `f = f(a₀) + (X - a₀) g` and `g = g(a₀) + (X - a₀) h`, with `g(a₀) = f'(a₀)` a unit.
  set g : S[X] := f /ₘ (X - C a₀) with hg
  have hfg : f = C (f.eval a₀) + (X - C a₀) * g := by
    rw [← modByMonic_X_sub_C_eq_C_eval, modByMonic_add_div]
  have hga : g.eval a₀ = f.derivative.eval a₀ := by
    conv_rhs => rw [hfg]
    simp [derivative_mul]
  set h : S[X] := g /ₘ (X - C a₀) with hh
  have hgh : g = C (g.eval a₀) + (X - C a₀) * h := by
    rw [← modByMonic_X_sub_C_eq_C_eval, modByMonic_add_div]
  obtain ⟨u, hu⟩ : IsUnit (g.eval a₀) := hga ▸ h₂
  set v : AdjoinRoot f := algebraMap S (AdjoinRoot f) (↑u⁻¹ : S) with hv
  have hvu : v * algebraMap S (AdjoinRoot f) (g.eval a₀) = 1 := by
    rw [hv, ← map_mul, ← hu, Units.inv_mul, map_one]
  have hfx : algebraMap S (AdjoinRoot f) (f.eval a₀) +
      (x - algebraMap S (AdjoinRoot f) a₀) * aeval x g = 0 := by
    have h0 : aeval x f = 0 := by rw [hx, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have h1 := congrArg (aeval x) hfg
    simp only [map_add, map_mul, map_sub, aeval_C, aeval_X] at h1
    rw [← h1, h0]
  have hgx : aeval x g = algebraMap S (AdjoinRoot f) (g.eval a₀) +
      (x - algebraMap S (AdjoinRoot f) a₀) * aeval x h := by
    have h1 := congrArg (aeval x) hgh
    simpa only [map_add, map_mul, map_sub, aeval_C, aeval_X] using h1
  -- The approximate idempotent `ε₀ = g(a₀)⁻¹ g(x)` of `A = S[X]/(f)`, idempotent modulo `𝔪_S A`.
  obtain ⟨ε₀, hε₀⟩ : ∃ ε : AdjoinRoot f, ε = v * aeval x g := ⟨_, rfl⟩
  have E1 : ε₀ * (x - algebraMap S (AdjoinRoot f) a₀) ∈ J := by
    have : ε₀ * (x - algebraMap S (AdjoinRoot f) a₀) =
        algebraMap S (AdjoinRoot f) (-((↑u⁻¹ : S) * f.eval a₀)) := by
      rw [map_neg, map_mul, ← hv]
      linear_combination v * hfx + (x - algebraMap S (AdjoinRoot f) a₀) * hε₀
    rw [this]
    exact Ideal.mem_map_of_mem _ (neg_mem (Ideal.mul_mem_left _ _ h₁))
  have E2 : ε₀ * ε₀ - ε₀ ∈ J := by
    have : ε₀ * ε₀ - ε₀ =
        (ε₀ * (x - algebraMap S (AdjoinRoot f) a₀)) * (v * aeval x h) := by
      linear_combination ε₀ * hε₀ + (ε₀ * v) * hgx + ε₀ * hvu
    rw [this]
    exact Ideal.mul_mem_right _ _ E1
  -- Lift `ε₀` to an idempotent `e` of `A`.
  obtain ⟨e, he, heε⟩ :=
    exists_isIdempotentElem_sub_mem_map_maximalIdeal_of_finite R S (A := AdjoinRoot f) ε₀ E2
  have F1 : e * (x - algebraMap S (AdjoinRoot f) a₀) ∈ J := by
    have : e * (x - algebraMap S (AdjoinRoot f) a₀) =
        (e - ε₀) * (x - algebraMap S (AdjoinRoot f) a₀) +
          ε₀ * (x - algebraMap S (AdjoinRoot f) a₀) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ heε) E1
  -- The residue point `φ : A → κ(S)`, `x ↦ a₀ mod 𝔪_S`.
  have hφ : f.eval₂ (residue S) (residue S a₀) = 0 := by
    rw [eval₂_at_apply, residue_eq_zero_iff]
    exact h₁
  let φ : AdjoinRoot f →+* ResidueField S := AdjoinRoot.lift (residue S) (residue S a₀) hφ
  have hφS : ∀ s : S, φ (algebraMap S (AdjoinRoot f) s) = residue S s := fun s => by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.lift_of hφ
  have hφx : φ x = residue S a₀ := AdjoinRoot.lift_root hφ
  have hφJ : ∀ z ∈ J, φ z = 0 := by
    have : J ≤ RingHom.ker φ := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro s hs
      rw [Ideal.mem_comap, RingHom.mem_ker, hφS, residue_eq_zero_iff]
      exact hs
    exact fun z hz => this hz
  have hφε : φ ε₀ = 1 := by
    rw [hε₀, map_mul, hv, hφS, hx, AdjoinRoot.aeval_eq, AdjoinRoot.lift_mk, eval₂_at_apply,
      ← map_mul, ← hu, Units.inv_mul, map_one]
  have hφe : φ e = 1 := by
    have h0 : φ (e - ε₀) = 0 := hφJ _ heε
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, hφε]
  -- The factor `B = A ⧸ (1 - e)`.
  set K : Ideal (AdjoinRoot f) := Ideal.span {1 - e} with hK
  let π : AdjoinRoot f →ₐ[S] AdjoinRoot f ⧸ K := Ideal.Quotient.mkₐ S K
  have hπe : π e = 1 := by
    have h0 : π (1 - e) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  have hBfin : Module.Finite S (AdjoinRoot f ⧸ K) :=
    Module.Finite.of_surjective π.toLinearMap Ideal.Quotient.mk_surjective
  set JB : Ideal (AdjoinRoot f ⧸ K) := (maximalIdeal S).map (algebraMap S (AdjoinRoot f ⧸ K))
    with hJB
  have hxB : π x - algebraMap S (AdjoinRoot f ⧸ K) a₀ ∈ JB := by
    have hmap : J.map (π : AdjoinRoot f →+* AdjoinRoot f ⧸ K) = JB := by
      rw [hJ, hJB, Ideal.map_map]
      congr 1
    have h1 : π (e * (x - algebraMap S (AdjoinRoot f) a₀)) ∈ JB := by
      rw [← hmap]
      exact Ideal.mem_map_of_mem _ F1
    rwa [map_mul, hπe, one_mul, map_sub, AlgHom.commutes] at h1
  -- Every element of `B` is congruent to a scalar modulo `𝔪_S B`.
  have hsurj : ∀ b : AdjoinRoot f ⧸ K, ∃ c : S, b - algebraMap S (AdjoinRoot f ⧸ K) c ∈ JB := by
    intro b
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    refine ⟨p.eval a₀, ?_⟩
    have hπp : Ideal.Quotient.mk K (AdjoinRoot.mk f p) = aeval (π x) p := by
      rw [hx, ← AdjoinRoot.aeval_eq, aeval_algHom_apply]
      rfl
    rw [hπp]
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub (π x) (algebraMap S (AdjoinRoot f ⧸ K) a₀)
      (p.map (algebraMap S (AdjoinRoot f ⧸ K)))
    rw [eval_map_algebraMap, eval_map_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval] at hc
    rw [hc]
    exact Ideal.mul_mem_right _ _ hxB
  -- Nakayama: `S → B` is surjective.
  have htop : (⊤ : Submodule S (AdjoinRoot f ⧸ K)) ≤
      LinearMap.range (Algebra.linearMap S (AdjoinRoot f ⧸ K)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal S) Module.Finite.fg_top
      (maximalIdeal_le_jacobson _) ?_
    intro b _
    obtain ⟨c, hc⟩ := hsurj b
    rw [Ideal.smul_top_eq_map]
    have hb : b = algebraMap S (AdjoinRoot f ⧸ K) c + (b - algebraMap S (AdjoinRoot f ⧸ K) c) := by
      ring
    rw [hb]
    exact Submodule.add_mem_sup ⟨c, rfl⟩ hc
  obtain ⟨a, ha⟩ : ∃ a : S, algebraMap S (AdjoinRoot f ⧸ K) a = π x :=
    htop (Submodule.mem_top (x := π x))
  -- `S → B` is injective: the power basis coordinates of `e` are not all in `𝔪_S`.
  have hinj : ∀ s : S, algebraMap S (AdjoinRoot f ⧸ K) s = 0 → s = 0 := by
    intro s hs
    have hsK : algebraMap S (AdjoinRoot f) s ∈ K := by
      rw [← π.commutes] at hs
      exact Ideal.Quotient.eq_zero_iff_mem.mp hs
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hsK
    have hse : s • e = 0 := by
      rw [Algebra.smul_def, ← hw]
      linear_combination (-w) * he.eq
    let pb := AdjoinRoot.powerBasis' hf
    have hrep : ∀ i, s * pb.basis.repr e i = 0 := by
      intro i
      have := congrArg (fun z => pb.basis.repr z i) hse
      simpa using this
    by_contra hs0
    have hall : ∀ i, pb.basis.repr e i ∈ maximalIdeal S := by
      intro i
      by_contra hi
      have hunit : IsUnit (pb.basis.repr e i) := by
        simpa [mem_maximalIdeal, mem_nonunits_iff] using hi
      exact hs0 ((hunit.mul_left_eq_zero).mp (hrep i))
    have heJ : e ∈ J := by
      rw [← pb.basis.sum_repr e]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hall i))
    have h0 := hφJ e heJ
    rw [hφe] at h0
    exact one_ne_zero h0
  refine ⟨a, ?_, ?_⟩
  · apply hinj
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval, ha, aeval_algHom_apply, hx,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  · have hK' : algebraMap S (AdjoinRoot f) a - x ∈ K := by
      rw [← Ideal.Quotient.eq]
      change π (algebraMap S (AdjoinRoot f) a) = π x
      rw [π.commutes, ha]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hK'
    have h0 := congrArg φ hw
    rw [map_mul, map_sub, map_one, hφe, sub_self, mul_zero, map_sub, hφS, hφx, eq_comm,
      sub_eq_zero] at h0
    rw [← residue_eq_zero_iff, map_sub, h0, sub_self]

end FiniteLocalHenselian

/-- **Stacks Project, Tag 04GH (2).** A local ring that is module-finite over a Henselian local
ring is Henselian. -/
theorem finiteLocalHenselian : FiniteLocalHenselianStatement.{u, v} := by
  intro R _ _ S _ _ _ _
  exact { is_henselian := fun f hf a₀ h₁ h₂ =>
    FiniteLocalHenselian.exists_isRoot_sub_mem_maximalIdeal R S f hf a₀ h₁ h₂ }

end Langlands.CommutativeAlgebra
