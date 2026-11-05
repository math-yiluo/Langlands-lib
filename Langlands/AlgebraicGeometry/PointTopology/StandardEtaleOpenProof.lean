import Langlands.AlgebraicGeometry.PointTopology.StandardEtaleOpenStatement
import Langlands.AlgebraicGeometry.PointTopology.SimpleRootContinuityProof
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.BigOperators.Fin

/-! # Standard etale point maps are open -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open Filter Polynomial
open scoped Topology BigOperators

namespace Langlands.AlgebraicGeometry.PointTopology

private theorem isOpenMap_of_local_sections
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (h : ∀ x, ∃ s : Y → X, s (f x) = x ∧ ContinuousAt s (f x) ∧
      ∀ᶠ y in 𝓝 (f x), f (s y) = y) : IsOpenMap f := by
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hc, hi⟩ := h x
  have hpre : ∀ᶠ y in 𝓝 (f x), s y ∈ U :=
    hc (by simpa only [hs] using hU.mem_nhds hx)
  filter_upwards [hpre, hi] with y hy he
  exact ⟨s y, hy, he⟩

private def pointMonicFamily {K : Type u} [CommRing K]
    (n : ℕ) (c : Fin n → K) : K[X] :=
  X ^ n + ∑ i : Fin n, C (c i) * X ^ i.val

variable {K : Type u} [NontriviallyNormedField K]
variable {A : Type v} [CommRing A] [Algebra K A]
variable {B : Type w} [CommRing B] [Algebra A B]

private theorem pointMonicFamily_eq_map (P : StandardEtalePresentation A B)
    (p : AlgPoint K A K) :
    pointMonicFamily P.f.natDegree (fun i => p (P.f.coeff i.val)) =
      P.f.map p.toAlgHom.toRingHom := by
  classical
  have h := congrArg (Polynomial.map p.toAlgHom.toRingHom) P.monic_f.as_sum
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C] at h
  change X ^ P.f.natDegree +
    ∑ i : Fin P.f.natDegree,
      C (p.toAlgHom.toRingHom (P.f.coeff i.val)) * X ^ i.val = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => C (p.toAlgHom.toRingHom (P.f.coeff i)) * X ^ i)]
  exact h.symm

private theorem standardEtalePoint_degree_pos (P : StandardEtalePresentation A B)
    (z : StandardEtalePointCoordinates (K := K) P) : 0 < P.f.natDegree := by
  by_contra h
  have hf := Polynomial.eq_one_of_monic_natDegree_zero P.monic_f (Nat.eq_zero_of_not_pos h)
  have hz := (congrArg
    (fun f : A[X] => f.eval₂ z.1.1.toAlgHom.toRingHom z.1.2) hf).symm.trans z.2.1
  simp only [Polynomial.eval₂_one] at hz
  exact one_ne_zero hz

private theorem standardEtalePoint_simple (P : StandardEtalePresentation A B)
    (z : StandardEtalePointCoordinates (K := K) P) :
    P.f.derivative.eval₂ z.1.1.toAlgHom.toRingHom z.1.2 ≠ 0 := by
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  intro hzero
  have h := congrArg (Polynomial.eval₂RingHom z.1.1.toAlgHom.toRingHom z.1.2) e
  simp only [map_add, map_mul, map_pow, Polynomial.coe_eval₂RingHom] at h
  rw [hzero, z.2.1, zero_mul, zero_mul, zero_add] at h
  exact pow_ne_zero n z.2.2 h.symm

private theorem standardEtaleCoordinate_local_section [CompleteSpace K]
    (P : StandardEtalePresentation A B)
    (z : StandardEtalePointCoordinates (K := K) P) :
    ∃ s : AlgPoint K A K → StandardEtalePointCoordinates (K := K) P,
      s z.1.1 = z ∧ ContinuousAt s z.1.1 ∧
      ∀ᶠ p in 𝓝 z.1.1, (s p).1.1 = p := by
  classical
  let c : AlgPoint K A K → (Fin P.f.natDegree → K) :=
    fun p i => p (P.f.coeff i.val)
  have hc : Continuous c :=
    continuous_pi (fun i => AlgPoint.continuous_eval (P.f.coeff i.val))
  have hpoly (p : AlgPoint K A K) :
      pointMonicFamily P.f.natDegree (c p) = P.f.map p.toAlgHom.toRingHom :=
    pointMonicFamily_eq_map P p
  have hroot : (pointMonicFamily P.f.natDegree (c z.1.1)).eval z.1.2 = 0 := by
    rw [hpoly, Polynomial.eval_map]
    exact z.2.1
  have hsimple :
      (pointMonicFamily P.f.natDegree (c z.1.1)).derivative.eval z.1.2 ≠ 0 := by
    rw [hpoly, Polynomial.derivative_map, Polynomial.eval_map]
    exact standardEtalePoint_simple P z
  obtain ⟨ψ, hψz, hψc, hψroot, _⟩ :=
    monicSimpleRootContinuity K P.f.natDegree (standardEtalePoint_degree_pos P z)
      (c z.1.1) z.1.2 hroot hsimple
  let r : AlgPoint K A K → K := fun p => ψ (c p)
  have hrz : r z.1.1 = z.1.2 := hψz
  have hrc : ContinuousAt r z.1.1 := hψc.comp hc.continuousAt
  have hf : ∀ᶠ p in 𝓝 z.1.1, P.f.eval₂ p.toAlgHom.toRingHom (r p) = 0 := by
    have he := hc.continuousAt.tendsto.eventually hψroot
    filter_upwards [he] with p hp
    have hp' : (pointMonicFamily P.f.natDegree (c p)).eval (r p) = 0 := hp.1
    rwa [hpoly, Polynomial.eval_map] at hp'
  have hgcont : ContinuousAt
      (fun p : AlgPoint K A K => P.g.eval₂ p.toAlgHom.toRingHom (r p)) z.1.1 :=
    (continuous_point_polynomial_eval (K := K) P.g).continuousAt.comp
      (continuousAt_id.prodMk hrc)
  have hg : ∀ᶠ p in 𝓝 z.1.1, P.g.eval₂ p.toAlgHom.toRingHom (r p) ≠ 0 :=
    hgcont.eventually_ne (by simpa only [hrz] using z.2.2)
  let valid (p : AlgPoint K A K) : Prop :=
    P.f.eval₂ p.toAlgHom.toRingHom (r p) = 0 ∧
      P.g.eval₂ p.toAlgHom.toRingHom (r p) ≠ 0
  have hz : valid z.1.1 := by
    dsimp only [valid]
    rw [hrz]
    exact z.2
  let s : AlgPoint K A K → StandardEtalePointCoordinates (K := K) P :=
    fun p => if h : valid p then ⟨(p, r p), h⟩ else z
  have hsnear : ∀ᶠ p in 𝓝 z.1.1, (s p).1 = (p, r p) := by
    filter_upwards [hf.and hg] with p hp
    change valid p at hp
    simp only [s, dite_eq_left hp]
  have hsz : s z.1.1 = z := by
    apply Subtype.ext
    simp only [s, dite_eq_left hz]
    exact Prod.ext rfl hrz
  refine ⟨s, hsz, ?_, ?_⟩
  · change Tendsto s (𝓝 z.1.1) (𝓝 (s z.1.1))
    rw [hsz, tendsto_subtype_rng]
    have ht : Tendsto (fun p : AlgPoint K A K => (p, r p))
        (𝓝 z.1.1) (𝓝 z.1) := by
      have ht : ContinuousAt (fun p : AlgPoint K A K => (p, r p)) z.1.1 :=
        continuousAt_id.prodMk hrc
      convert ht.tendsto using 1
      rw [hrz]
    exact ht.congr' (Filter.EventuallyEq.symm hsnear)
  · filter_upwards [hsnear] with p hp
    exact congrArg Prod.fst hp

/-- Restriction along a standard etale algebra presentation is open on actual points. -/
theorem standardEtalePointOpen : StandardEtalePointOpenStatement.{u, v, w} := by
  intro K _ _ A _ _ B _ _ _ _ P
  have hprojection : IsOpenMap
      (fun z : StandardEtalePointCoordinates (K := K) P => z.1.1) :=
    isOpenMap_of_local_sections _ (standardEtaleCoordinate_local_section P)
  exact hprojection.comp (standardEtalePointHomeomorph (K := K) P).isOpenMap

end Langlands.AlgebraicGeometry.PointTopology
