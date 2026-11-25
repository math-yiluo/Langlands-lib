import Langlands.GaloisCohomology.Global.BrauerSequence.FiniteComparison
import Langlands.GaloisCohomology.CompactSupport.TateModified.OrderTwo
import Mathlib.LinearAlgebra.Complex.Module
import Langlands.Cohomology.Profinite.Cup.Basic

/-!
# Local invariants of inflated classes at the infinite places

For an infinite place `w` of a number field `K`, `K̄_w` (Mathlib's `AlgebraicClosure w.Completion`)
is isomorphic to `ℂ` through an embedding extending `extensionEmbedding : K_w → ℂ`
(`closureToComplex`, `closureEquivComplex`). At a complex place `Gal(K̄_w/K_w)` is trivial and the local
Brauer group is zero (`subsingleton_realBrauerGroup_of_isComplex`); at a real place it has two
elements, `1` and the transported complex conjugation `closureConj` (`eq_one_or_eq_closureConj`), and
the class of a `2`-cocycle `z` vanishes exactly when `z(c, c) · z(1, 1)` is a norm, i.e. has positive
image in `ℂ` (`cohomologyπ_two_eq_zero_iff_of_orderTwo`, `exists_mul_closureConj_iff`). Hence the real
invariant of the class of `z` is the Library's sign class of that image (`realInvariant_cohomologyπ`).

For a finite Galois extension `E ⊆ Ω` of `K` and embeddings `ι`, the place `realPlace ι E w` of `E`
above `w` is the one of `E → K̄_w → ℂ`. The real local invariant of a class inflated from
`H²(Gal(E/K), Eˣ)` is the Library's `archimedeanInvariant` at that place
(`realLocalInvariant_unitsInflation`): both are computed from `f(c, c) · f(1, 1)` for a cocycle `f`,
`c` the image of the conjugation in `Gal(E/K)`.
-/

namespace Langlands.GaloisCohomology
open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open NumberField.InfinitePlace.Completion

universe u

noncomputable section

section OrderTwoCriterion

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{u} k G) [IsSmoothRep A]

omit [DiscreteTopology G] in
/-- `z(1, g) = z(1, 1)` for a `2`-cocycle. -/
theorem cochainOf_one_left (z : ProfiniteCohomology.cocycles A 2) (g : G) :
    cochainOf A (cocycleι A 2 z) ![1, g] = cochainOf A (cocycleι A 2 z) ![1, 1] := by
  have e := OrderTwo.cocycle_two A z 1 1 g
  simp only [one_mul, map_one, Module.End.one_apply] at e
  rw [← sub_eq_zero, ← e]
  abel

omit [DiscreteTopology G] in
/-- `z(g, 1) = g • z(1, 1)` for a `2`-cocycle. -/
theorem cochainOf_one_right (z : ProfiniteCohomology.cocycles A 2) (g : G) :
    cochainOf A (cocycleι A 2 z) ![g, 1] = A.ρ g (cochainOf A (cocycleι A 2 z) ![1, 1]) := by
  have e := OrderTwo.cocycle_two A z g 1 1
  simp only [mul_one] at e
  rw [eq_comm, ← sub_eq_zero, ← e]
  abel

omit [DiscreteTopology G] in
/-- For an involution `c`, `z(c, c) + z(1, 1)` is fixed by `c`. -/
theorem fixed_cochainOf_add {c : G} (hcc : c * c = 1) (z : ProfiniteCohomology.cocycles A 2) :
    A.ρ c (cochainOf A (cocycleι A 2 z) ![c, c] + cochainOf A (cocycleι A 2 z) ![1, 1]) =
      cochainOf A (cocycleι A 2 z) ![c, c] + cochainOf A (cocycleι A 2 z) ![1, 1] := by
  have e := OrderTwo.cocycle_two A z c c c
  rw [hcc, cochainOf_one_left A z c, cochainOf_one_right A z c] at e
  rw [map_add, ← sub_eq_zero, ← e]
  abel

/-- For a group `{1, c}` of order two, a `2`-cocycle `z` is a coboundary exactly when
`z(c, c) + z(1, 1)` is a norm `m + c • m`. -/
theorem cohomologyπ_two_eq_zero_iff_of_orderTwo {c : G} (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)
    (z : ProfiniteCohomology.cocycles A 2) :
    cohomologyπ A 2 z = 0 ↔ ∃ m : A,
      cochainOf A (cocycleι A 2 z) ![c, c] + cochainOf A (cocycleι A 2 z) ![1, 1] = m + A.ρ c m := by
  have hcc := OrderTwo.mul_self_eq_one hG hc
  set w := cochainOf A (cocycleι A 2 z) with hw
  have e1 : ∀ g, w ![1, g] = w ![1, 1] := fun g => by
    have e := OrderTwo.cocycle_two A z 1 1 g
    simp only [one_mul, map_one, Module.End.one_apply] at e
    rw [← hw] at e
    rw [← sub_eq_zero, ← e]
    abel
  have e2 : ∀ g, w ![g, 1] = A.ρ g (w ![1, 1]) := fun g => by
    have e := OrderTwo.cocycle_two A z g 1 1
    simp only [mul_one] at e
    rw [← hw] at e
    rw [eq_comm, ← sub_eq_zero, ← e]
    abel
  rw [OrderTwo.cohomologyπ_two_eq_zero_iff]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f c, ?_⟩
    rw [hw, hf c c, hf 1 1, hcc]
    simp only [map_one, Module.End.one_apply, one_mul]
    abel
  · rintro ⟨m, hm⟩
    classical
    refine ⟨fun g => if g = 1 then w ![1, 1] else m, fun g h => ?_⟩
    rw [← hw]
    rcases hG g with hg | hg <;> rcases hG h with hh | hh <;> rw [hg, hh]
    · simp
    · simp only [hc, ↓reduceIte, map_one, Module.End.one_apply, one_mul]
      rw [e1]; abel
    · simp only [hc, ↓reduceIte, mul_one]
      rw [e2]; abel
    · simp only [hc, hcc, ↓reduceIte]
      have : w ![c, c] = m + A.ρ c m - w ![1, 1] := by rw [← hm]; abel
      rw [this]; abel

/-- For the trivial group, every `2`-cocycle is a coboundary. -/
theorem cohomologyπ_two_eq_zero_of_forall_eq_one (hG : ∀ g : G, g = 1)
    (z : ProfiniteCohomology.cocycles A 2) : cohomologyπ A 2 z = 0 := by
  rw [OrderTwo.cohomologyπ_two_eq_zero_iff]
  refine ⟨fun _ => cochainOf A (cocycleι A 2 z) ![1, 1], fun g h => ?_⟩
  rw [hG g, hG h]
  simp

end OrderTwoCriterion

section Closure

variable {K : Type u} [Field K] [NumberField K] (w : InfinitePlace K)

/-- `ℂ` as an algebra over `K_w` through `extensionEmbedding`. -/
abbrev complexAlgebra : Algebra w.Completion ℂ := (extensionEmbedding w).toAlgebra

/-- An embedding `K̄_w → ℂ` extending `extensionEmbedding : K_w → ℂ`. -/
def closureToComplex : AlgebraicClosure w.Completion →+* ℂ :=
  letI := complexAlgebra w
  (IsAlgClosed.lift : AlgebraicClosure w.Completion →ₐ[w.Completion] ℂ).toRingHom

omit [NumberField K] in
/-- `closureToComplex` extends `extensionEmbedding`. -/
theorem closureToComplex_algebraMap (x : w.Completion) :
    closureToComplex w (algebraMap w.Completion (AlgebraicClosure w.Completion) x) =
      extensionEmbedding w x :=
  letI := complexAlgebra w
  (IsAlgClosed.lift : AlgebraicClosure w.Completion →ₐ[w.Completion] ℂ).commutes x

omit [NumberField K] in
/-- At a real place, `extensionEmbedding` takes real values. -/
theorem extensionEmbedding_im_eq_zero {w : InfinitePlace K} (hw : w.IsReal) (x : w.Completion) :
    (extensionEmbedding w x).im = 0 := by
  rw [← extensionEmbeddingOfIsReal_apply hw x, Complex.ofReal_im]

/-- `closureToComplex` is onto: at a real place its image contains `ℝ` and a square root of `-1`. -/
theorem closureToComplex_surjective : Function.Surjective (closureToComplex w) := by
  intro z
  by_cases hw : w.IsReal
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_root
      (Polynomial.X ^ 2 + 1 : Polynomial (AlgebraicClosure w.Completion)) (by
        rw [Polynomial.degree_add_eq_left_of_degree_lt] <;> simp)
    have hr2 : closureToComplex w r ^ 2 = -1 := by
      have := congrArg (closureToComplex w) hr.eq_zero
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        map_add, map_pow, map_one, map_zero] at this
      linear_combination this
    have hI : closureToComplex w r = Complex.I ∨ closureToComplex w r = -Complex.I := by
      have h : (closureToComplex w r - Complex.I) * (closureToComplex w r + Complex.I) = 0 := by
        ring_nf; rw [Complex.I_sq, hr2]; ring
      rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    obtain ⟨a, ha⟩ := surjective_extensionEmbeddingOfIsReal hw z.re
    obtain ⟨b, hb⟩ := surjective_extensionEmbeddingOfIsReal hw z.im
    have ha' : closureToComplex w (algebraMap _ _ a) = z.re := by
      rw [closureToComplex_algebraMap, ← extensionEmbeddingOfIsReal_apply hw, ha]
    have hb' : closureToComplex w (algebraMap _ _ b) = z.im := by
      rw [closureToComplex_algebraMap, ← extensionEmbeddingOfIsReal_apply hw, hb]
    rcases hI with hI | hI
    · refine ⟨algebraMap _ _ a + algebraMap _ _ b * r, ?_⟩
      rw [map_add, map_mul, ha', hb', hI, Complex.re_add_im]
    · refine ⟨algebraMap _ _ a - algebraMap _ _ b * r, ?_⟩
      rw [map_sub, map_mul, ha', hb', hI, mul_neg, sub_neg_eq_add, Complex.re_add_im]
  · obtain ⟨x, hx⟩ := (bijective_extensionEmbedding_of_isComplex
      (InfinitePlace.not_isReal_iff_isComplex.1 hw)).2 z
    exact ⟨algebraMap _ _ x, by rw [closureToComplex_algebraMap, hx]⟩

/-- `K̄_w ≅ ℂ`, extending `extensionEmbedding`. -/
def closureEquivComplex : AlgebraicClosure w.Completion ≃+* ℂ :=
  RingEquiv.ofBijective (closureToComplex w)
    ⟨(closureToComplex w).injective, closureToComplex_surjective w⟩

/-- `closureEquivComplex` is `closureToComplex`. -/
theorem closureEquivComplex_apply (x : AlgebraicClosure w.Completion) :
    closureEquivComplex w x = closureToComplex w x :=
  rfl


/-- Every automorphism of `K̄_w` over `K_w` becomes the identity or (at a real place) complex conjugation in `ℂ`. -/
theorem closureToComplex_comp_eq (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) :
    (∀ x, closureToComplex w (σ x) = closureToComplex w x) ∨
      (w.IsReal ∧ ∀ x, closureToComplex w (σ x) = starRingEnd ℂ (closureToComplex w x)) := by
  set e := closureEquivComplex w
  -- the conjugate of `σ` by `e`, an automorphism of `ℂ` fixing the image of `K_w`
  let f : ℂ →+* ℂ := (e.toRingHom.comp (σ : AlgebraicClosure w.Completion →+* _)).comp e.symm.toRingHom
  have hf : ∀ x, f (extensionEmbedding w x) = extensionEmbedding w x := fun x => by
    change e (σ (e.symm (extensionEmbedding w x))) = _
    have h1 : e.symm (extensionEmbedding w x) = algebraMap _ _ x :=
      e.symm_apply_eq.2 (closureToComplex_algebraMap w x).symm
    rw [h1, AlgEquiv.commutes, closureEquivComplex_apply, closureToComplex_algebraMap]
  have hfe : ∀ x, closureToComplex w (σ x) = f (closureToComplex w x) := fun x => by
    change _ = e (σ (e.symm (e x)))
    rw [RingEquiv.symm_apply_apply]
    rfl
  by_cases hw : w.IsReal
  · let F : ℂ →ₐ[ℝ] ℂ :=
      { f with
        commutes' := fun r => by
          obtain ⟨a, ha⟩ := surjective_extensionEmbeddingOfIsReal hw r
          change f r = r
          rw [← ha, extensionEmbeddingOfIsReal_apply hw, hf] }
    rcases Complex.real_algHom_eq_id_or_conj F with h | h
    · left
      intro x
      rw [hfe]
      exact congrArg (fun φ : ℂ →ₐ[ℝ] ℂ => φ (closureToComplex w x)) h
    · right
      refine ⟨hw, fun x => ?_⟩
      rw [hfe]
      exact congrArg (fun φ : ℂ →ₐ[ℝ] ℂ => φ (closureToComplex w x)) h
  · left
    intro x
    rw [hfe]
    obtain ⟨y, hy⟩ := (bijective_extensionEmbedding_of_isComplex
      (InfinitePlace.not_isReal_iff_isComplex.1 hw)).2 (closureToComplex w x)
    rw [← hy, hf]

/-- At a real place, complex conjugation transported to `K̄_w`. -/
def closureConj (hw : w.IsReal) : Gal(AlgebraicClosure w.Completion/w.Completion) :=
  { ((closureEquivComplex w).trans (starRingAut (R := ℂ))).trans (closureEquivComplex w).symm with
    commutes' := fun x => by
      change (closureEquivComplex w).symm (starRingEnd ℂ (closureToComplex w (algebraMap _ _ x))) = _
      rw [closureToComplex_algebraMap, ← extensionEmbeddingOfIsReal_apply hw, Complex.conj_ofReal,
        extensionEmbeddingOfIsReal_apply hw, RingEquiv.symm_apply_eq, closureEquivComplex_apply,
        closureToComplex_algebraMap] }

/-- `closureConj` becomes complex conjugation in `ℂ`. -/
theorem closureToComplex_closureConj (hw : w.IsReal) (x : AlgebraicClosure w.Completion) :
    closureToComplex w (closureConj w hw x) = starRingEnd ℂ (closureToComplex w x) := by
  change closureEquivComplex w ((closureEquivComplex w).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- `closureConj` is not the identity. -/
theorem closureConj_ne_one (hw : w.IsReal) : closureConj w hw ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := closureToComplex_surjective w Complex.I
  have := closureToComplex_closureConj w hw x
  rw [h, AlgEquiv.one_apply, hx, Complex.conj_I] at this
  exact absurd (congrArg Complex.im this) (by norm_num)

/-- At a real place `Gal(K̄_w/K_w) = {1, closureConj}`. -/
theorem eq_one_or_eq_closureConj (hw : w.IsReal) (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) :
    σ = 1 ∨ σ = closureConj w hw := by
  rcases closureToComplex_comp_eq w σ with h | ⟨-, h⟩
  · left
    exact AlgEquiv.ext fun x => (closureToComplex w).injective (h x)
  · right
    exact AlgEquiv.ext fun x => (closureToComplex w).injective ((h x).trans
      (closureToComplex_closureConj w hw x).symm)

/-- At a complex place `Gal(K̄_w/K_w)` is trivial. -/
theorem eq_one_of_isComplex (hw : w.IsComplex) (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) :
    σ = 1 := by
  rcases closureToComplex_comp_eq w σ with h | ⟨h', -⟩
  · exact AlgEquiv.ext fun x => (closureToComplex w).injective (h x)
  · exact absurd h' (InfinitePlace.not_isReal_iff_isComplex.2 hw)

/-- `Gal(K̄_w/K_w)` is finite. -/
instance finite_closureGalois : Finite Gal(AlgebraicClosure w.Completion/w.Completion) := by
  classical
  refine Finite.of_injective (fun σ => decide (σ = 1)) fun σ τ h => ?_
  by_cases hw : w.IsReal
  · rcases eq_one_or_eq_closureConj w hw σ with rfl | rfl <;>
      rcases eq_one_or_eq_closureConj w hw τ with rfl | rfl <;> simp_all [closureConj_ne_one w hw]
  · rw [eq_one_of_isComplex w (InfinitePlace.not_isReal_iff_isComplex.1 hw) σ,
      eq_one_of_isComplex w (InfinitePlace.not_isReal_iff_isComplex.1 hw) τ]

/-- `Gal(K̄_w/K_w)` is discrete. -/
instance discreteTopology_closureGalois :
    DiscreteTopology Gal(AlgebraicClosure w.Completion/w.Completion) :=
  inferInstance


/-- At a real place, a unit of `K̄_w` fixed by conjugation is a norm `m · c(m)` exactly when its
image in `ℂ` is positive. -/
theorem exists_mul_closureConj_iff (hw : w.IsReal) (x : (AlgebraicClosure w.Completion)ˣ)
    (hx : closureConj w hw (x : AlgebraicClosure w.Completion) = x) :
    (∃ m : (AlgebraicClosure w.Completion)ˣ,
        (x : AlgebraicClosure w.Completion) = m * closureConj w hw (m : AlgebraicClosure w.Completion)) ↔
      0 < (closureToComplex w x).re := by
  have hreal : (closureToComplex w x).im = 0 := by
    have h := closureToComplex_closureConj w hw x
    rw [hx] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  constructor
  · rintro ⟨m, hm⟩
    rw [hm, map_mul, closureToComplex_closureConj, Complex.mul_conj]
    have hm0 : closureToComplex w m ≠ 0 := (map_ne_zero _).2 m.ne_zero
    rw [Complex.ofReal_re]
    exact Complex.normSq_pos.2 hm0
  · intro hpos
    obtain ⟨s, hs⟩ := closureToComplex_surjective w (Real.sqrt (closureToComplex w x).re)
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [map_zero] at hs
      have := congrArg Complex.re hs
      rw [Complex.zero_re, Complex.ofReal_re] at this
      exact absurd this.symm (Real.sqrt_pos.2 hpos).ne'
    refine ⟨Units.mk0 s hs0, (closureToComplex w).injective ?_⟩
    rw [Units.val_mk0, map_mul, closureToComplex_closureConj, hs, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hpos.le]
    exact (Complex.ext rfl (by rw [hreal, Complex.ofReal_im]))

end Closure

section RealInvariant

variable {K : Type u} [Field K] [NumberField K] (w : InfinitePlace K)

/-- At a complex place the local Brauer group is zero. -/
theorem subsingleton_realBrauerGroup_of_isComplex (hw : w.IsComplex) :
    Subsingleton (RealBrauerGroup w) := by
  refine ⟨fun y y' => ?_⟩
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 2 y
  obtain ⟨z', rfl⟩ := cohomologyπ_surjective _ 2 y'
  rw [cohomologyπ_two_eq_zero_of_forall_eq_one _ (eq_one_of_isComplex w hw),
    cohomologyπ_two_eq_zero_of_forall_eq_one _ (eq_one_of_isComplex w hw)]

/-- At a real place, the invariant of the class of a `2`-cocycle `z` is the sign class of the image
in `ℂ` of `z(c, c) · z(1, 1)`, `c` the conjugation. -/
theorem realInvariant_cohomologyπ (hw : w.IsReal)
    (z : ProfiniteCohomology.cocycles (unitsModule w.Completion (AlgebraicClosure w.Completion)) 2) :
    realInvariant w (cohomologyπ _ 2 z) =
      Langlands.ClassFieldTheory.Global.Reciprocity.signClass (closureToComplex w ((Additive.toMul
        (cochainOf _ (cocycleι _ 2 z) ![closureConj w hw, closureConj w hw] +
          cochainOf _ (cocycleι _ 2 z) ![1, 1]) : (AlgebraicClosure w.Completion)ˣ) :
            AlgebraicClosure w.Completion)) := by
  classical
  set c := closureConj w hw with hc_def
  set A := unitsModule w.Completion (AlgebraicClosure w.Completion)
  set y : A := cochainOf A (cocycleι A 2 z) ![c, c] + cochainOf A (cocycleι A 2 z) ![1, 1] with hy
  have hcc : c * c = 1 := OrderTwo.mul_self_eq_one (eq_one_or_eq_closureConj w hw) (closureConj_ne_one w hw)
  have hfix : A.ρ c y = y := fixed_cochainOf_add A hcc z
  have hfix' : c ((Additive.toMul y : (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion) =
      ((Additive.toMul y : (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion) :=
    congrArg (fun t : A => ((Additive.toMul t : (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion)) hfix
  have hcrit := cohomologyπ_two_eq_zero_iff_of_orderTwo A (eq_one_or_eq_closureConj w hw)
    (closureConj_ne_one w hw) z
  have hnorm := exists_mul_closureConj_iff w hw (Additive.toMul y) hfix'
  have hiff : cohomologyπ A 2 z = 0 ↔ 0 < (closureToComplex w (Additive.toMul y : (AlgebraicClosure w.Completion)ˣ)).re := by
    rw [hcrit, ← hnorm]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨Additive.toMul m, ?_⟩
      exact congrArg (fun t : A => ((Additive.toMul t : (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion)) hm
    · rintro ⟨m, hm⟩
      refine ⟨Additive.ofMul m, ?_⟩
      apply Additive.toMul.injective
      apply Units.ext
      exact hm
  have hne : (closureToComplex w (Additive.toMul y : (AlgebraicClosure w.Completion)ˣ)).re ≠ 0 := by
    intro h0
    have him : (closureToComplex w (Additive.toMul y : (AlgebraicClosure w.Completion)ˣ)).im = 0 := by
      have h := closureToComplex_closureConj w hw (Additive.toMul y : (AlgebraicClosure w.Completion)ˣ)
      rw [hfix'] at h
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    exact ((map_ne_zero _).2 (Additive.toMul y).ne_zero) (Complex.ext h0 him)
  unfold realInvariant Langlands.ClassFieldTheory.Global.Reciprocity.signClass
  by_cases h : cohomologyπ A 2 z = 0
  · rw [ite_eq_left h, ite_eq_right (not_lt.2 (hiff.1 h).le)]
  · rw [ite_eq_right h, ite_eq_left (lt_of_le_of_ne (not_lt.1 (fun hp => h (hiff.2 hp))) hne)]

end RealInvariant

section Comparison

open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
  [NumberField E] (w : InfinitePlace K)

/-- The embedding `E → K̄_w` of `ι`. -/
abbrev realPlaceEmbedding : E →ₐ[K] AlgebraicClosure w.Completion := (ι.infinite w).comp E.val

/-- The complex embedding `E → K̄_w → ℂ` of `ι`. -/
def realComplexEmbedding : E →+* ℂ := (closureToComplex w).comp (realPlaceEmbedding ι E w).toRingHom

/-- The infinite place of `E` above `w` determined by `ι`. -/
def realPlace : InfinitePlace E := InfinitePlace.mk (realComplexEmbedding ι E w)

omit [FiniteDimensional K ↥E] [NumberField ↥E] in
/-- The image in `Gal(E/K)` of `σ ∈ Gal(K̄_w/K_w)` is `σ` transported along the embedding of `ι`. -/
theorem realPlaceEmbedding_restrictNormal (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) (x : E) :
    realPlaceEmbedding ι E w (AlgEquiv.restrictNormalHom E (decompositionHom w.Completion (ι.infinite w) σ) x) =
      σ (realPlaceEmbedding ι E w x) := by
  have h1 := AlgEquiv.restrictNormal_commutes (decompositionHom w.Completion (ι.infinite w) σ) E x
  change ι.infinite w (algebraMap E Ω
    (AlgEquiv.restrictNormalHom E (decompositionHom w.Completion (ι.infinite w) σ) x)) =
      σ (ι.infinite w (algebraMap E Ω x))
  erw [h1]
  exact decompositionHom_apply (ι.infinite w) σ (algebraMap E Ω x)


/-- The image of `σ ∈ Gal(K̄_w/K_w)` in `Gal(E/K)`. -/
abbrev realRestrict (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) : Gal(E/K) :=
  AlgEquiv.restrictNormalHom E (decompositionHom w.Completion (ι.infinite w) σ)

omit [FiniteDimensional K ↥E] [NumberField ↥E] in
/-- The complex embedding of `ι` intertwines the image of `σ` with `σ`. -/
theorem realComplexEmbedding_realRestrict (σ : Gal(AlgebraicClosure w.Completion/w.Completion)) (x : E) :
    realComplexEmbedding ι E w (realRestrict ι E w σ x) =
      closureToComplex w (σ (realPlaceEmbedding ι E w x)) :=
  congrArg (closureToComplex w) (realPlaceEmbedding_restrictNormal ι E w σ x)

omit [FiniteDimensional K ↥E] [NumberField ↥E] in
/-- At a real place, the image of the conjugation becomes complex conjugation. -/
theorem realComplexEmbedding_realRestrict_closureConj (hw : w.IsReal) (x : E) :
    realComplexEmbedding ι E w (realRestrict ι E w (closureConj w hw) x) =
      starRingEnd ℂ (realComplexEmbedding ι E w x) := by
  rw [realComplexEmbedding_realRestrict, closureToComplex_closureConj]
  rfl

omit [IsSepClosure K Ω] [FiniteDimensional K ↥E] [IsGalois K ↥E] [NumberField ↥E] in
/-- On `K` the complex embedding of `ι` is the embedding of `w`. -/
theorem realComplexEmbedding_comp_algebraMap :
    (realComplexEmbedding ι E w).comp (algebraMap K E) = w.embedding := by
  ext x
  change closureToComplex w (ι.infinite w (algebraMap E Ω (algebraMap K E x))) = _
  rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes,
    IsScalarTower.algebraMap_apply K w.Completion (AlgebraicClosure w.Completion),
    closureToComplex_algebraMap, InfinitePlace.Completion.algebraMap_apply,
    extensionEmbedding_coe]
  rfl

omit [FiniteDimensional K ↥E] [NumberField ↥E] in
/-- The image of `1` is `1`. -/
theorem realRestrict_one : realRestrict ι E w 1 = 1 := by
  simp [realRestrict]

omit [NumberField ↥E] in
/-- The local invariant at an infinite place of a class inflated from `E` is the Library's
archimedean invariant at the place of `E` determined by `ι`. -/
theorem realLocalInvariant_unitsInflation (a : relativeCohomology K E 2) :
    realLocalInvariant ι w ((unitsInflation E 2).hom a) =
      Reciprocity.archimedeanInvariant (realPlace ι E w) a := by
  classical
  obtain ⟨f, rfl⟩ := Reciprocity.H2π_surjective a
  rw [Reciprocity.archimedeanInvariant, Reciprocity.H2Lift_H2π]
  obtain ⟨wc, hwc, hval⟩ := exists_cocycle_relativeToContinuous_H2π K E Ω f
  have hinf : (unitsInflation E 2).hom (groupCohomology.H2π _ f) = cohomologyπ _ 2 wc := by
    rw [hwc, ← unitsModuleContinuousEquiv_unitsInflation, LinearEquiv.symm_apply_apply]
  have hloc : realBrauerLocalization ι w 2 (cohomologyπ _ 2 wc) =
      cohomologyπ _ 2 (cocyclesMap (decompositionHom w.Completion (ι.infinite w))
        (realUnitsLocalHom ι w) 2 wc) :=
    map_cohomologyπ _ _ wc
  set z := cocyclesMap (decompositionHom w.Completion (ι.infinite w)) (realUnitsLocalHom ι w) 2 wc
    with hz_def
  have hz : ∀ g h, ((Additive.toMul (cochainOf _ (cocycleι _ 2 z) ![g, h]) :
      (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion) =
      realPlaceEmbedding ι E w ((Additive.toMul (f (realRestrict ι E w g, realRestrict ι E w h)) : Eˣ) : E) := by
    intro g h
    rw [hz_def, cochainOf_cocycleι_cocyclesMap]
    change ι.infinite w ((Additive.toMul (cochainOf _ (cocycleι _ 2 wc) _) : Ωˣ) : Ω) = _
    rw [hval]
    rfl
  have hemb : ∀ y : E, Reciprocity.signClass ((realPlace ι E w).embedding y) =
      Reciprocity.signClass (realComplexEmbedding ι E w y) := by
    intro y
    rcases InfinitePlace.mk_eq_iff.1 ((realPlace ι E w).mk_embedding) with h | h
    · rw [h]
    · rw [← h, Reciprocity.signClass_conjugate]
  rw [realLocalInvariant, hinf, hloc]
  by_cases hw : w.IsReal
  · rw [realInvariant_cohomologyπ w hw z]
    set d := realRestrict ι E w (closureConj w hw) with hd
    have hv : closureToComplex w ((Additive.toMul
        (cochainOf _ (cocycleι _ 2 z) ![closureConj w hw, closureConj w hw] +
          cochainOf _ (cocycleι _ 2 z) ![1, 1]) : (AlgebraicClosure w.Completion)ˣ) :
            AlgebraicClosure w.Completion) =
        realComplexEmbedding ι E w (Reciprocity.conjugationValue d f : E) := by
      change closureToComplex w (((Additive.toMul (cochainOf _ (cocycleι _ 2 z)
          ![closureConj w hw, closureConj w hw]) : (AlgebraicClosure w.Completion)ˣ) :
            AlgebraicClosure w.Completion) * ((Additive.toMul (cochainOf _ (cocycleι _ 2 z) ![1, 1]) :
              (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion)) = _
      rw [hz, hz, realRestrict_one, ← map_mul]
      rfl
    rw [hv]
    have hconj : ∀ x : E, realComplexEmbedding ι E w (d x) = starRingEnd ℂ (realComplexEmbedding ι E w x) :=
      realComplexEmbedding_realRestrict_closureConj ι E w hw
    by_cases hd1 : d = 1
    · rw [Reciprocity.archimedeanCocycleHom_apply_of_not_exists]
      · have hreal : ∀ x : E, starRingEnd ℂ (realComplexEmbedding ι E w x) = realComplexEmbedding ι E w x :=
          fun x => by rw [← hconj, hd1, AlgEquiv.one_apply]
        set y : E := ((Additive.toMul (f (1, 1)) : Eˣ) : E) with hy
        have hcv : (Reciprocity.conjugationValue d f : E) = y * y := by
          rw [hd1]
          rfl
        have hy0 : realComplexEmbedding ι E w y ≠ 0 := (map_ne_zero _).2 (Additive.toMul (f (1, 1))).ne_zero
        have him : (realComplexEmbedding ι E w y).im = 0 := by
          have := congrArg Complex.im (hreal y)
          rw [Complex.conj_im] at this
          linarith
        rw [hcv, map_mul, Reciprocity.signClass, ite_eq_right]
        rw [Complex.mul_re, him, mul_zero, sub_zero, not_lt]
        exact mul_self_nonneg _
      · rintro ⟨c, hc, hc1⟩
        rcases (InfinitePlace.mem_stabilizer_mk_iff _ c).1 hc with h | h
        · exact hc1 h
        · apply hc1
          refine AlgEquiv.ext fun x => (realComplexEmbedding ι E w).injective ?_
          rw [AlgEquiv.one_apply, h.eq]
          change starRingEnd ℂ _ = _
          rw [← hconj, hd1, AlgEquiv.one_apply]
    · have hdstab : d ∈ MulAction.stabilizer (E ≃ₐ[K] E) (realPlace ι E w) :=
        (InfinitePlace.mem_stabilizer_mk_iff _ d).2 (Or.inr (by
          ext x
          rw [ComplexEmbedding.conjugate_coe_eq]
          exact (hconj x).symm))
      rw [Reciprocity.archimedeanCocycleHom_apply_of_mem hdstab hd1, hemb]
  · have hwc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have := subsingleton_realBrauerGroup_of_isComplex w hwc
    rw [Subsingleton.elim (cohomologyπ _ 2 z) 0, realInvariant_zero,
      Reciprocity.archimedeanCocycleHom_apply_of_not_exists]
    rintro ⟨c, hc, hc1⟩
    rcases (InfinitePlace.mem_stabilizer_mk_iff _ c).1 hc with h | h
    · exact hc1 h
    · apply hw
      have hr := h.isReal_comp
      rw [realComplexEmbedding_comp_algebraMap] at hr
      exact InfinitePlace.isReal_iff.2 hr

end Comparison

end

end Langlands.GaloisCohomology
