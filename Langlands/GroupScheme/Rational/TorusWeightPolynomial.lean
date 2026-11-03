import Langlands.GroupScheme.Rational.TorusWeightSmooth
import Langlands.CommutativeAlgebra.GradedFormallySmoothPolynomial

/-! # Polynomial coordinate algebras of cyclic weight subgroups -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.Corepresented

section Tail

variable {Λ : Type*} [AddCommMonoid Λ]

/-- The cyclic tail `{n • a : n ≥ r, n > 0}` of a character. -/
def cyclicTail (a : Λ) (r : ℕ) : AddSubsemigroup Λ where
  carrier := {χ | ∃ n : ℕ, r ≤ n ∧ 0 < n ∧ n • a = χ}
  add_mem' := by
    rintro χ ψ ⟨n, hn, hn0, rfl⟩ ⟨m, _, _, rfl⟩
    exact ⟨n + m, by omega, by omega, add_nsmul a n m⟩

theorem mem_cyclicTail (a : Λ) (r : ℕ) (χ : Λ) :
    χ ∈ cyclicTail a r ↔ ∃ n : ℕ, r ≤ n ∧ 0 < n ∧ n • a = χ :=
  Iff.rfl

end Tail

section Lattice

variable {I : Type u}

/-- Multiples of a nonzero exponent vector are distinct. -/
theorem nsmul_left_injective_of_ne_zero {a : I → ℤ} (ha : a ≠ 0) :
    Function.Injective fun n : ℕ => n • a := by
  intro n m h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have h' := congrFun h i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h' hi
  exact_mod_cast mul_right_cancel₀ hi h'

theorem zero_notMem_cyclicTail {a : I → ℤ} (ha : a ≠ 0) (r : ℕ) :
    (0 : I → ℤ) ∉ cyclicTail a r := by
  rintro ⟨n, -, hn, h⟩
  have h' : n • a = (0 : ℕ) • a := by rw [h, zero_nsmul]
  exact hn.ne' (nsmul_left_injective_of_ne_zero ha h')

theorem mem_insertZero_cyclicTail {a : I → ℤ} (ha : a ≠ 0) (r : ℕ) (n : ℕ) :
    n • a ∈ insertZero (cyclicTail a r) ↔ n = 0 ∨ r ≤ n := by
  rw [mem_insertZero]
  constructor
  · rintro (h | ⟨m, hm, -, h⟩)
    · left
      exact nsmul_left_injective_of_ne_zero ha (show n • a = (0 : ℕ) • a by rw [h, zero_nsmul])
    · right
      rwa [← nsmul_left_injective_of_ne_zero ha h]
  · rintro (rfl | h)
    · left
      exact zero_nsmul a
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · left
        exact zero_nsmul a
      · right
        exact ⟨n, h, hn, rfl⟩

end Lattice

section Quotient

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

variable (P : AddSubsemigroup (I → ℤ))

/-- The corepresentation of a weight subgroup by the quotient by its weight ideal. -/
abbrev weightCorep :
    (cutFunctor (isCutOutBy_weightIdeal e σ P) ⋙ forget GrpCat).CorepresentableBy
      (quotientAlgebra (weightIdeal e σ P)) :=
  cutCorepresentableBy (isCutOutBy_weightIdeal e σ P)

/-- The torus action restricted to a weight subgroup. -/
abbrev weightAction : TorusAction (cutFunctor (isCutOutBy_weightIdeal e σ P)) I :=
  σ.restrict (isCutOutBy_weightIdeal e σ P) fun t _ hx => act_mem_weightSubgroup e σ P t hx

/-- On the coordinate algebra of `U_P`, the weight components outside `{0} ∪ P` vanish. -/
theorem comp_weightAction_eq_zero {m : I → ℤ} (hm : m ∉ insertZero P) (f : B) :
    comp (weightCorep e σ P) (weightAction e σ P) m (Ideal.Quotient.mk _ f) = 0 := by
  rw [comp_restrict, Ideal.Quotient.eq_zero_iff_mem]
  have hm0 : m ≠ 0 := fun h => hm ((mem_insertZero P m).2 (Or.inl h))
  have hmP : m ∉ P := fun h => hm ((mem_insertZero P m).2 (Or.inr h))
  have h : comp e σ m f - algebraMap R B (AffineLinearEmbedding.counit e (comp e σ m f)) ∈ weightIdeal e σ P :=
    Ideal.subset_span ⟨f, m, hmP, rfl⟩
  simp only [counit_comp, hm0, ↓reduceIte, map_zero, sub_zero] at h
  exact h

/-- If `0 ∉ P`, the weight-zero components on the coordinate algebra of `U_P` are scalars. -/
theorem comp_zero_weightAction (h0 : (0 : I → ℤ) ∉ P) (f : B) :
    comp (weightCorep e σ P) (weightAction e σ P) 0 (Ideal.Quotient.mk _ f) =
      algebraMap R (B ⧸ weightIdeal e σ P) (AffineLinearEmbedding.counit e (comp e σ 0 f)) := by
  rw [comp_restrict, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
  exact Ideal.subset_span ⟨f, 0, h0, rfl⟩

theorem mem_insertZero_of_comp_weightAction_ne_zero {m : I → ℤ}
    (g : B ⧸ weightIdeal e σ P)
    (hg : comp (weightCorep e σ P) (weightAction e σ P) m g ≠ 0) : m ∈ insertZero P := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  by_contra hm
  exact hg (comp_weightAction_eq_zero e σ P hm f)

/-- If `0 ∉ P`, homogeneous elements of weight zero on the coordinate algebra of `U_P` are
scalars. -/
theorem exists_algebraMap_of_isHomogeneous_zero (h0 : (0 : I → ℤ) ∉ P)
    {g : B ⧸ weightIdeal e σ P}
    (hg : IsHomogeneous (weightCorep e σ P) (weightAction e σ P) 0 g) :
    ∃ c : R, algebraMap R (B ⧸ weightIdeal e σ P) c = g := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  exact ⟨_, (comp_zero_weightAction e σ P h0 f).symm.trans hg.comp_self⟩

/-- The counit factors through the coordinate algebra of `U_P`. -/
def weightCounit : B ⧸ weightIdeal e σ P →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (AffineLinearEmbedding.counit e) fun b hb => by
    have h : (1 : F.obj (CommAlgCat.of R R)) ∈ weightSubgroup e σ P (CommAlgCat.of R R) :=
      Subgroup.one_mem _
    exact (isCutOutBy_weightIdeal e σ P _ 1).1 h b hb

end Quotient

section Field

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

/-- The coordinate algebra of a cyclic weight subgroup is a polynomial algebra on homogeneous
generators whose weights are multiples `d • a` with `d ≥ r`, if the representing algebra is
formally smooth and of finite type. -/
theorem exists_aeval_bijective_cyclicTail [Algebra.FormallySmooth k B] [Algebra.FiniteType k B]
    {a : I → ℤ} (ha : a ≠ 0) (r : ℕ) :
    ∃ (n : ℕ) (d : Fin n → ℕ) (x : Fin n → B ⧸ weightIdeal e σ (cyclicTail a r)),
      (∀ i, 0 < d i) ∧ (∀ i, r ≤ d i) ∧
      (∀ i, IsHomogeneous (weightCorep e σ (cyclicTail a r))
        (weightAction e σ (cyclicTail a r)) (d i • a) (x i)) ∧
      Function.Bijective
        (MvPolynomial.aeval x : MvPolynomial (Fin n) k →ₐ[k] B ⧸ weightIdeal e σ (cyclicTail a r)) := by
  set P := cyclicTail a r
  have h0 : (0 : I → ℤ) ∉ P := zero_notMem_cyclicTail ha r
  have hφ : Function.Injective (multiplesHom (I → ℤ) a) := nsmul_left_injective_of_ne_zero ha
  have hsupp : ∀ (g : B ⧸ weightIdeal e σ P) m,
      comp (weightCorep e σ P) (weightAction e σ P) m g ≠ 0 →
        m ∈ Set.range (multiplesHom (I → ℤ) a) := by
    intro g m hg
    rcases (mem_insertZero P m).1 (mem_insertZero_of_comp_weightAction_ne_zero e σ P g hg) with
      rfl | ⟨n, -, -, rfl⟩
    · exact ⟨0, zero_nsmul a⟩
    · exact ⟨n, rfl⟩
  let _ := gradedAlgebra (weightCorep e σ P) (weightAction e σ P) hφ hsupp
  have : Algebra.FormallySmooth k (B ⧸ weightIdeal e σ P) :=
    formallySmooth_quotient_weightIdeal e σ P h0
  have : Nontrivial (B ⧸ weightIdeal e σ P) :=
    RingHom.domain_nontrivial (weightCounit e σ P).toRingHom
  have hdeg0 : homogeneousSubmodule (weightCorep e σ P) (weightAction e σ P)
      (multiplesHom (I → ℤ) a 0) =
        LinearMap.range (Algebra.linearMap k (B ⧸ weightIdeal e σ P)) := by
    ext g
    rw [map_zero, mem_homogeneousSubmodule]
    constructor
    · intro hg
      obtain ⟨c, hc⟩ := exists_algebraMap_of_isHomogeneous_zero e σ P h0 hg
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      exact isHomogeneous_algebraMap (weightCorep e σ P) (weightAction e σ P) c
  obtain ⟨n, d, x, hd, hx, hbij⟩ :=
    Langlands.Algebra.GradedFormallySmooth.exists_homogeneous_aeval_bijective
      (k := k) (C := B ⧸ weightIdeal e σ P)
      (fun i => homogeneousSubmodule (weightCorep e σ P) (weightAction e σ P)
        (multiplesHom (I → ℤ) a i)) hdeg0
  refine ⟨n, d, x, hd, fun i => ?_, hx, hbij⟩
  have hxi : x i ≠ 0 := by
    intro h
    have h1 : (MvPolynomial.aeval x : MvPolynomial (Fin n) k →ₐ[k] B ⧸ weightIdeal e σ P)
        (MvPolynomial.X i) =
          (MvPolynomial.aeval x : MvPolynomial (Fin n) k →ₐ[k] B ⧸ weightIdeal e σ P) 0 := by
      rw [MvPolynomial.aeval_X, h, map_zero]
    exact MvPolynomial.X_ne_zero i (hbij.1 h1)
  have hcomp : comp (weightCorep e σ P) (weightAction e σ P) (d i • a) (x i) ≠ 0 := by
    have hxi' : IsHomogeneous (weightCorep e σ P) (weightAction e σ P) (d i • a) (x i) := hx i
    rw [hxi'.comp_self]
    exact hxi
  have hmem := mem_insertZero_of_comp_weightAction_ne_zero e σ P (x i) hcomp
  rcases (mem_insertZero_cyclicTail ha r (d i)).1 hmem with h | h
  · exact absurd h (hd i).ne'
  · exact h

end Field

section Span

variable {k C ι : Type*} [CommRing k] [CommRing C] [Algebra k C]
  (𝒜 : ℕ → Submodule k C) [GradedAlgebra 𝒜]

/-- In an algebra generated by homogeneous elements of degrees at least `r > 0`, the
homogeneous elements of degree `r` are linear combinations of the generators of degree `r`. -/
theorem mem_span_of_mem_graded {x : ι → C} {d : ι → ℕ} (hx : ∀ i, x i ∈ 𝒜 (d i))
    (hsurj : Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι k →ₐ[k] C))
    {r : ℕ} (hr0 : 0 < r) (hr : ∀ i, r ≤ d i) {g : C} (hg : g ∈ 𝒜 r) :
    g ∈ Submodule.span k (x '' {i | d i = r}) := by
  classical
  obtain ⟨p, rfl⟩ := hsurj g
  have h1 := Langlands.Algebra.GradedFormallySmooth.decompose_aeval 𝒜 hx p r
  rw [DirectSum.decompose_of_mem_same 𝒜 hg] at h1
  rw [h1, MvPolynomial.weightedHomogeneousComponent_apply, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmw : Finsupp.weight d m = r := (Finset.mem_filter.mp hm).2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero] at hmw
    exact hr0.ne hmw
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hm0 (Finsupp.ext h)
  have hle : Finsupp.weight d m ≤ d i := hmw ▸ hr i
  have hmi := Langlands.Algebra.GradedFormallySmooth.eq_single_of_weight_le
    (w := d) (fun j => hr0.trans_le (hr j)) hi hle
  subst hmi
  have hdi : d i = r := by
    rw [← hmw, Finsupp.weight_single, one_smul]
  rw [← MvPolynomial.C_mul_X_eq_monomial, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hdi, rfl⟩)

end Span

end Langlands.GroupScheme.Corepresented
