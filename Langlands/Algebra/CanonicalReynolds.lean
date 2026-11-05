import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Canonical Reynolds operators of semisimple representations -/

namespace Langlands.Algebra.CanonicalReynolds

open Representation

section Linear

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The span of the differences `ρ g v - v` for `g` in the group and `v` in `N`. -/
def differenceSpan (ρ : Representation k G V) (N : Submodule k V) : Submodule k V :=
  Submodule.span k {w | ∃ g : G, ∃ v ∈ N, ρ g v - v = w}

/-- A subspace is stable when every group element maps it into itself. -/
def IsStable (ρ : Representation k G V) (N : Submodule k V) : Prop :=
  ∀ g : G, ∀ v ∈ N, ρ g v ∈ N

variable {ρ : Representation k G V}

lemma apply_of_mem_invariants {v : V} (hv : v ∈ ρ.invariants) (g : G) : ρ g v = v :=
  (mem_invariants ρ v).1 hv g

lemma sub_mem_differenceSpan {N : Submodule k V} (g : G) {v : V} (hv : v ∈ N) :
    ρ g v - v ∈ differenceSpan ρ N :=
  Submodule.subset_span ⟨g, v, hv, rfl⟩

lemma differenceSpan_mono {N N' : Submodule k V} (h : N ≤ N') :
    differenceSpan ρ N ≤ differenceSpan ρ N' :=
  Submodule.span_mono fun _ ⟨g, v, hv, hw⟩ => ⟨g, v, h hv, hw⟩

lemma isStable_top : IsStable ρ ⊤ := fun _ _ _ => Submodule.mem_top

lemma isStable_invariants : IsStable ρ ρ.invariants := by
  intro g v hv
  rw [apply_of_mem_invariants hv g]
  exact hv

lemma IsStable.inf {N N' : Submodule k V} (hN : IsStable ρ N) (hN' : IsStable ρ N') :
    IsStable ρ (N ⊓ N') :=
  fun g _ hv => ⟨hN g _ hv.1, hN' g _ hv.2⟩

lemma differenceSpan_le {N : Submodule k V} (hN : IsStable ρ N) : differenceSpan ρ N ≤ N :=
  Submodule.span_le.2 fun _ ⟨g, v, hv, hw⟩ => hw ▸ N.sub_mem (hN g v hv) hv

lemma isStable_differenceSpan (N : Submodule k V) : IsStable ρ (differenceSpan ρ N) := by
  intro g w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨h, v, hv, rfl⟩ := hw
    have : ρ g (ρ h v - v) = (ρ (g * h) v - v) - (ρ g v - v) := by
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
    rw [this]
    exact Submodule.sub_mem _ (sub_mem_differenceSpan _ hv) (sub_mem_differenceSpan _ hv)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- In a semisimple representation every stable subspace has a stable complement. -/
lemma exists_isStable_isCompl [IsSemisimpleRepresentation ρ] {N : Submodule k V}
    (hN : IsStable ρ N) : ∃ Q : Submodule k V, IsStable ρ Q ∧ IsCompl N Q := by
  obtain ⟨Q, hQ⟩ := exists_isCompl (⟨N, hN⟩ : Subrepresentation ρ)
  refine ⟨Q.toSubmodule, fun g v hv => Q.apply_mem_toSubmodule g hv, ?_⟩
  have hd := disjoint_iff.1 hQ.1
  have hc := codisjoint_iff.1 hQ.2
  exact ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hd),
    codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hc)⟩

/-- A stable complement of the invariants of `N` contains the difference span of `N`. -/
lemma differenceSpan_le_of_isCompl {N Q : Submodule k V} (hN : IsStable ρ N)
    (hQ : IsStable ρ Q) (hNQ : IsCompl (N ⊓ ρ.invariants) Q) :
    differenceSpan ρ N ≤ Q ⊓ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, v, hv, rfl⟩
  have hv' : v ∈ (N ⊓ ρ.invariants) ⊔ Q := hNQ.2.eq_top ▸ Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hv'
  have hpinv : ρ g p = p := apply_of_mem_invariants (Submodule.mem_inf.1 hp).2 g
  have hqN : q ∈ N := by
    have := N.sub_mem hv (Submodule.mem_inf.1 hp).1
    simpa using this
  have : ρ g (p + q) - (p + q) = ρ g q - q := by
    rw [map_add, hpinv]
    abel
  rw [this]
  exact ⟨Q.sub_mem (hQ g q hq) hq, N.sub_mem (hN g q hqN) hqN⟩

/-- Every vector of a stable subspace is an invariant vector of that subspace plus a sum of
differences from that subspace. -/
theorem le_invariants_sup_differenceSpan [IsSemisimpleRepresentation ρ] {N : Submodule k V}
    (hN : IsStable ρ N) : N ≤ (N ⊓ ρ.invariants) ⊔ differenceSpan ρ N := by
  obtain ⟨Q, hQ, hPQ⟩ := exists_isStable_isCompl (hN.inf isStable_invariants)
  have hAC := differenceSpan_le_of_isCompl hN hQ hPQ
  have hCA : Q ⊓ N ≤ differenceSpan ρ N := by
    obtain ⟨Q', hQ', hAQ'⟩ := exists_isStable_isCompl (isStable_differenceSpan (ρ := ρ) N)
    intro c hc
    have hc' : c ∈ differenceSpan ρ N ⊔ Q' := hAQ'.2.eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, q', hq', rfl⟩ := Submodule.mem_sup.1 hc'
    have hq'C : q' ∈ Q ⊓ N := by
      have := (Q ⊓ N).sub_mem hc (hAC ha)
      simpa using this
    have hinv : q' ∈ ρ.invariants := by
      refine (mem_invariants ρ q').2 fun g => ?_
      have hmem : ρ g q' - q' ∈ differenceSpan ρ N ⊓ Q' :=
        ⟨sub_mem_differenceSpan g (Submodule.mem_inf.1 hq'C).2, Q'.sub_mem (hQ' g q' hq') hq'⟩
      rw [hAQ'.1.eq_bot] at hmem
      exact sub_eq_zero.1 ((Submodule.mem_bot k).1 hmem)
    have hzero : q' = 0 := by
      have hmem : q' ∈ (N ⊓ ρ.invariants) ⊓ Q :=
        ⟨⟨(Submodule.mem_inf.1 hq'C).2, hinv⟩, (Submodule.mem_inf.1 hq'C).1⟩
      rw [hPQ.1.eq_bot] at hmem
      exact (Submodule.mem_bot k).1 hmem
    simpa [hzero] using ha
  intro v hv
  have hv' : v ∈ (N ⊓ ρ.invariants) ⊔ Q := hPQ.2.eq_top ▸ Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hv'
  have hqN : q ∈ N := by
    have := N.sub_mem hv (Submodule.mem_inf.1 hp).1
    simpa using this
  exact Submodule.add_mem_sup hp (hCA ⟨hq, hqN⟩)

theorem disjoint_invariants_differenceSpan [IsSemisimpleRepresentation ρ] :
    Disjoint ρ.invariants (differenceSpan ρ ⊤) := by
  obtain ⟨Q, hQ, hPQ⟩ := exists_isStable_isCompl (isStable_top.inf (isStable_invariants (ρ := ρ)))
  have hA := differenceSpan_le_of_isCompl isStable_top hQ hPQ
  rw [top_inf_eq] at hPQ
  exact hPQ.1.mono_right (hA.trans inf_le_left)

/-- The invariants and the span of all differences are complementary. -/
theorem isCompl_invariants_differenceSpan [IsSemisimpleRepresentation ρ] :
    IsCompl ρ.invariants (differenceSpan ρ ⊤) := by
  refine ⟨disjoint_invariants_differenceSpan, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
  have := le_invariants_sup_differenceSpan (isStable_top (ρ := ρ))
  rwa [top_inf_eq] at this

variable (ρ) in
/-- The canonical Reynolds operator: projection onto the invariants along the span of all
differences `ρ g v - v`. -/
noncomputable def reynolds [IsSemisimpleRepresentation ρ] : V →ₗ[k] V :=
  ρ.invariants.projection (differenceSpan ρ ⊤) isCompl_invariants_differenceSpan

variable [IsSemisimpleRepresentation ρ]

theorem reynolds_mem_invariants (v : V) : reynolds ρ v ∈ ρ.invariants :=
  Submodule.projection_apply_mem _ v

theorem reynolds_of_mem_invariants {v : V} (hv : v ∈ ρ.invariants) : reynolds ρ v = v :=
  Submodule.projection_apply_of_mem_left _ hv

theorem sub_reynolds_mem (v : V) : v - reynolds ρ v ∈ differenceSpan ρ ⊤ :=
  Submodule.sub_projection_mem _ v

theorem reynolds_eq_zero_iff {v : V} : reynolds ρ v = 0 ↔ v ∈ differenceSpan ρ ⊤ :=
  Submodule.projection_apply_eq_zero_iff _

/-- The Reynolds value is the unique invariant vector differing from `v` by a sum of
differences. -/
theorem reynolds_eq_of {v w : V} (hw : w ∈ ρ.invariants) (hvw : v - w ∈ differenceSpan ρ ⊤) :
    reynolds ρ v = w := by
  have h1 : reynolds ρ v - w ∈ ρ.invariants :=
    Submodule.sub_mem _ (reynolds_mem_invariants v) hw
  have h2 : reynolds ρ v - w ∈ differenceSpan ρ ⊤ := by
    have := Submodule.sub_mem _ hvw (sub_reynolds_mem (ρ := ρ) v)
    convert this using 1
    abel
  exact sub_eq_zero.1 ((Submodule.disjoint_def.1 disjoint_invariants_differenceSpan) _ h1 h2)

theorem reynolds_apply (g : G) (v : V) : reynolds ρ (ρ g v) = reynolds ρ v := by
  have : reynolds ρ (ρ g v - v) = 0 :=
    reynolds_eq_zero_iff.2 (sub_mem_differenceSpan g Submodule.mem_top)
  rwa [map_sub, sub_eq_zero] at this

/-- The Reynolds operator maps every stable subspace into itself. -/
theorem reynolds_mem {N : Submodule k V} (hN : IsStable ρ N) {v : V} (hv : v ∈ N) :
    reynolds ρ v ∈ N := by
  obtain ⟨p, hp, a, ha, rfl⟩ := Submodule.mem_sup.1 (le_invariants_sup_differenceSpan hN hv)
  rw [reynolds_eq_of (Submodule.mem_inf.1 hp).2 (by simpa using differenceSpan_mono le_top ha)]
  exact (Submodule.mem_inf.1 hp).1

/-- Linear maps that are invariant under the group do not see the Reynolds projection. -/
theorem apply_reynolds_of_invariant {M : Type*} [AddCommGroup M] [Module k M] (ψ : V →ₗ[k] M)
    (hψ : ∀ g v, ψ (ρ g v) = ψ v) (v : V) : ψ (reynolds ρ v) = ψ v := by
  have hle : differenceSpan ρ ⊤ ≤ LinearMap.ker ψ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, w, -, rfl⟩
    simp [hψ]
  have := hle (sub_reynolds_mem (ρ := ρ) v)
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  exact this.symm

variable {W : Type*} [AddCommGroup W] [Module k W] {σ : Representation k G W}

omit [IsSemisimpleRepresentation ρ] in
lemma map_differenceSpan_le (φ : V →ₗ[k] W) (hφ : ∀ g v, φ (ρ g v) = σ g (φ v)) :
    (differenceSpan ρ ⊤).map φ ≤ differenceSpan σ ⊤ := by
  rw [differenceSpan, Submodule.map_span_le]
  rintro _ ⟨g, v, -, rfl⟩
  rw [map_sub, hφ]
  exact sub_mem_differenceSpan g Submodule.mem_top

/-- Reynolds operators commute with equivariant linear maps. -/
theorem map_reynolds [IsSemisimpleRepresentation σ] (φ : V →ₗ[k] W)
    (hφ : ∀ g v, φ (ρ g v) = σ g (φ v)) (v : V) : φ (reynolds ρ v) = reynolds σ (φ v) := by
  symm
  refine reynolds_eq_of ((mem_invariants σ _).2 fun g => ?_) ?_
  · rw [← hφ, apply_of_mem_invariants (reynolds_mem_invariants v) g]
  · rw [← map_sub]
    exact map_differenceSpan_le φ hφ (Submodule.mem_map_of_mem (sub_reynolds_mem v))

omit [IsSemisimpleRepresentation ρ] in
/-- A representation that is an equivariant image of a semisimple one is semisimple. -/
theorem isSemisimpleRepresentation_of_surjective [IsSemisimpleRepresentation ρ]
    (φ : V →ₗ[k] W) (hφ : ∀ g v, φ (ρ g v) = σ g (φ v)) (hsurj : Function.Surjective φ) :
    IsSemisimpleRepresentation σ := by
  refine ⟨fun N => ?_⟩
  have hpre : IsStable ρ (N.toSubmodule.comap φ) := fun g v hv => by
    rw [Submodule.mem_comap, hφ]
    exact N.apply_mem_toSubmodule g hv
  obtain ⟨Q, hQ, hPQ⟩ := exists_isStable_isCompl hpre
  refine ⟨⟨Q.map φ, ?_⟩, ?_⟩
  · rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hQ g v hv, hφ g v⟩
  constructor
  · rw [disjoint_iff]
    refine Subrepresentation.toSubmodule_injective ?_
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨hyN, ⟨x, hx, rfl⟩⟩ := hy
    have hmem : x ∈ N.toSubmodule.comap φ ⊓ Q := ⟨hyN, hx⟩
    rw [hPQ.1.eq_bot] at hmem
    rw [(Submodule.mem_bot k).1 hmem, map_zero]
    exact Submodule.zero_mem _
  · rw [codisjoint_iff]
    refine Subrepresentation.toSubmodule_injective ?_
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ N.toSubmodule.comap φ ⊔ Q := hPQ.2.eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup ha (Submodule.mem_map_of_mem hb)

end Linear

section Algebra

variable {k G A : Type*} [Field k] [Group G] [CommRing A] [Algebra k A]

/-- The representation acts on the algebra by algebra endomorphisms. -/
structure IsMultiplicative (ρ : Representation k G A) : Prop where
  map_one : ∀ g, ρ g 1 = 1
  map_mul : ∀ g a b, ρ g (a * b) = ρ g a * ρ g b

variable {ρ : Representation k G A}

/-- The subalgebra of invariant elements. -/
def invariantSubalgebra (hρ : IsMultiplicative ρ) : Subalgebra k A where
  carrier := ρ.invariants
  mul_mem' {a b} ha hb := (mem_invariants ρ _).2 fun g => by
    rw [hρ.map_mul, apply_of_mem_invariants ha g, apply_of_mem_invariants hb g]
  add_mem' ha hb := ρ.invariants.add_mem ha hb
  algebraMap_mem' c := (mem_invariants ρ _).2 fun g => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hρ.map_one]

@[simp]
lemma mem_invariantSubalgebra (hρ : IsMultiplicative ρ) {a : A} :
    a ∈ invariantSubalgebra hρ ↔ a ∈ ρ.invariants :=
  Iff.rfl

variable [IsSemisimpleRepresentation ρ]

/-- The Reynolds operator is linear over the invariant subalgebra. -/
theorem reynolds_mul_left (hρ : IsMultiplicative ρ) {f : A} (hf : f ∈ ρ.invariants) (a : A) :
    reynolds ρ (f * a) = f * reynolds ρ a := by
  have := map_reynolds (ρ := ρ) (σ := ρ) (LinearMap.mulLeft k f)
    (fun g v => show f * ρ g v = ρ g (f * v) by
      rw [hρ.map_mul, apply_of_mem_invariants hf g]) a
  simpa [LinearMap.mulLeft_apply] using this.symm

theorem reynolds_one (hρ : IsMultiplicative ρ) : reynolds ρ (1 : A) = 1 :=
  reynolds_of_mem_invariants ((mem_invariants ρ _).2 hρ.map_one)

/-- Extension and contraction of an ideal of the invariant subalgebra returns that ideal. -/
theorem comap_map_ideal (hρ : IsMultiplicative ρ) (I : Ideal (invariantSubalgebra hρ)) :
    (I.map (algebraMap (invariantSubalgebra hρ) A)).comap
      (algebraMap (invariantSubalgebra hρ) A) = I := by
  refine le_antisymm (fun x hx => ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap, Ideal.map, Ideal.span, Submodule.mem_span_set'] at hx
  obtain ⟨n, f, g, hsum⟩ := hx
  choose y hyI hy using fun i => (g i).2
  have key : (x : A) = ∑ i, reynolds ρ (f i) * (y i : A) := by
    have h1 : reynolds ρ (x : A) = x := reynolds_of_mem_invariants x.2
    rw [← h1, ← show (algebraMap (invariantSubalgebra hρ) A x) = x from rfl, ← hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hy i, mul_comm]
    exact reynolds_mul_left hρ (y i).2 (f i) |>.trans (mul_comm _ _)
  have hx : x = ∑ i, (⟨reynolds ρ (f i), reynolds_mem_invariants _⟩ :
      invariantSubalgebra hρ) * y i := by
    apply Subtype.ext
    simpa using key
  rw [hx]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hyI i)

/-- Over an algebraically closed field, every rational point of the invariant subalgebra of a
finitely generated algebra lifts to a rational point of the algebra. -/
theorem exists_algHom_comp_val_eq [IsAlgClosed k] [Algebra.FiniteType k A]
    (hρ : IsMultiplicative ρ) (χ : invariantSubalgebra hρ →ₐ[k] k) :
    ∃ ψ : A →ₐ[k] k, ψ.comp (invariantSubalgebra hρ).val = χ := by
  have hχs : Function.Surjective χ := fun c => ⟨algebraMap k _ c, χ.commutes c⟩
  have hm : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχs
  have hne : (RingHom.ker χ).map (algebraMap (invariantSubalgebra hρ) A) ≠ ⊤ := by
    intro htop
    have := comap_map_ideal hρ (RingHom.ker χ)
    rw [htop, Ideal.comap_top] at this
    exact hm.ne_top this.symm
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have _ : Module.Finite k (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ M)
  have _ : Algebra.IsIntegral k (A ⧸ M) := Algebra.IsIntegral.of_finite k (A ⧸ M)
  have hbij : Function.Bijective (algebraMap k (A ⧸ M)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] A ⧸ M := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ M)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k M), ?_⟩
  ext x
  have hx : x - algebraMap k _ (χ x) ∈ RingHom.ker χ := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have hxM : (x : A) - algebraMap k A (χ x) ∈ M :=
    hle (by simpa using Ideal.mem_map_of_mem (algebraMap (invariantSubalgebra hρ) A) hx)
  have hq : Ideal.Quotient.mkₐ k M (x : A) = e (χ x) := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq.2 hxM, Ideal.Quotient.mk_algebraMap]
    rfl
  show e.symm (Ideal.Quotient.mkₐ k M (x : A)) = χ x
  rw [hq, AlgEquiv.symm_apply_apply]

/-- Two comaximal stable ideals are separated by an invariant element. -/
theorem exists_invariant_mem_sub_one_mem (hρ : IsMultiplicative ρ) {I J : Ideal A}
    (hI : IsStable ρ (I.restrictScalars k)) (hJ : IsStable ρ (J.restrictScalars k))
    (hIJ : I ⊔ J = ⊤) : ∃ f ∈ ρ.invariants, f ∈ I ∧ f - 1 ∈ J := by
  have h1 : (1 : A) ∈ I ⊔ J := hIJ ▸ Submodule.mem_top
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 h1
  refine ⟨reynolds ρ i, reynolds_mem_invariants i, reynolds_mem hI hi, ?_⟩
  have : reynolds ρ i - 1 = reynolds ρ (-j) := by
    rw [← reynolds_one hρ, ← map_sub, ← hij]
    congr 1
    abel
  rw [this]
  exact reynolds_mem hJ (J.neg_mem hj)

omit [IsSemisimpleRepresentation ρ] in
/-- An equivariant surjection of algebras maps invariants onto invariants. -/
theorem map_invariantSubalgebra_eq [IsSemisimpleRepresentation ρ] {B : Type*} [CommRing B]
    [Algebra k B] {σ : Representation k G B} (hρ : IsMultiplicative ρ) (hσ : IsMultiplicative σ)
    (φ : A →ₐ[k] B) (hφ : ∀ g a, φ (ρ g a) = σ g (φ a)) (hsurj : Function.Surjective φ) :
    (invariantSubalgebra hρ).map φ = invariantSubalgebra hσ := by
  have := isSemisimpleRepresentation_of_surjective φ.toLinearMap hφ hsurj
  refine le_antisymm ?_ fun b hb => ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact (mem_invariants σ _).2 fun g => by
      show σ g (φ a) = φ a
      rw [← hφ, apply_of_mem_invariants ha g]
  · obtain ⟨a, rfl⟩ := hsurj b
    refine ⟨reynolds ρ a, reynolds_mem_invariants a, ?_⟩
    have := map_reynolds (σ := σ) φ.toLinearMap hφ a
    simp only [AlgHom.toLinearMap_apply] at this
    rw [RingHom.coe_coe, this, reynolds_of_mem_invariants hb]

end Algebra

section Graded

variable {k G A : Type*} [Field k] [Group G] [CommRing A] [Algebra k A]
  {ρ : Representation k G A} (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

omit [GradedAlgebra 𝒜] in
lemma proj_apply_rep [GradedAlgebra 𝒜] (h𝒜 : ∀ d, IsStable ρ (𝒜 d)) (d : ℕ) (g : G) (x : A) :
    GradedRing.proj 𝒜 d (ρ g x) = ρ g (GradedRing.proj 𝒜 d x) := by
  classical
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i m =>
    have hm : ρ g (m : A) ∈ 𝒜 i := h𝒜 i g _ m.2
    by_cases hd : i = d
    · subst hd
      simp only [GradedRing.proj_apply]
      rw [DirectSum.decompose_of_mem_same 𝒜 hm, DirectSum.decompose_coe, DirectSum.of_eq_same]
    · simp only [GradedRing.proj_apply]
      rw [DirectSum.decompose_of_mem_ne 𝒜 hm hd, DirectSum.decompose_coe,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hd), ZeroMemClass.coe_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- Hilbert's finiteness theorem: if a semisimple representation acts by graded algebra
automorphisms on a Noetherian graded algebra whose degree-zero part consists of scalars, then the
invariant subalgebra is finitely generated. -/
theorem invariantSubalgebra_fg [IsSemisimpleRepresentation ρ] [IsNoetherianRing A]
    (hρ : IsMultiplicative ρ) (h𝒜 : ∀ d, IsStable ρ (𝒜 d))
    (h0 : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a) :
    (invariantSubalgebra hρ).FG := by
  classical
  set S : Set A := {a | a ∈ ρ.invariants ∧ ∃ d, 0 < d ∧ a ∈ 𝒜 d}
  obtain ⟨T, hTS, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).1
    (IsNoetherian.noetherian (Submodule.span A S))
  choose! e he using fun t (ht : t ∈ T) => (hTS ht).2
  have key : ∀ d, ∀ a ∈ 𝒜 d, a ∈ ρ.invariants → a ∈ Algebra.adjoin k (T : Set A) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro a ha hainv
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · obtain ⟨c, rfl⟩ := h0 a ha
      exact Subalgebra.algebraMap_mem _ c
    · have haS : a ∈ Submodule.span A (T : Set A) := hT ▸ Submodule.subset_span ⟨hainv, d, hd, ha⟩
      obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 haS
      have hsum : a = ∑ t ∈ T,
          (if e t ≤ d then reynolds ρ (GradedRing.proj 𝒜 (d - e t) (f t)) * t else 0) := by
        calc a = reynolds ρ (GradedRing.proj 𝒜 d a) := by
              rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 ha,
                reynolds_of_mem_invariants hainv]
          _ = ∑ t ∈ T, reynolds ρ (GradedRing.proj 𝒜 d (f t * t)) := by
              rw [← hf, map_sum, map_sum]
              rfl
          _ = _ := by
              refine Finset.sum_congr rfl fun t ht => ?_
              rw [GradedRing.proj_apply, DirectSum.coe_decompose_mul_of_right_mem 𝒜 d (he t ht).2]
              split_ifs
              · rw [mul_comm, reynolds_mul_left hρ (hTS ht).1, mul_comm, GradedRing.proj_apply]
              · exact map_zero _
      rw [hsum]
      refine Subalgebra.sum_mem _ fun t ht => ?_
      split_ifs with hle
      · refine Subalgebra.mul_mem _ (ih (d - e t) (by have := (he t ht).1; omega) _ ?_ ?_)
          (Algebra.subset_adjoin ht)
        · exact reynolds_mem (h𝒜 (d - e t)) (by
            rw [GradedRing.proj_apply]
            exact (DirectSum.decompose 𝒜 (f t) (d - e t)).2)
        · exact reynolds_mem_invariants _
      · exact Subalgebra.zero_mem _
  refine ⟨T, le_antisymm ?_ fun a ha => ?_⟩
  · exact Algebra.adjoin_le fun t ht => (hTS ht).1
  · rw [← DirectSum.sum_support_decompose 𝒜 a]
    refine Subalgebra.sum_mem _ fun d _ => key d _ (DirectSum.decompose 𝒜 a d).2 ?_
    refine (mem_invariants ρ _).2 fun g => ?_
    have := proj_apply_rep 𝒜 h𝒜 d g a
    rw [apply_of_mem_invariants ha g] at this
    simpa [GradedRing.proj_apply] using this.symm

end Graded

end Langlands.Algebra.CanonicalReynolds
