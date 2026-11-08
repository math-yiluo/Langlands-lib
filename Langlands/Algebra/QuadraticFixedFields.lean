import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.IndexNormal

/-! # Index-two Galois subgroups and separable quadratic intermediate extensions -/

noncomputable section

universe u

open Module IntermediateField

namespace Langlands.Algebra.QuadraticFixedFields

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

section Nested

variable (K₀ K : IntermediateField k L)

/-- The inclusion algebra between nested intermediate fields. Mathlib has no
instance for it, since `K₀ ≤ K` is a proposition. -/
@[reducible] def nestedAlgebra (h : K₀ ≤ K) : Algebra K₀ K :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

theorem nestedAlgebra_isScalarTower (h : K₀ ≤ K) :
    letI := nestedAlgebra K₀ K h
    IsScalarTower K₀ K L := by
  let _ := nestedAlgebra K₀ K h
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

variable [Algebra K₀ K] [IsScalarTower K₀ K L]

/-- A scalar-tower algebra between intermediate fields is the inclusion. -/
theorem coe_algebraMap (x : K₀) : ((algebraMap K₀ K x : K) : L) = x := by
  change algebraMap K L (algebraMap K₀ K x) = algebraMap K₀ L x
  rw [← IsScalarTower.algebraMap_apply]

theorem le_of_isScalarTower : K₀ ≤ K := by
  intro x hx
  have := (algebraMap K₀ K ⟨x, hx⟩).2
  rwa [coe_algebraMap] at this

theorem isScalarTower_base : IsScalarTower k K₀ K :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (by rw [coe_algebraMap]; rfl)

end Nested

section Galois

variable [FiniteDimensional k L] [IsGalois k L]

omit [IsGalois k L] in
/-- Cardinalities of nested subgroups are related by the relative index. -/
theorem nat_card_eq_relIndex_mul {H H' : Subgroup (L ≃ₐ[k] L)} (hle : H ≤ H') :
    Nat.card H' = H.relIndex H' * Nat.card H := by
  have hpos : H'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h : Nat.card H' * H'.index = (H.relIndex H' * Nat.card H) * H'.index := by
    rw [Subgroup.card_mul_index, ← Subgroup.card_mul_index H, ← Subgroup.relIndex_mul_index hle]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) h

variable (K₀ K : IntermediateField k L) [Algebra K₀ K] [IsScalarTower K₀ K L]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The fixing subgroups of nested intermediate fields are nested. -/
theorem fixingSubgroup_le : K.fixingSubgroup ≤ K₀.fixingSubgroup :=
  IntermediateField.fixingSubgroup_le (le_of_isScalarTower K₀ K)

/-- **Galois correspondence for degrees.** The degree of nested intermediate fields is
the relative index of their fixing subgroups. -/
theorem finrank_eq_relIndex :
    finrank K₀ K = K.fixingSubgroup.relIndex K₀.fixingSubgroup := by
  have htower := Module.finrank_mul_finrank K₀ K L
  rw [← IsGalois.card_fixingSubgroup_eq_finrank, ← IsGalois.card_fixingSubgroup_eq_finrank,
    nat_card_eq_relIndex_mul (fixingSubgroup_le K₀ K)] at htower
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos htower

/-- Index two of the fixing subgroups makes the nested extension quadratic. -/
theorem isQuadraticExtension (h2 : K.fixingSubgroup.relIndex K₀.fixingSubgroup = 2) :
    Algebra.IsQuadraticExtension K₀ K where
  finrank_eq_two' := (finrank_eq_relIndex K₀ K).trans h2

omit [FiniteDimensional k L] in
/-- A nested extension inside a Galois extension is separable. -/
theorem isSeparable : Algebra.IsSeparable K₀ K :=
  Algebra.isSeparable_tower_bot_of_isSeparable K₀ K L

/-- A quadratic nested extension has fixing subgroups of relative index two. -/
theorem relIndex_eq_two [Algebra.IsQuadraticExtension K₀ K] :
    K.fixingSubgroup.relIndex K₀.fixingSubgroup = 2 :=
  (finrank_eq_relIndex K₀ K).symm.trans (Algebra.IsQuadraticExtension.finrank_eq_two K₀ K)

omit [FiniteDimensional k L] [IsGalois k L] in
/-- In relative index two, conjugation by an element of the larger fixing subgroup
preserves the smaller one. -/
theorem conj_mem_fixingSubgroup (h2 : K.fixingSubgroup.relIndex K₀.fixingSubgroup = 2)
    {s : L ≃ₐ[k] L} (hs : s ∈ K₀.fixingSubgroup) {g : L ≃ₐ[k] L}
    (hg : g ∈ K.fixingSubgroup) : s * g * s⁻¹ ∈ K.fixingSubgroup := by
  have hN := Subgroup.normal_of_index_eq_two h2
  have hle := fixingSubgroup_le K₀ K
  have h := hN.conj_mem ⟨g, hle hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨s, hs⟩
  rw [Subgroup.mem_subgroupOf] at h
  exact h

/-- Hence such an element maps the smaller fixed field into itself. -/
theorem apply_mem (h2 : K.fixingSubgroup.relIndex K₀.fixingSubgroup = 2)
    {s : L ≃ₐ[k] L} (hs : s ∈ K₀.fixingSubgroup) {x : L} (hx : x ∈ K) : s x ∈ K := by
  rw [← IsGalois.fixedField_fixingSubgroup K, mem_fixedField_iff] at hx ⊢
  intro g hg
  have hconj := hx _ (conj_mem_fixingSubgroup K₀ K h2 (inv_mem hs) hg)
  have hsx : s.symm (g (s x)) = x := by
    simpa only [AlgEquiv.mul_apply, inv_inv, AlgEquiv.aut_inv, AlgEquiv.symm_symm] using hconj
  calc g (s x) = s (s.symm (g (s x))) := (s.apply_symm_apply _).symm
    _ = s x := by rw [hsx]

/-- The restriction to the larger intermediate field, as an automorphism over the
smaller one, of an element fixing the smaller one. -/
def restrict (h2 : K.fixingSubgroup.relIndex K₀.fixingSubgroup = 2)
    (s : L ≃ₐ[k] L) (hs : s ∈ K₀.fixingSubgroup) : K ≃ₐ[K₀] K where
  toFun x := ⟨s x, apply_mem K₀ K h2 hs x.2⟩
  invFun x := ⟨s.symm x, by
    have h := apply_mem K₀ K h2 (inv_mem hs) x.2
    rwa [AlgEquiv.aut_inv] at h⟩
  left_inv x := Subtype.ext (s.symm_apply_apply (x : L))
  right_inv x := Subtype.ext (s.apply_symm_apply (x : L))
  map_mul' x y := Subtype.ext (map_mul s (x : L) y)
  map_add' x y := Subtype.ext (map_add s (x : L) y)
  commutes' c := Subtype.ext (by
    change s ((algebraMap K₀ K c : K) : L) = ((algebraMap K₀ K c : K) : L)
    rw [coe_algebraMap]
    exact (mem_fixingSubgroup_iff K₀ s).mp hs c c.2)

@[simp] theorem coe_restrict (h2 : K.fixingSubgroup.relIndex K₀.fixingSubgroup = 2)
    (s : L ≃ₐ[k] L) (hs : s ∈ K₀.fixingSubgroup) (x : K) :
    ((restrict K₀ K h2 s hs x : K) : L) = s x := rfl

/-- The restriction is nontrivial when the element does not fix the larger field. -/
theorem restrict_ne_one (h2 : K.fixingSubgroup.relIndex K₀.fixingSubgroup = 2)
    {s : L ≃ₐ[k] L} (hs : s ∈ K₀.fixingSubgroup) (hsK : s ∉ K.fixingSubgroup) :
    restrict K₀ K h2 s hs ≠ 1 := by
  intro h1
  apply hsK
  refine (mem_fixingSubgroup_iff K s).mpr fun x hx => ?_
  exact congrArg Subtype.val (DFunLike.congr_fun h1 ⟨x, hx⟩)

/-- **Conjugation of a quadratic intermediate extension.** If `K / K₀` is a separable
quadratic extension inside the finite Galois extension `L / k`, then every Galois
element fixing `K₀` but not `K` restricts on `K` to its nontrivial conjugation. -/
theorem conjugation_apply [Algebra.IsQuadraticExtension K₀ K] [Algebra.IsSeparable K₀ K]
    {s : L ≃ₐ[k] L} (hs : s ∈ K₀.fixingSubgroup) (hsK : s ∉ K.fixingSubgroup) (x : K) :
    (Langlands.GroupScheme.SU3Root.conjugation K₀ K x : L) = s x := by
  have h2 := relIndex_eq_two K₀ K
  rw [← Langlands.GroupScheme.SU3Root.conjugation_unique K₀ K (restrict K₀ K h2 s hs)
    (restrict_ne_one K₀ K h2 hs hsK)]
  rfl

omit [FiniteDimensional k L] [IsGalois k L] [Algebra K₀ K] [IsScalarTower K₀ K L] in
/-- Some Galois element fixes `K₀` but not `K`, in relative index two. -/
theorem exists_mem_not_mem (h2 : K.fixingSubgroup.relIndex K₀.fixingSubgroup = 2) :
    ∃ s ∈ K₀.fixingSubgroup, s ∉ K.fixingSubgroup := by
  by_contra h
  push Not at h
  have h1 : K.fixingSubgroup.relIndex K₀.fixingSubgroup = 1 :=
    Subgroup.relIndex_eq_one.mpr h
  omega

/-- The fixed points of the conjugation are exactly the smaller field. -/
theorem conjugation_eq_self_iff [Algebra.IsQuadraticExtension K₀ K] [Algebra.IsSeparable K₀ K]
    (x : K) : Langlands.GroupScheme.SU3Root.conjugation K₀ K x = x ↔ (x : L) ∈ K₀ := by
  obtain ⟨s, hs, hsK⟩ := exists_mem_not_mem K₀ K (relIndex_eq_two K₀ K)
  constructor
  · intro hx
    rw [← IsGalois.fixedField_fixingSubgroup K₀, mem_fixedField_iff]
    intro g hg
    by_cases hgK : g ∈ K.fixingSubgroup
    · exact (mem_fixingSubgroup_iff K g).mp hgK x x.2
    · rw [← conjugation_apply K₀ K hg hgK x, hx]
  · intro hx
    apply Subtype.ext
    rw [conjugation_apply K₀ K hs hsK x]
    exact (mem_fixingSubgroup_iff K₀ s).mp hs x hx

end Galois

end Langlands.Algebra.QuadraticFixedFields
