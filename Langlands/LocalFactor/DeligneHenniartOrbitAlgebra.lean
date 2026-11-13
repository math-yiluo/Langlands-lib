import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Normal.Basic

/-! # Finite-orbit algebra for the norm--trace comparison -/

noncomputable section

open scoped BigOperators

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

section Orbits

variable (G Y A : Type*) [Group G] [Fintype G] [Fintype Y] [MulAction G Y]
  [AddCommGroup A]

omit [Fintype G] in
/-- Membership of every orbit sum implies membership of the sum over an
invariant finite subset. No equivariance of the summand is required. -/
theorem sum_mem_of_orbit_sums (S : AddSubgroup A) (f : Y → A) (s : Finset Y)
    (hs : ∀ g : G, ∀ y ∈ s, g • y ∈ s)
    (hf : ∀ y ∈ s, ∑ z ∈ (MulAction.orbit G y).toFinite.toFinset, f z ∈ S) :
    ∑ y ∈ s, f y ∈ S := by
  classical
  let q : Y → Quotient (MulAction.orbitRel G Y) := Quotient.mk''
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image q) (g := q) (fun _ hy => Finset.mem_image_of_mem q hy) f]
  apply S.sum_mem
  intro c hc
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
  have heq : (s.filter fun z => q z = q y) = (MulAction.orbit G y).toFinite.toFinset := by
    ext z
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨_, h⟩
      exact Quotient.exact h
    · intro hz
      obtain ⟨g, rfl⟩ := hz
      exact ⟨hs g y hy, Quotient.sound (MulAction.mem_orbit _ _)⟩
  rw [heq]
  exact hf y hy

/-- Summing over the acting group counts every orbit element with multiplicity
equal to the cardinality of the stabilizer. -/
theorem sum_action_eq_card_stabilizer_nsmul (f : Y → A) (y : Y) :
    ∑ g : G, f (g • y) =
      Nat.card (MulAction.stabilizer G y) •
        ∑ z ∈ (MulAction.orbit G y).toFinite.toFinset, f z := by
  classical
  let : Fintype (MulAction.orbit G y) := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer G y) := Fintype.ofFinite _
  let π : G → MulAction.orbit G y := fun g => ⟨g • y, MulAction.mem_orbit _ _⟩
  have hfiber (a : MulAction.orbit G y) :
      ∑ g : {g // π g = a}, f ((g : G) • y) =
        Nat.card (MulAction.stabilizer G y) • f a := by
    obtain ⟨h, hh⟩ := a.property
    change h • y = (a : Y) at hh
    let e : MulAction.stabilizer G y ≃ {g // π g = a} :=
      { toFun := fun b => ⟨h * b, Subtype.ext (by
          change (h * (b : G)) • y = (a : Y)
          rw [mul_smul, b.property, hh])⟩
        invFun := fun g => ⟨h⁻¹ * g, by
          change (h⁻¹ * (g : G)) • y = y
          rw [mul_smul, show (g : G) • y = (a : Y) from
            congrArg Subtype.val g.property, ← hh, inv_smul_smul]⟩
        left_inv := fun b => Subtype.ext (by simp)
        right_inv := fun g => Subtype.ext (by simp) }
    have hconst (g : {g // π g = a}) : f ((g : G) • y) = f a :=
      congrArg f (congrArg Subtype.val g.property)
    simp_rw [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_congr e.symm,
      Fintype.card_eq_nat_card]
  rw [← Fintype.sum_fiberwise π (fun g : G => f (g • y))]
  simp_rw [hfiber]
  rw [← Finset.smul_sum,
    Finset.sum_subtype (MulAction.orbit G y).toFinite.toFinset
      (fun _ => Set.Finite.mem_toFinset _) f]

/-- The two finite-orbit sum facts used to pass from orbitwise trace bounds
to the full norm expansion. -/
def OrbitSumDecompositionStatement : Prop :=
  (∀ (S : AddSubgroup A) (f : Y → A) (s : Finset Y),
    (∀ g : G, ∀ y ∈ s, g • y ∈ s) →
    (∀ y ∈ s, ∑ z ∈ (MulAction.orbit G y).toFinite.toFinset, f z ∈ S) →
    ∑ y ∈ s, f y ∈ S) ∧
  (∀ (f : Y → A) (y : Y),
    ∑ g : G, f (g • y) =
      Nat.card (MulAction.stabilizer G y) •
        ∑ z ∈ (MulAction.orbit G y).toFinite.toFinset, f z)

theorem orbitSumDecomposition : OrbitSumDecompositionStatement G Y A :=
  ⟨sum_mem_of_orbit_sums G Y A, sum_action_eq_card_stabilizer_nsmul G Y A⟩

end Orbits

section Fields

variable (K L M : Type*) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Normal K M]

/-- An embedding of an intermediate field into a normal overfield extends to
an automorphism of that overfield. -/
theorem exists_automorphism_extending_embedding (σ : L →ₐ[K] M) :
    ∃ g : M ≃ₐ[K] M,
      g.toAlgHom.comp (IsScalarTower.toAlgHom K L M) = σ := by
  let φ : M →ₐ[K] M := σ.liftNormal M
  let g : M ≃ₐ[K] M := AlgEquiv.ofBijective φ (φ.normal_bijective K M M)
  refine ⟨g, ?_⟩
  ext x
  exact σ.liftNormal_commutes M x

/-- Postcomposition into an algebraically closed extension creates no new
embeddings of a field contained in a normal overfield. -/
theorem normal_embeddings_postcomp_bijective
    (E : Type*) [Field E] [Algebra K E] [Algebra M E]
    [IsScalarTower K M E] [IsAlgClosed E] :
    Function.Bijective (fun σ : L →ₐ[K] M =>
      (IsScalarTower.toAlgHom K M E).comp σ) := by
  refine ⟨?_, ?_⟩
  · intro σ τ h
    ext x
    exact (algebraMap M E).injective (congrArg (fun f : L →ₐ[K] E => f x) h)
  · intro σ
    let : Normal L M := Normal.tower_top_of_normal K L M
    obtain ⟨φ, hφ⟩ :=
      IsAlgClosed.surjective_domRestrict_of_isAlgebraic (E := M) σ
    refine ⟨(φ.restrictNormal M).comp (IsScalarTower.toAlgHom K L M), ?_⟩
    ext x
    change algebraMap M E (φ.restrictNormal M (algebraMap L M x)) = σ x
    rw [AlgHom.restrictNormal_commutes]
    exact congrArg (fun f : L →ₐ[K] E => f x) hφ

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The norm of an element of a separable intermediate field is the product
over its embeddings into the normal overfield. -/
theorem algebraMap_norm_eq_prod_embeddings_normal (y : L) :
    algebraMap K M (Algebra.norm K y) = ∏ σ : L →ₐ[K] M, σ y := by
  classical
  let E := AlgebraicClosure M
  let e : (L →ₐ[K] M) ≃ (L →ₐ[K] E) :=
    Equiv.ofBijective _ (normal_embeddings_postcomp_bijective K L M E)
  apply (algebraMap M E).injective
  rw [map_prod, ← IsScalarTower.algebraMap_apply K M E,
    Algebra.norm_eq_prod_embeddings K E y]
  exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm

/-- The trace of an element of a separable intermediate field is the sum
over its embeddings into the normal overfield. -/
theorem algebraMap_trace_eq_sum_embeddings_normal (y : L) :
    algebraMap K M (Algebra.trace K L y) = ∑ σ : L →ₐ[K] M, σ y := by
  classical
  let E := AlgebraicClosure M
  let e : (L →ₐ[K] M) ≃ (L →ₐ[K] E) :=
    Equiv.ofBijective _ (normal_embeddings_postcomp_bijective K L M E)
  apply (algebraMap M E).injective
  rw [map_sum, ← IsScalarTower.algebraMap_apply K M E,
    trace_eq_sum_embeddings E]
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

end Fields

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
