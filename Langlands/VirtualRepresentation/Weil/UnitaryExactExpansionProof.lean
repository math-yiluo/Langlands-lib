import Langlands.VirtualRepresentation.Weil.UnitaryExactExpansionStatement
import Langlands.VirtualRepresentation.Weil.ExactRealizationProof
import Langlands.Weil.Representation.UnitaryProof
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Effective unitary exact expansion

An invariant positive Hermitian form makes every subquotient of a
finite-dimensional representation unitarizable: invariant subspaces inherit the
restricted form, and a quotient is identified with the invariant orthogonal
complement of the kernel. Hence every composition factor of an actual continuous
unitarizable representation is a genuine unitary irreducible class, and the
composition-series sum is a nonnegative unitary combination expanding the whole
exact class.
-/

noncomputable section

universe uG uV uW

namespace Langlands.FiniteRepresentation

section Orthogonal

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- In finite dimension, every vector differs from a vector of a supplied
subspace by a vector orthogonal to that subspace for a positive definite
Hermitian form. -/
theorem exists_sub_mem_orthogonal (h : InnerProductSpace.Core ℂ V) (K : Submodule ℂ V)
    (v : V) : ∃ k ∈ K, ∀ u ∈ K, h.inner u (v - k) = 0 := by
  let : InnerProductSpace.Core ℂ V := h
  let : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ V := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ V)
  have : CompleteSpace K := FiniteDimensional.complete ℂ K
  obtain ⟨k, hk, hv⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := K) v
  exact ⟨k, hk, (Submodule.mem_orthogonal K _).mp hv⟩

end Orthogonal

variable {G : Type uG} [Group G]

/-- The vectors orthogonal to an invariant subspace for an invariant positive
form form an invariant subspace, because each group element acts invertibly. -/
def orthogonalSubrepresentation {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (b : InvariantPositiveForm ρ) (S : Subrepresentation ρ) :
    Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ u ∈ S.toSubmodule, b.inner u v = 0}
      zero_mem' := by
        let : InnerProductSpace.Core ℂ V := b.toInnerProductCore
        intro u _
        exact InnerProductSpace.Core.inner_zero_right u
      add_mem' := by
        let : InnerProductSpace.Core ℂ V := b.toInnerProductCore
        intro v w hv hw u hu
        have h := InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) u v w
        change b.inner u (v + w) = b.inner u v + b.inner u w at h
        rw [h, hv u hu, hw u hu, add_zero]
      smul_mem' := by
        let : InnerProductSpace.Core ℂ V := b.toInnerProductCore
        intro c v hv u hu
        have h := InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ) u v (r := c)
        change b.inner u (c • v) = c * b.inner u v at h
        rw [h, hv u hu, mul_zero] }
  apply_mem_toSubmodule g v hv u hu := by
    have hu' : ρ g⁻¹ u ∈ S.toSubmodule := S.apply_mem_toSubmodule g⁻¹ hu
    change b.inner u (ρ g v) = 0
    rw [← Representation.self_inv_apply ρ g u, b.invariant]
    exact hv _ hu'

/-- An invariant positive form pulls back along any injective intertwiner. -/
theorem isUnitary_of_injective_intertwiner {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    {B : FiniteRepresentation.{0, uG, uW} ℂ G}
    (i : A.representation.IntertwiningMap B.representation) (hi : Function.Injective i)
    (hB : B.IsUnitary) : A.IsUnitary :=
  (isUnitary_iff_isUnitarizable A).mpr
    (((isUnitary_iff_isUnitarizable B).mp hB).of_injective i hi)

/-- An actual invariant subspace of a unitarizable representation is unitarizable. -/
theorem isUnitary_subrepresentation {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    (hA : A.IsUnitary) (S : Subrepresentation A.representation) :
    (of S.toRepresentation).IsUnitary := by
  let i : S.toRepresentation.IntertwiningMap A.representation :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' _ := rfl }
  exact isUnitary_of_injective_intertwiner i (Submodule.injective_subtype _) hA

/-- A quotient of a finite-dimensional unitarizable representation, in the
stronger form of any surjective intertwiner, is unitarizable. The orthogonal
complement of the kernel is invariant and maps isomorphically onto the target. -/
theorem isUnitary_of_surjective_intertwiner {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    {B : FiniteRepresentation.{0, uG, uW} ℂ G}
    (q : A.representation.IntertwiningMap B.representation) (hq : Function.Surjective q)
    (hA : A.IsUnitary) : B.IsUnitary := by
  obtain ⟨b⟩ := (isUnitary_iff_isUnitarizable A).mp hA
  let K : Subrepresentation A.representation := q.ker
  let C : Subrepresentation A.representation := orthogonalSubrepresentation b K
  let i : C.toRepresentation.IntertwiningMap A.representation :=
    { toLinearMap := C.toSubmodule.subtype
      isIntertwining' _ := rfl }
  have hi : Function.Injective i := Submodule.injective_subtype _
  have hbij : Function.Bijective (q.comp i) := by
    constructor
    · intro x y hxy
      have hk : (x : A) - y ∈ K.toSubmodule := by
        change q ((x : A) - y) = 0
        rw [map_sub, sub_eq_zero]
        exact hxy
      have hc : (x : A) - y ∈ C.toSubmodule := C.toSubmodule.sub_mem x.property y.property
      have h0 : (x : A) - y = 0 := b.definite _ (hc _ hk)
      exact Subtype.ext (sub_eq_zero.mp h0)
    · intro w
      obtain ⟨v, rfl⟩ := hq w
      obtain ⟨k, hk, hvk⟩ := exists_sub_mem_orthogonal b.toInnerProductCore K.toSubmodule v
      refine ⟨⟨v - k, hvk⟩, ?_⟩
      have hk' : q k = 0 := hk
      change q (v - k) = q v
      rw [map_sub, hk', sub_zero]
  let e : Equiv (of C.toRepresentation) B := (q.comp i).ofBijective hbij
  exact isUnitary_of_equiv e.symm (isUnitary_subrepresentation hA C)

variable [TopologicalSpace G]

/-- Every graded quotient of a finite filtration of a continuous unitarizable
representation is unitarizable. -/
theorem isUnitary_continuousFiltrationGraded (A : ContinuousObjects.{uG, uV} G)
    (hA : A.val.IsUnitary) {n : ℕ} (s : ObjectRepFiltration A.val.obj n) (i : Fin n) :
    (continuousFiltrationGraded A s i).val.IsUnitary :=
  isUnitary_of_surjective_intertwiner (s.gradedProjection i).hom
    (s.gradedProjection_surjective i) (isUnitary_subrepresentation hA (s.subrepresentation i.succ))

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation ExactCoefficients

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- An actual continuous irreducible unitarizable object gives a unitary basis class. -/
theorem basisOf_mem_unitarySet (B : ContinuousObjects.{uG, uV} G) (h : B.val.IsIrreducible)
    (hu : B.val.IsUnitary) : basisOf B h ∈ unitarySet G :=
  ⟨B.val, hu, rfl⟩

/-- Including the unitary lattice sends a unitary generator to the same class. -/
theorem includeUnitary_generator (b : UnitaryBasis.{uG, uV} G) :
    includeUnitary G (generator b) = generator b.val := by
  simp [includeUnitary, includeSubset, map, generator]

/-- Every generator has nonnegative coefficients. -/
theorem generator_mem_effective {ι : Type*} (b : ι) : generator b ∈ effective := by
  classical
  intro j
  simp only [generator, Finsupp.single_apply]
  split_ifs <;> norm_num

/-- The unitary-lattice sum of the factors of a composition series whose
factors are unitarizable. -/
def unitarySeriesSum (A : ContinuousObjects.{uG, uV} G) {n : ℕ}
    (s : ObjectRepFiltration A.val.obj n) (hs : s.HasSimpleFactors)
    (hu : ∀ i, (continuousFiltrationGraded A s i).val.IsUnitary) :
    UnitaryLattice.{uG, uV} G :=
  ∑ i : Fin n, generator
    (⟨basisOf (continuousFiltrationGraded A s i) (hs i),
      basisOf_mem_unitarySet _ (hs i) (hu i)⟩ : UnitaryBasis.{uG, uV} G)

theorem unitarySeriesSum_mem_effective (A : ContinuousObjects.{uG, uV} G) {n : ℕ}
    (s : ObjectRepFiltration A.val.obj n) (hs : s.HasSimpleFactors)
    (hu : ∀ i, (continuousFiltrationGraded A s i).val.IsUnitary) :
    unitarySeriesSum A s hs hu ∈ effective :=
  AddSubmonoid.sum_mem _ fun _ _ => generator_mem_effective _

theorem includeUnitary_unitarySeriesSum (A : ContinuousObjects.{uG, uV} G) {n : ℕ}
    (s : ObjectRepFiltration A.val.obj n) (hs : s.HasSimpleFactors)
    (hu : ∀ i, (continuousFiltrationGraded A s i).val.IsUnitary) :
    includeUnitary G (unitarySeriesSum A s hs hu) = seriesSum A s hs := by
  simp only [unitarySeriesSum, map_sum, includeUnitary_generator, seriesSum]

variable (G)

/-- **Effective unitary exact expansion.** The exact class of every actual
continuous unitarizable finite-dimensional representation is the image of a
nonnegative combination of genuine continuous irreducible unitary classes. -/
theorem effectiveUnitaryExactExpansion :
    EffectiveUnitaryExactExpansionStatement.{uG, uV} G := by
  intro A hc hu
  obtain ⟨n, s, hs⟩ := exists_series (⟨A, hc⟩ : ContinuousObjects.{uG, uV} G)
  have hfac : ∀ i, (continuousFiltrationGraded ⟨A, hc⟩ s i).val.IsUnitary :=
    isUnitary_continuousFiltrationGraded ⟨A, hc⟩ hu s
  refine ⟨unitarySeriesSum ⟨A, hc⟩ s hs hfac,
    unitarySeriesSum_mem_effective ⟨A, hc⟩ s hs hfac, ?_⟩
  exact (congrArg (realizeExact G) (includeUnitary_unitarySeriesSum _ s hs hfac)).trans
    (realizeExact_seriesSum G _ s hs)

end Langlands.VirtualRepresentation.Weil

namespace Langlands.VirtualRepresentation.LocalWeil

universe uF

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Effective unitary exact expansion for the actual local Weil group. -/
theorem effectiveUnitaryExactExpansion :
    EffectiveUnitaryExactExpansionStatement.{uF, uW} F :=
  (effectiveUnitaryExactExpansion_iff F).mpr
    (Weil.effectiveUnitaryExactExpansion (localWeilGroup F))

end Langlands.VirtualRepresentation.LocalWeil
