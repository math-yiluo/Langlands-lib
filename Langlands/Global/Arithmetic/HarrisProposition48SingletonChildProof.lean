import Langlands.Global.Arithmetic.HarrisProposition48SingletonChildStatement

/-!
# The equal-rank singleton child in Harris, Proposition 4.8

A proof of `Langlands.Global.Harris.Proposition48SingletonChildNormalizationStatement`. A single
double coset `Gal(L/D) \ Gal(L/E) / Gal(L/E')` makes `Gal(L/D)` act transitively on the cosets of
`Gal(L/E')`, so the Mackey rank `[D · E' : D]` equals `[E' : E]`. The parity normalizer is then
trivial, the determinant multiple by the trivial character is equality of realizations, and the
raw child realization is a solution. See the paired Markdown.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic

section Generic

/-- If every element of `G` is a product `x * y` with `x ∈ H` and `y ∈ K`, then
`[H : H ∩ K] = [G : K]`: the group `H` acts transitively on `G ⧸ K` and the stabilizer of the
trivial coset is `H ∩ K`. -/
theorem relIndex_eq_index_of_forall_eq_mul {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ g : G, ∃ x ∈ H, ∃ y ∈ K, g = x * y) : K.relIndex H = K.index := by
  have hstab : MulAction.stabilizer H ((1 : G) : G ⧸ K) = K.subgroupOf H := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change ((x * 1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) ↔ _
    rw [QuotientGroup.eq]
    simp
  have horbit : MulAction.orbit H ((1 : G) : G ⧸ K) = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨x, hx, y, hy, rfl⟩ := h g
      refine ⟨⟨x, hx⟩, ?_⟩
      change ((x * 1 : G) : G ⧸ K) = ((x * y : G) : G ⧸ K)
      rw [QuotientGroup.eq]
      simpa using hy
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, horbit, Set.ncard_univ,
    Subgroup.index]

/-- In a finite Galois extension `L/E`, if `Gal(L/E) = Gal(L/D) · Gal(L/K)` (one double coset),
then `[D ⊔ K : D] = [K : E]`. The algebra structure of `D ⊔ K` over `D` is the inclusion, as in
`Proposition48Problem.mackeyRank`. -/
theorem finrank_sup_left_eq_of_forall_eq_mul {E L : Type*} [Field E] [Field L] [Algebra E L]
    [FiniteDimensional E L] [IsGalois E L] (D K : IntermediateField E L)
    (h : ∀ g : L ≃ₐ[E] L, ∃ x ∈ D.fixingSubgroup, ∃ y ∈ K.fixingSubgroup, g = x * y) :
    letI : Algebra D ↥(D ⊔ K) :=
      (IntermediateField.inclusion (show D ≤ D ⊔ K from le_sup_left)).toAlgebra
    Module.finrank D ↥(D ⊔ K) = Module.finrank E K := by
  let : Algebra D ↥(D ⊔ K) :=
    (IntermediateField.inclusion (show D ≤ D ⊔ K from le_sup_left)).toAlgebra
  have : IsScalarTower D ↥(D ⊔ K) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 := Module.finrank_mul_finrank D ↥(D ⊔ K) L
  rw [← IsGalois.card_fixingSubgroup_eq_finrank (D ⊔ K),
    ← IsGalois.card_fixingSubgroup_eq_finrank D, IntermediateField.fixingSubgroup_sup] at h1
  have h2 := Subgroup.relIndex_mul_card K.fixingSubgroup D.fixingSubgroup
  rw [relIndex_eq_index_of_forall_eq_mul h, inf_comm] at h2
  rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := K)]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

end Generic

namespace Proposition48Problem

/-- A single Mackey double coset gives Mackey rank `[E' : E]` at the identity coset. -/
theorem mackeyRank_one_eq_of_card_mackeyIndex (Q : Proposition48Problem.{uF})
    (D : IntermediateField Q.E Q.L) (hQ : Q.IsAuxiliaryValid)
    (hcard : Nat.card (Q.MackeyIndex D) = 1) :
    Q.mackeyRank D 1 = Module.finrank Q.E Q.E' := by
  obtain ⟨-, -, -, hnormal, -⟩ := hQ
  let : IsNormalClosure Q.E Q.E' Q.L := hnormal
  let : Normal Q.E Q.L := IsNormalClosure.normal (K := Q.E')
  let : IsGalois Q.E Q.L := ⟨⟩
  have : Subsingleton (DoubleCoset.Quotient (D.fixingSubgroup : Set (Q.L ≃ₐ[Q.E] Q.L))
      ((Q.conjugateField 1).fixingSubgroup : Set (Q.L ≃ₐ[Q.E] Q.L))) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  have hmul : ∀ g : Q.L ≃ₐ[Q.E] Q.L, ∃ x ∈ D.fixingSubgroup,
      ∃ y ∈ (Q.conjugateField 1).fixingSubgroup, g = x * y := by
    intro g
    have hg : DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup 1 =
        DoubleCoset.mk _ _ g := Subsingleton.elim _ _
    obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.eq.mp hg
    exact ⟨x, hx, y, hy, by rw [mul_one]⟩
  exact (finrank_sup_left_eq_of_forall_eq_mul D (Q.conjugateField 1) hmul).trans
    (Q.conjugateEmbedding 1).equivFieldRange.toLinearEquiv.finrank_eq.symm

end Proposition48Problem

/-- **The equal-rank singleton child.** For an auxiliary-valid problem `Q` whose cyclic step `D`
has a single Mackey double coset, the actual child `R` at the identity coset has the parent rank,
its parity normalizer `ν` is trivial, the raw realization `S` and the normalized realization `T`
have the same class, and the class of `S` is a solution of `R`. -/
theorem proposition48SingletonChildNormalization :
    Proposition48SingletonChildNormalizationStatement.{uF, uV} := by
  intro Q D hQ _ hcard R ν χs r S T _ hrank hnorm hsol
  have hrankEq : Module.finrank R.E R.E' = Module.finrank Q.E Q.E' :=
    hrank.trans (Q.mackeyRank_one_eq_of_card_mackeyIndex D hQ hcard)
  have hν : ν = 1 := hnorm.2.2.1 (by rw [hrankEq])
  subst hν
  obtain ⟨hweak, hdual, hsc, -, hreg, -, -, hdet⟩ := hsol
  have hreal : S.realization = T.realization :=
    OperatorRealization.isDeterminantMultiple_one_iff.mp hdet
  have hST : S = T := by
    obtain ⟨S, _, _⟩ := S
    obtain ⟨T, _, _⟩ := T
    cases hreal
    rfl
  subst hST
  exact ⟨hrankEq, rfl, rfl, hweak, hreg, hdual, hsc⟩

end Langlands.Global.Harris
