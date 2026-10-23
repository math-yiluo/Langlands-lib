import Langlands.FieldTheory.FiniteExtensionDescentStatement
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.FieldTheory.SeparableClosure

namespace Langlands.FieldTheory

open Module

universe u v

private theorem finite_subset_stage {L : Type u} [Field L] {I : Type v}
    (A : I → Subfield L) (hdir : Directed (· ≤ ·) A)
    (hcover : ∀ x : L, ∃ i, x ∈ A i) (i₀ : I) (s : Finset L) :
    ∃ i, A i₀ ≤ A i ∧ ∀ x ∈ s, x ∈ A i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨i₀, le_rfl, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨i, hi, hs⟩ := ih
    obtain ⟨j, hj⟩ := hcover x
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, hi.trans hik, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hjk hj
    · exact hik (hs y hy)

private theorem basis_span_field {L M : Type u} [Field L] [Field M]
    [Algebra L M] {ι : Type*} [Fintype ι] (b : Basis ι L M)
    (F : Subfield L)
    (h1 : ∀ k, b.repr 1 k ∈ F)
    (hmul : ∀ j k l, b.repr (b j * b k) l ∈ F) :
    let : Algebra F L := Algebra.ofSubsemiring F
    let : Algebra F M := Algebra.ofSubsemiring F
    let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq' rfl
    ∃ (B : IntermediateField F M) (c : Basis ι F B),
      (∀ j, (c j : M) = b j) ∧
      (∀ x : M, x ∈ B ↔ ∀ j, b.repr x j ∈ F) := by
  classical
  let : Algebra F L := Algebra.ofSubsemiring F
  let : Algebra F M := Algebra.ofSubsemiring F
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq' rfl
  let V := Submodule.span F (Set.range b)
  have hmem (x : M) : x ∈ V ↔ ∀ j, b.repr x j ∈ F := by
    rw [b.mem_span_iff_repr_mem F]
    simp only [Algebra.algebraMap_ofSubsemiring_apply, Set.mem_range, Subtype.exists,
      exists_prop, exists_eq_right]
  have hmul' (x y : M) (hx : x ∈ V) (hy : y ∈ V) : x * y ∈ V := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact (hmem _).2 (hmul j k)
      | zero => simp
      | add y z hy hz iy iz => simpa [mul_add] using V.add_mem iy iz
      | smul a y hy iy => simpa [mul_smul_comm] using V.smul_mem a iy
    | zero => simp
    | add x z hx hz ix iz => simpa [add_mul] using V.add_mem ix iz
    | smul a x hx ix => simpa [smul_mul_assoc] using V.smul_mem a ix
  let S : Subalgebra F M :=
    { V with
      one_mem' := (hmem 1).2 h1
      mul_mem' := fun hx hy => hmul' _ _ hx hy
      algebraMap_mem' := fun a => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact V.smul_mem a ((hmem 1).2 h1) }
  let : FiniteDimensional F S := FiniteDimensional.span_of_finite F (Set.finite_range b)
  let B : IntermediateField F M := Algebra.IsAlgebraic.toIntermediateField S
  let c : Basis ι F B := b.restrictScalars F
  refine ⟨B, c, ?_, ?_⟩
  · exact b.restrictScalars_apply F
  · exact hmem

private theorem separable_of_minpoly_coeffs {L M : Type u} [Field L] [Field M]
    [Algebra L M] (F : Subfield L) (x : M) (hx : IsSeparable L x)
    (hcoeff : ∀ n, (minpoly L x).coeff n ∈ F) :
    let : Algebra F M := Algebra.ofSubsemiring F
    IsSeparable F x := by
  let : Algebra F L := Algebra.ofSubsemiring F
  let : Algebra F M := Algebra.ofSubsemiring F
  obtain ⟨p, hp⟩ := (Polynomial.mem_map_range F.subtype).2 (fun n =>
    ⟨⟨_, hcoeff n⟩, rfl⟩)
  have hp' : p.map F.subtype = minpoly L x := hp
  have hsep : p.Separable := (Polynomial.separable_map F.subtype).1 (hp' ▸ hx)
  exact hsep.of_dvd (minpoly.dvd F x (by
    rw [Polynomial.aeval_eq_aeval_map (φ := F.subtype) rfl, hp']
    exact minpoly.aeval L x))

private theorem basis_separable {F M : Type u} [Field F] [Field M] [Algebra F M]
    {ι : Type*} [Fintype ι] (B : IntermediateField F M) (c : Basis ι F B)
    (hsep : ∀ j, IsSeparable F (c j : M)) : Algebra.IsSeparable F B := by
  apply (le_separableClosure_iff F M B).1
  intro x hx
  have heq := congrArg (fun y : B => (y : M)) (c.sum_repr ⟨x, hx⟩)
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at heq
  rw [← heq]
  exact (separableClosure F M).sum_mem fun j _ =>
    (separableClosure F M).smul_mem (hsep j)

private theorem basis_galois {F L M : Type u} [Field F] [Field L] [Field M]
    [Algebra F L] [Algebra L M] [Algebra F M] [IsScalarTower F L M]
    [FiniteDimensional L M] [IsGalois L M]
    {ι : Type*} [Fintype ι] (b : Basis ι L M)
    (B : IntermediateField F M) (c : Basis ι F B)
    (hc : ∀ j, (c j : M) = b j)
    (hinv : ∀ (σ : M ≃ₐ[L] M) j, σ (b j) ∈ B) : IsGalois F B := by
  classical
  let : FiniteDimensional F B := Module.Finite.of_basis c
  have hmap (σ : M ≃ₐ[L] M) (x : B) : σ (x : M) ∈ B := by
    have heq := congrArg (fun y : B => (y : M)) (c.sum_repr x)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at heq
    rw [← heq, map_sum]
    refine B.sum_mem fun j _ => ?_
    have hsmul : σ (c.repr x j • (c j : M)) = c.repr x j • σ (c j : M) := by
      simpa only [AlgEquiv.toLinearMap_apply, AlgEquiv.restrictScalars_apply] using
        (σ.restrictScalars F).toLinearMap.map_smul (c.repr x j) (c j : M)
    rw [hsmul]
    exact B.smul_mem (hc j ▸ hinv σ j)
  let f (σ : M ≃ₐ[L] M) : B →ₐ[F] B :=
    (((σ.restrictScalars F).toAlgHom).comp B.val).codRestrict B.toSubalgebra (hmap σ)
  have hf : Function.Injective f := by
    intro σ τ h
    have hlin : σ.toLinearMap = τ.toLinearMap := b.ext fun j => by
      have hj := congrArg (fun g : B →ₐ[F] B => (g (c j) : M)) h
      change σ (c j : M) = τ (c j : M) at hj
      simpa only [hc, AlgEquiv.toLinearMap_apply] using hj
    ext x
    exact LinearMap.congr_fun hlin x
  apply IsGalois.of_card_aut_eq_finrank
  rw [Nat.card_congr (algEquivEquivAlgHom F B).toEquiv]
  apply le_antisymm
  · simpa only [Nat.card_eq_fintype_card] using (AlgHom.card_le (F := F) (K := B))
  · have h := Fintype.card_le_of_injective f hf
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank] at h
    simpa only [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c,
      Nat.card_eq_fintype_card] using h

/-- Finite extensions descend to a stage of a directed union, with the full
same-witness degree, finite-set, separability and Galois refinements. -/
theorem finiteExtensionDirectedUnionDescent : FiniteExtensionDirectedUnionDescent.{u,v} := by
  classical
  intro L M _ _ _ _ I _ A hdir hcover i₀ s
  let b := Module.finBasis L M
  let t : Finset M := ({1} ∪ s) ∪
    (Finset.univ.image fun jk : Fin (finrank L M) × Fin (finrank L M) => b jk.1 * b jk.2) ∪
    (Finset.univ.image fun sj : (M ≃ₐ[L] M) × Fin (finrank L M) => sj.1 (b sj.2))
  let coords : Finset L := t.biUnion fun x => Finset.univ.image fun j => b.repr x j
  let polys : Finset L := Finset.univ.biUnion fun j =>
    (minpoly L (b j)).support.image (minpoly L (b j)).coeff
  obtain ⟨i, hi, hstage⟩ := finite_subset_stage A hdir hcover i₀ (coords ∪ polys)
  have hcoords {x : M} (hx : x ∈ t) (j : Fin (finrank L M)) : b.repr x j ∈ A i :=
    hstage _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨x, hx, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩))
  have hpoly (j : Fin (finrank L M)) (n : ℕ) : (minpoly L (b j)).coeff n ∈ A i := by
    by_cases hn : n ∈ (minpoly L (b j)).support
    · exact hstage _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ j, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩))
    · have hn0 : (minpoly L (b j)).coeff n = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hn
      simpa only [hn0] using (A i).zero_mem
  have h1 : ∀ j, b.repr 1 j ∈ A i := hcoords (by simp [t])
  have hmul : ∀ j k l, b.repr (b j * b k) l ∈ A i := by
    intro j k
    apply hcoords
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩))
  let : Algebra (A i) L := Algebra.ofSubsemiring (A i)
  let : Algebra (A i) M := Algebra.ofSubsemiring (A i)
  let : IsScalarTower (A i) L M := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨B, c, hc, hmem⟩ := basis_span_field b (A i) h1 hmul
  let : FiniteDimensional (A i) B := Module.Finite.of_basis c
  refine ⟨i, hi, B, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Module.finrank_eq_card_basis c).trans (Module.finrank_eq_card_basis b).symm
  · apply IntermediateField.LinearDisjoint.of_basis_left c
    convert b.linearIndependent using 1
    funext j
    exact hc j
  · apply top_unique
    intro x _
    rw [← b.sum_repr x]
    apply IntermediateField.sum_mem
    intro j _
    apply IntermediateField.smul_mem
    exact IntermediateField.subset_adjoin L (B : Set M) (hc j ▸ (c j).property)
  · intro x hx
    exact (hmem x).2 (hcoords (by simp [t, hx]))
  · intro hsep
    let : Algebra.IsSeparable L M := hsep
    apply basis_separable B c
    intro j
    rw [hc]
    exact separable_of_minpoly_coeffs (A i) (b j)
      (Algebra.IsSeparable.isSeparable L (b j)) (hpoly j)
  · intro hgal
    let : IsGalois L M := hgal
    apply basis_galois b B c hc
    intro σ j
    apply (hmem _).2
    apply hcoords
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨(σ, j), Finset.mem_univ _, rfl⟩)

end Langlands.FieldTheory
