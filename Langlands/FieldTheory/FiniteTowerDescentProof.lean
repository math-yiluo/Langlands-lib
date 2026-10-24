import Langlands.FieldTheory.FiniteTowerDescentStatement
import Langlands.FieldTheory.FiniteExtensionDescentProof
import Mathlib.RingTheory.AlgebraTower

namespace Langlands.FieldTheory

open Module

universe u v

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


/-- Compatible descent of a finite separable tower with Galois upper extension. -/
theorem finiteTowerDirectedUnionDescent : FiniteTowerDirectedUnionDescent.{u,v} := by
  classical
  intro U E L _ _ _ _ _ _ _ _ _
  let : Algebra U L := ((algebraMap E L).comp (algebraMap U E)).toAlgebra
  let : IsScalarTower U E L := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional U L := Module.Finite.trans E L
  intro I _ A hdir hcover i₀ sE sL
  let b := Module.finBasis E L
  let t : Finset L := ({1} ∪ sL) ∪
    (Finset.univ.image fun jk : Fin (finrank E L) × Fin (finrank E L) => b jk.1 * b jk.2) ∪
    (Finset.univ.image fun sj : (L ≃ₐ[E] L) × Fin (finrank E L) => sj.1 (b sj.2))
  let coords : Finset E := t.biUnion fun x => Finset.univ.image fun j => b.repr x j
  obtain ⟨i, hi, B, hBfin, hBdeg, hBld, hBtop, hBset, hBsep, _⟩ :=
    finiteExtensionDirectedUnionDescent U E I A hdir hcover i₀ (sE ∪ coords)
  let : Algebra (A i) U := Algebra.ofSubsemiring (A i)
  let : Algebra (A i) E := Algebra.ofSubsemiring (A i)
  let : Algebra (A i) L := Algebra.ofSubsemiring (A i)
  let : IsScalarTower (A i) U E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (A i) U L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (A i) E L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra B L := Algebra.ofSubsemiring B
  let : IsScalarTower B E L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (A i) B L := inferInstance
  let : FiniteDimensional (A i) B := hBfin
  have hcoords {x : L} (hx : x ∈ t) (j : Fin (finrank E L)) : b.repr x j ∈ B :=
    hBset _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨x, hx, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩))
  have h1 : ∀ j, b.repr 1 j ∈ B.toSubfield := hcoords (by simp [t])
  have hmul : ∀ j k l, b.repr (b j * b k) l ∈ B.toSubfield := by
    intro j k
    apply hcoords
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩))
  have hspan : ∃ (C : IntermediateField B L) (c : Basis (Fin (finrank E L)) B C),
      (∀ j, (c j : L) = b j) ∧ (∀ x : L, x ∈ C ↔ ∀ j, b.repr x j ∈ B) :=
    basis_span_field b B.toSubfield h1 hmul
  obtain ⟨C, c, hc, hmem⟩ := hspan
  let : IsScalarTower (A i) C L := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional B C := Module.Finite.of_basis c
  have hCdeg : finrank B C = finrank E L :=
    (Module.finrank_eq_card_basis c).trans (Module.finrank_eq_card_basis b).symm
  have hCgal : IsGalois B C := by
    apply basis_galois b C c hc
    intro σ j
    apply (hmem _).2
    apply hcoords
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨(σ, j), Finset.mem_univ _, rfl⟩)
  have hCld : C.LinearDisjoint E := by
    apply IntermediateField.LinearDisjoint.of_basis_left c
    convert b.linearIndependent using 1
    funext j
    exact hc j
  have hCtop : IntermediateField.adjoin E (C : Set L) = ⊤ := by
    apply top_unique
    intro x _
    rw [← b.sum_repr x]
    apply IntermediateField.sum_mem
    intro j _
    apply IntermediateField.smul_mem
    exact IntermediateField.subset_adjoin E (C : Set L) (hc j ▸ (c j).property)
  let : FiniteDimensional (A i) C := Module.Finite.trans B C
  have hTotalDeg : finrank (A i) C = finrank U L := by
    rw [← finrank_mul_finrank (A i) B C, hBdeg, hCdeg, finrank_mul_finrank U E L]
  let a := Module.finBasis (A i) B
  let d := a.smulTower c
  have hd (jk) : (d jk : L) = (a jk.1 : E) • b jk.2 := by
    simp only [d, Basis.smulTower_apply, IntermediateField.coe_smul, hc]
    rfl
  have hLI : LinearIndependent U ((C.restrictScalars (A i)).val ∘ d) := by
    convert linearIndependent_smul (hBld.linearIndependent_left a.linearIndependent)
      b.linearIndependent using 1
    funext jk
    exact hd jk
  have hTotalLd : (C.restrictScalars (A i)).LinearDisjoint U :=
    IntermediateField.LinearDisjoint.of_basis_left d hLI
  have hcard : Fintype.card (Fin (finrank (A i) B) × Fin (finrank E L)) = finrank U L := by
    rw [← Module.finrank_eq_card_basis d, hTotalDeg]
  let e := basisOfLinearIndependentOfCardEqFinrank'
    ((C.restrictScalars (A i)).val ∘ d) hLI hcard
  have he (j) : e j = (d j : L) := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank'
      ((C.restrictScalars (A i)).val ∘ d) hLI hcard) j
  have hTotalTop : IntermediateField.adjoin U (C : Set L) = ⊤ := by
    apply top_unique
    intro x _
    rw [← e.sum_repr x]
    apply IntermediateField.sum_mem
    intro j _
    apply IntermediateField.smul_mem
    exact IntermediateField.subset_adjoin U (C : Set L) (he j ▸ (d j).property)
  refine ⟨i, hi, B, C, hBfin, hBsep inferInstance, hBdeg, inferInstance, hCgal,
    hCdeg, inferInstance, hTotalDeg, hBld, hBtop, hTotalLd, hTotalTop, hCld, hCtop,
    ?_, ?_, ?_⟩
  · intro x hx
    exact hBset x (Finset.mem_union_left _ hx)
  · intro x hx
    exact (hmem x).2 (hcoords (by simp [t, hx]))
  · exact IsScalarTower.algebraMap_eq B C L |>.symm.trans
      (IsScalarTower.algebraMap_eq B E L)

end Langlands.FieldTheory
