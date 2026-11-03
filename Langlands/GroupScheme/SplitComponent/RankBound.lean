import Langlands.GroupScheme.SplitComponent.ImageTorus

/-! # A bound on the rank of image lattices

If the representing algebra `B'` is of finite type over a field `k`, the image lattices of all
natural homomorphisms from lattice tori into the corepresented functor have bounded rank. Write
`Δ h = ∑ aᵢ ⊗ bᵢ` for generators `h` of `B'`; then every character `[m]` in the support of `ψ h`
lies in the span of the `ψ aᵢ`, so the supports are uniformly bounded, and they generate the image
lattice as a monoid.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.SplitComponent

open Corepresented.LinearEmbedding

section Supported

variable {k : Type u} [Field k] {Λ : Type u} [AddCommGroup Λ]

/-- The subalgebra of elements of `k[Λ]` supported on an additive submonoid. -/
def supportedSubalgebra (P : AddSubmonoid Λ) : Subalgebra k (AddMonoidAlgebra k Λ) where
  carrier := {x | ↑x.coeff.support ⊆ (P : Set Λ)}
  mul_mem' := by
    classical
    intro x y hx hy m hm
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset x y hm)
    exact P.add_mem (hx ha) (hy hb)
  add_mem' := by
    classical
    intro x y hx hy m hm
    rw [Set.mem_ofPred_eq] at hx hy
    rcases Finset.mem_union.mp (Finsupp.support_add hm) with h | h
    · exact hx h
    · exact hy h
  algebraMap_mem' := by
    intro r m hm
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single] at hm
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hm)]
    exact P.zero_mem

theorem mem_supportedSubalgebra {P : AddSubmonoid Λ} {x : AddMonoidAlgebra k Λ} :
    x ∈ supportedSubalgebra P ↔ ↑x.coeff.support ⊆ (P : Set Λ) := Iff.rfl

end Supported

section Bound

variable {k : Type u} [Field k]
  {F' : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}} {B' : CommAlgCat.{u} (CommRingCat.of k)}
  (d : (F' ⋙ forget GrpCat).CorepresentableBy B')

/-- The support of `ψ h` has at most as many elements as a tensor decomposition of `Δ h` has
terms. -/
theorem card_support_le {Λ : Type u} [AddCommGroup Λ]
    (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F') (h : B') (S : Finset (B' × B'))
    (hS : (comul d).hom h = S.sum fun i => i.1 ⊗ₜ[CommRingCat.of k] i.2) :
    ((classify (latticeCorep (CommRingCat.of k) Λ) d α).hom h).coeff.support.card ≤ S.card := by
  classical
  set ψ := (classify (latticeCorep (CommRingCat.of k) Λ) d α).hom
  set T : Finset (AddMonoidAlgebra k Λ) := S.image fun i => ψ i.1
  set V : Submodule k (AddMonoidAlgebra k Λ) := Submodule.span k (T : Set (AddMonoidAlgebra k Λ))
  have hV : ∀ m ∈ (ψ h).coeff.support, AddMonoidAlgebra.single m (1 : k) ∈ V := by
    intro m hm
    have key := coeff_smul_single_eq d α h m
    have hmem : ψ (TensorProduct.rid (CommRingCat.of k) B'
        ((coeffAt m ∘ₗ ψ.toLinearMap).lTensor B' ((comul d).hom h))) ∈ V := by
      rw [hS, map_sum, map_sum, map_sum]
      refine Submodule.sum_mem _ fun i hi => ?_
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_smul]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hi)))
    have hne : (ψ h).coeff m ≠ 0 := Finsupp.mem_support_iff.mp hm
    have hs : (AddMonoidAlgebra.single m (1 : k) : AddMonoidAlgebra k Λ) =
        ((ψ h).coeff m)⁻¹ • ((ψ h).coeff m • AddMonoidAlgebra.single m 1) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hs]
    refine Submodule.smul_mem _ _ ?_
    rw [key]
    exact hmem
  let f : (ψ h).coeff.support → V := fun m => ⟨AddMonoidAlgebra.single m.1 1, hV m.1 m.2⟩
  have hli : LinearIndependent k f := by
    apply LinearIndependent.of_comp V.subtype
    have := (AddMonoidAlgebra.basis Λ k).linearIndependent.comp
      (Subtype.val : (ψ h).coeff.support → Λ) Subtype.val_injective
    convert this using 1
    funext m
    simp [f]
  calc (ψ h).coeff.support.card = Fintype.card (ψ h).coeff.support := by simp
    _ ≤ Module.finrank k V := hli.fintype_card_le_finrank
    _ ≤ T.card := finrank_span_finset_le_card T
    _ ≤ S.card := Finset.card_image_le

/-- Over a field, the image lattices of homomorphisms from lattice tori into a functor
corepresented by an algebra of finite type have uniformly bounded rank. -/
theorem exists_rank_bound (hfin : Algebra.FiniteType (CommRingCat.of k) B') :
    ∃ N : ℕ, ∀ (Λ : Type u) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
      (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F'),
      Module.finrank ℤ (imageSubgroup d α).toIntSubmodule ≤ N := by
  classical
  obtain ⟨s, hs⟩ := hfin.out
  choose S hS using fun h : B' => TensorProduct.exists_finset ((comul d).hom h)
  refine ⟨s.sum fun h => (S h).card, fun Λ _ _ _ α => ?_⟩
  set ψ := (classify (latticeCorep (CommRingCat.of k) Λ) d α).hom
  set F : Finset Λ := s.biUnion fun h => (ψ h).coeff.support
  have hF : F.card ≤ s.sum fun h => (S h).card :=
    (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun h _ => card_support_le d α h (S h) (hS h))
  set P : Submodule ℤ Λ := Submodule.span ℤ (F : Set Λ)
  have hrange : ∀ x ∈ ψ.range, x ∈ supportedSubalgebra P.toAddSubmonoid := by
    intro x hx
    obtain ⟨h, rfl⟩ := (AlgHom.mem_range _).mp hx
    have hh : h ∈ Algebra.adjoin (CommRingCat.of k) (s : Set B') := by
      rw [hs]
      exact Algebra.mem_top
    have hle : Algebra.adjoin (CommRingCat.of k) (s : Set B') ≤
        (supportedSubalgebra (k := k) P.toAddSubmonoid).comap ψ := by
      rw [Algebra.adjoin_le_iff]
      intro h' hh' m hm
      exact Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_biUnion.mpr ⟨h', Finset.mem_coe.mp hh', hm⟩))
    exact hle hh
  have hsub : (imageSubgroup d α).toIntSubmodule ≤ P := by
    intro m hm
    have := hrange _ hm
    rw [mem_supportedSubalgebra, AddMonoidAlgebra.coeff_single] at this
    exact this (by simp)
  calc Module.finrank ℤ (imageSubgroup d α).toIntSubmodule ≤ Module.finrank ℤ P :=
        Submodule.finrank_mono hsub
    _ ≤ F.card := finrank_span_finset_le_card F
    _ ≤ _ := hF

end Bound

end Langlands.GroupScheme.SplitComponent
