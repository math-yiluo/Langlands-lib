import Langlands.Representation.RestrictedTensor.Reindex
import Langlands.Representation.RestrictedTensor.Action
import Mathlib.RepresentationTheory.Intertwining

/-! # Naturality and actions for actual restricted tensor reindexing -/

noncomputable section
open scoped Classical TensorProduct

universe uK uI uJ uG uV uW

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.RestrictedTensor

variable {K : Type uK} [Field K] {ι : Type uI} {κ : Type uJ}
variable {V : κ → Type uV} {W : κ → Type uW}
variable [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
variable [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]

/-- An index equivalence preserves an almost-everywhere reference identity. -/
theorem reindex_preserves (q : ι ≃ κ) {e : ∀ j, V j} {d : ∀ j, W j}
    {f : ∀ j, V j →ₗ[K] W j}
    (hf : ∀ᶠ j in Filter.cofinite, f j (e j) = d j) :
    ∀ᶠ i in Filter.cofinite, f (q i) (e (q i)) = d (q i) :=
  q.injective.tendsto_cofinite.eventually hf

/-- Factor maps commute with actual reindexing, allowing different exceptions
and reference families. No nonzero-reference condition is required. -/
theorem reindexMap_natural (q : ι ≃ κ) (E E' : Finset ι)
    (e : ∀ j, V j) (d : ∀ j, W j) (f : ∀ j, V j →ₗ[K] W j)
    (hf : ∀ᶠ j in Filter.cofinite, f j (e j) = d j) :
    (reindexMap q E' d).comp
        (map E E' (fun i => e (q i)) (fun i => d (q i))
          (fun i => f (q i)) (reindex_preserves q hf)) =
      (map (E.map q.toEmbedding) (E'.map q.toEmbedding) e d f hf).comp
        (reindexMap q E e) := by
  let A := mapBound E' (reindex_preserves q hf)
  let B := mapBound (E'.map q.toEmbedding) hf
  apply hom_ext_cofinal (A ∪ B.map q.symm.toEmbedding)
  intro S hS v
  have hA : A ⊆ S.1 := Finset.subset_union_left.trans hS
  have hB : B ⊆ S.1.map q.toEmbedding := by
    intro j hj
    have hpre : q.symm j ∈ S.1 :=
      hS (Finset.mem_union_right A (Finset.mem_map.mpr ⟨j, hj, rfl⟩))
    exact Finset.mem_map.mpr ⟨q.symm j, hpre, q.apply_symm_apply j⟩
  obtain ⟨x, rfl⟩ :=
    (Equiv.piCongrLeft (fun j : S.1.map q.toEmbedding => V j)
      (reindexFinite q S.1)).symm.surjective v
  simp only [LinearMap.comp_apply]
  rw [map_pure_of_subset E E' (fun i => e (q i)) (fun i => d (q i))
    (fun i => f (q i)) (reindex_preserves q hf) S hA]
  simp only [Equiv.piCongrLeft_symm_apply]
  have hE' : E' ⊆ S.1 := (subset_mapBound E' _).trans hA
  exact (reindexMap_pure (K := K) q E' d ⟨S.1, hE'⟩
    (fun j => f j (x j))).trans
      ((map_pure_of_subset (E.map q.toEmbedding) (E'.map q.toEmbedding)
        e d f hf
        ⟨S.1.map q.toEmbedding, Finset.map_subset_map.mpr S.2⟩ hB x).symm.trans
          (congrArg (map (E.map q.toEmbedding) (E'.map q.toEmbedding) e d f hf)
            (reindexMap_pure (K := K) q E e S x).symm))

variable {G : κ → Type uG} [∀ j, Group (G j)]

/-- Pull back an actual cofinite restricted-product element coordinatewise. -/
def reindexGroup (q : ι ≃ κ) (H : ∀ j, Subgroup (G j)) :
    RestrictedGroup G H →* RestrictedGroup (fun i => G (q i)) (fun i => H (q i)) where
  toFun g := ⟨fun i => g (q i), q.injective.tendsto_cofinite.eventually g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem reindexGroup_apply (q : ι ≃ κ) (H : ∀ j, Subgroup (G j))
    (g : RestrictedGroup G H) (i : ι) :
    reindexGroup q H g i = g (q i) := rfl

/-- Reference fixedness pulls back along the actual finite-set image. -/
theorem reindex_reference_fixed (q : ι ≃ κ) (H : ∀ j, Subgroup (G j))
    (ρ : ∀ j, Representation K (G j) (V j)) (E : Finset ι) (e : ∀ j, V j)
    (he : ∀ j ∉ E.map q.toEmbedding, ∀ g ∈ H j, ρ j g (e j) = e j)
    (i : ι) (hi : i ∉ E) (g : G (q i)) (hg : g ∈ H (q i)) :
    ρ (q i) g (e (q i)) = e (q i) :=
  he (q i) (by simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hi) g hg

/-- Equivariant reindexing of the genuine restricted-product actions. -/
def reindexRepresentationEquiv (q : ι ≃ κ) (H : ∀ j, Subgroup (G j))
    (ρ : ∀ j, Representation K (G j) (V j)) (E : Finset ι) (e : ∀ j, V j)
    (he : ∀ j ∉ E.map q.toEmbedding, ∀ g ∈ H j, ρ j g (e j) = e j)
    (hne : ∀ j ∉ E.map q.toEmbedding, e j ≠ 0) :
    Representation.Equiv
      ((representation (fun i => H (q i)) (fun i => ρ (q i)) E
      (fun i => e (q i)) (reindex_reference_fixed q H ρ E e he)).comp
        (reindexGroup q H))
      (representation H ρ (E.map q.toEmbedding) e he) :=
  Representation.Equiv.mk (reindex q E e hne) (fun g => by
    change (reindexMap q E e).comp
      (map E E (fun i => e (q i)) (fun i => e (q i))
        (fun i => ρ (q i) (g (q i))) _) =
      (map (E.map q.toEmbedding) (E.map q.toEmbedding) e e
        (fun j => ρ j (g j)) _).comp (reindexMap q E e)
    exact reindexMap_natural q E E e e (fun j => ρ j (g j))
      (action_preserves H ρ (E.map q.toEmbedding) e he g))

@[simp]
theorem reindexRepresentationEquiv_apply (q : ι ≃ κ) (H : ∀ j, Subgroup (G j))
    (ρ : ∀ j, Representation K (G j) (V j)) (E : Finset ι) (e : ∀ j, V j)
    (he : ∀ j ∉ E.map q.toEmbedding, ∀ g ∈ H j, ρ j g (e j) = e j)
    (hne : ∀ j ∉ E.map q.toEmbedding, e j ≠ 0)
    (x : Space K (fun i => V (q i)) E (fun i => e (q i))) :
    reindexRepresentationEquiv q H ρ E e he hne x = reindexMap q E e x := rfl

end Langlands.RestrictedTensor
