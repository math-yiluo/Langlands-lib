import Langlands.GroupScheme.Reductive.TitsIndexAnisotropicKernelIndexProof
import Langlands.GroupScheme.Reductive.TitsIndexStarProof

/-! # Simple vertices of the actual anisotropic-kernel subdiagram -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
  {d : TitsIndexData G} {e : TitsIndexData D} {ι : D ⟶ G}

/-- The actual full star action restricted to the zero-restriction vertices. -/
def zeroStar (d : TitsIndexData G)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (a : d.zeroVertices) : d.zeroVertices :=
  ⟨d.star σ a.val, (titsIndexStarInvariant k G d σ a.val).mpr a.property⟩

/-- A kernel comparison identifies the kernel's actual simple vertices with
exactly the ambient zero-restriction simple vertices. -/
def KernelComparison.vertexEquiv (h : d.KernelComparison ι e) :
    e.Vertex ≃ d.zeroVertices := by
  let φ := h.choose_spec.choose
  have hbase := h.choose_spec.choose_spec.2.2.2.2.1
  refine
    { toFun := fun a =>
        ⟨⟨(φ a.val).val, (hbase a.val).mp a.property⟩, (φ a.val).property⟩
      invFun := fun a =>
        ⟨φ.symm ⟨a.val.val, a.property⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply (hbase _).mpr
    change (φ (φ.symm ⟨a.val.val, a.property⟩)).val ∈ d.pinning.base.support
    simpa only [Equiv.apply_symm_apply] using a.val.property
  · intro a
    apply Subtype.ext
    exact φ.symm_apply_apply a.val
  · intro a
    apply Subtype.ext
    apply Subtype.ext
    change (φ (φ.symm ⟨a.val.val, a.property⟩)).val = a.val.val
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨a.val.val, a.property⟩)

/-- The simple-vertex equivalence preserves every integral Cartan entry. -/
theorem KernelComparison.vertexEquiv_cartan (h : d.KernelComparison ι e)
    (a b : e.Vertex) :
    d.cartan (h.vertexEquiv a).val (h.vertexEquiv b).val = e.cartan a b :=
  (h.choose_spec.choose_spec.2.2.2.1 a.val b.val).symm

/-- The simple-vertex equivalence intertwines every full absolute Galois element. -/
theorem KernelComparison.vertexEquiv_star (h : d.KernelComparison ι e)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : e.Vertex) :
    h.vertexEquiv (e.star σ a) = d.zeroStar σ (h.vertexEquiv a) := by
  apply Subtype.ext
  apply Subtype.ext
  exact h.choose_spec.choose_spec.2.2.2.2.2 σ a.val a.property

/-- Number the actual ambient zero vertices using a numbering of the kernel. -/
def KernelComparison.zeroNumbering (h : d.KernelComparison ι e) {n : ℕ}
    (q : e.Vertex ≃ Fin n) : d.zeroVertices ≃ Fin n :=
  h.vertexEquiv.symm.trans q

/-- Transport a kernel Cartan matrix to the actual ambient zero subdiagram. -/
theorem KernelComparison.zeroNumbering_cartan (h : d.KernelComparison ι e)
    {n : ℕ} (q : e.Vertex ≃ Fin n) {M : Matrix (Fin n) (Fin n) ℤ}
    (hq : ∀ a b, e.cartan a b = M (q a) (q b)) (a b : d.zeroVertices) :
    d.cartan a.val b.val = M (h.zeroNumbering q a) (h.zeroNumbering q b) := by
  calc
    d.cartan a.val b.val =
        e.cartan (h.vertexEquiv.symm a) (h.vertexEquiv.symm b) := by
      simpa only [Equiv.apply_symm_apply] using
        h.vertexEquiv_cartan (h.vertexEquiv.symm a) (h.vertexEquiv.symm b)
    _ = M (h.zeroNumbering q a) (h.zeroNumbering q b) := hq _ _

/-- The transported numbering retains the actual full-star permutation. -/
theorem KernelComparison.zeroNumbering_star (h : d.KernelComparison ι e)
    {n : ℕ} (q : e.Vertex ≃ Fin n)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.zeroVertices) :
    h.zeroNumbering q (d.zeroStar σ a) =
      q (e.star σ (h.vertexEquiv.symm a)) := by
  change q (h.vertexEquiv.symm (d.zeroStar σ a)) = _
  congr 1
  apply h.vertexEquiv.injective
  rw [Equiv.apply_symm_apply, h.vertexEquiv_star, Equiv.apply_symm_apply]

/-- Triviality of the kernel's full star action is exactly triviality on all
ambient zero vertices. -/
theorem KernelComparison.star_trivial_iff (h : d.KernelComparison ι e) :
    (∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : e.Vertex),
      e.star σ a = a) ↔
    ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.zeroVertices),
      d.star σ a.val = a.val := by
  constructor
  · intro he σ a
    obtain ⟨b, rfl⟩ := h.vertexEquiv.surjective a
    have hb := h.vertexEquiv_star σ b
    rw [he σ b] at hb
    exact (congrArg (fun x : d.zeroVertices => x.val) hb).symm
  · intro hd σ a
    apply h.vertexEquiv.injective
    rw [h.vertexEquiv_star]
    apply Subtype.ext
    exact hd σ (h.vertexEquiv a)

end Langlands.GroupScheme.TitsIndexData
