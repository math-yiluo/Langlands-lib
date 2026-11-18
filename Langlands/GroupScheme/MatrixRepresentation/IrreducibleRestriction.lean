import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability

/-! # Irreducibility under restriction along a group-scheme isomorphism -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
    {I : Type} [Fintype I] [DecidableEq I]

/-- Irreducibility on all affine tests transports through an actual group isomorphism. -/
theorem IsIrreducible.restrict_iso {ρ : MatrixRepresentation G I}
    (hρ : ρ.IsIrreducible) (e : H ≅ G) :
    (ρ.restrict e.hom).IsIrreducible := by
  refine ⟨hρ.1, fun V hV => hρ.2 V ?_⟩
  intro S x v hv ℓ
  have h := hV S (x ≫ e.inv.hom.hom) v hv ℓ
  have hx : (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x := by
    rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id]
    exact Category.comp_id x
  change (fun i => ℓ (((ρ.affineMatrix S
    ((x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom) : Matrix I I S) *ᵥ
      (fun j => algebraMap k S (v j))) i)) ∈ V at h
  rw [hx] at h
  exact h

end Langlands.GroupScheme.MatrixRepresentation
