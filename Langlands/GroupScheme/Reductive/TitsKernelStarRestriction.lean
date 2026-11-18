import Langlands.GroupScheme.Reductive.TitsKernelWeightRestriction

/-! # Star equivariance of actual weight restriction to an anisotropic kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]

/-- For any automorphism of a root pairing, pairing a transported weight with a
coroot is the pairing of the original weight with the coroot at the index
moved by the inverse permutation. -/
theorem aut_pairing_weightEquiv_coroot {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N) (δ : P.Aut) (x : M) (i : ι) :
    P.toLinearMap (δ.weightEquiv x) (P.coroot i) =
      P.toLinearMap x (P.coroot (δ.indexEquiv.symm i)) := by
  rw [RootPairing.Equiv.toLinearMap_weightEquiv, RootPairing.Equiv.coweightEquiv_apply,
    RootPairing.Hom.coroot_coweightMap_apply]

/-- Pairing a star-transported actual character with a simple coroot is the
pairing of the original character with the coroot at the vertex moved by the
inverse Galois element. -/
theorem pairing_starAction_weight_coroot (d : TitsIndexData G)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (x : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
        d.pinning.torus)) (a : d.Vertex) :
    d.pinning.rootDatum.toLinearMap ((d.pinning.starAction σ).val.weightEquiv x)
        (d.pinning.rootDatum.coroot a.val) =
      d.pinning.rootDatum.toLinearMap x
        (d.pinning.rootDatum.coroot (d.star σ⁻¹ a).val) := by
  have hs : (d.pinning.starAction σ).val.indexEquiv.symm a.val = (d.star σ⁻¹ a).val := by
    change _ = (d.pinning.starAction σ⁻¹).val.indexEquiv a.val
    rw [map_inv]
    rfl
  have h := aut_pairing_weightEquiv_coroot d.pinning.toSplitPinning.rootDatum
    (d.pinning.starAction σ).val x a.val
  rw [hs] at h
  exact h

variable {d : TitsIndexData G} {e : TitsIndexData D} {ι : D ⟶ G}

/-- Restriction of actual integral characters to the kernel torus intertwines
the full absolute star actions of the ambient group and of the kernel. -/
theorem KernelComparison.weightRestriction_starAction (h : d.KernelComparison ι e)
    (he : e.pinning.rootDatum.corootSpan ℤ = ⊤)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (x : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
        d.pinning.torus)) :
    h.weightRestriction ((d.pinning.starAction σ).val.weightEquiv x) =
      (e.pinning.starAction σ).val.weightEquiv (h.weightRestriction x) := by
  apply IntegralWeylVector.eq_of_pairing_simple_eq e.pinning.rootDatum e.pinning.base he
  intro b
  rw [h.pairing_weightRestriction_simple, pairing_starAction_weight_coroot,
    e.pairing_starAction_weight_coroot, h.pairing_weightRestriction_simple,
    h.vertexEquiv_star]
  rfl

/-- Restriction to the kernel carries a weight fixed by the full ambient star
action to a weight fixed by the full star action of the kernel. -/
theorem KernelComparison.weightRestriction_starFixed (h : d.KernelComparison ι e)
    (he : e.pinning.rootDatum.corootSpan ℤ = ⊤)
    {x : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
        d.pinning.torus)}
    (hx : ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      (d.pinning.starAction σ).val.weightEquiv x = x)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    (e.pinning.starAction σ).val.weightEquiv (h.weightRestriction x) =
      h.weightRestriction x := by
  rw [← h.weightRestriction_starAction he, hx σ]

end Langlands.GroupScheme.TitsIndexData
