import Langlands.GroupScheme.Torus.CocharacterDatum
import Langlands.GroupScheme.Torus.CocharacterCoefficientDescent

/-! # Galois descent of cocharacter data

A cocharacter datum over a finite Galois extension `N / k` gives one over `k`: the product of its
Galois conjugates is fixed by the Galois group, so its coordinates descend to `k[Λ]`. The weight
gets multiplied by the order of the Galois group.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterDatum

set_option backward.isDefEq.respectTransparency false

variable {k N : Type u} [Field k] [Field N] [Algebra k N] [FiniteDimensional k N]
variable {Z : CommGroupScheme (Spec (CommRingCat.of k))} {Λ : Type u} [AddCommGroup Λ]

variable (k) in
/-- The **Galois norm** of a point over `N[Λ]`: the product of its conjugates under all
`k`-automorphisms of `N`, acting on coefficients. -/
def galoisNorm (p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra N Λ)) :
    Lie.AffinePoints Z.toGrp (AddMonoidAlgebra N Λ) :=
  ∏ σ : N ≃ₐ[k] N, coeffMap (σ : N →ₐ[k] N) p

omit [FiniteDimensional k N] in
theorem mapAlgHom_comp_mapAlgHom_algEquiv (τ σ : N ≃ₐ[k] N) :
    (AddMonoidAlgebra.mapAlgHom Λ (τ : N →ₐ[k] N)).comp
        (AddMonoidAlgebra.mapAlgHom Λ (σ : N →ₐ[k] N)) =
      AddMonoidAlgebra.mapAlgHom Λ ((τ * σ : N ≃ₐ[k] N) : N →ₐ[k] N) := by
  apply AlgHom.ext
  intro a
  ext γ
  simp [AddMonoidAlgebra.coeff_mapAlgHom, AlgEquiv.mul_apply]

omit [FiniteDimensional k N] in
theorem coeffMap_coeffMap_algEquiv (τ σ : N ≃ₐ[k] N)
    (p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra N Λ)) :
    coeffMap (τ : N →ₐ[k] N) (coeffMap (σ : N →ₐ[k] N) p) =
      coeffMap ((τ * σ : N ≃ₐ[k] N) : N →ₐ[k] N) p := by
  rw [coeffMap, coeffMap, coeffMap, ← Lie.affineMap_comp, mapAlgHom_comp_mapAlgHom_algEquiv]

/-- The Galois norm is fixed by every `k`-automorphism of `N`. -/
theorem coeffMap_galoisNorm (τ : N ≃ₐ[k] N) (p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra N Λ)) :
    coeffMap (τ : N →ₐ[k] N) (galoisNorm k p) = galoisNorm k p := by
  rw [galoisNorm, map_prod]
  simp_rw [coeffMap_coeffMap_algEquiv]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl

/-- The coordinates of the Galois norm come from `k[Λ]`. -/
theorem coord_galoisNorm_mem [IsGalois k N] [IsAffine Z.toGrp.X.left]
    (p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra N Λ)) (c : coordAlgebra Z.toGrp) :
    (coord (galoisNorm k p)).hom c ∈ (AddMonoidAlgebra.mapAlgHom Λ (Algebra.ofId k N)).range := by
  obtain ⟨y, hy⟩ := CocharacterDescent.exists_mapAlgHom_ofId_eq_of_isGalois
    ((coord (galoisNorm k p)).hom c) fun σ : N ≃ₐ[k] N => by
      have h := congrArg (fun φ => φ.hom c)
        (coord_affineMap (AddMonoidAlgebra.mapAlgHom Λ (σ : N →ₐ[k] N)) (galoisNorm k p))
      change (coord (coeffMap (σ : N →ₐ[k] N) (galoisNorm k p))).hom c = _ at h
      rw [coeffMap_galoisNorm] at h
      exact h.symm
  exact ⟨y, hy⟩

/-- **Galois descent of cocharacter data.** A cocharacter datum of weight `m` over a finite Galois
extension `N / k` gives a cocharacter datum over `k` of weight `[N : k] • m`, where the multiplier
is the order of the Galois group. -/
theorem IsDatum.exists_of_isGalois [IsGalois k N] [IsAffine Z.toGrp.X.left]
    {χ : characterLattice Z} {m : Λ} {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra N Λ)}
    (hp : IsDatum χ m p) :
    ∃ p' : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra k Λ),
      IsDatum χ (Nat.card (N ≃ₐ[k] N) • m) p' := by
  have hν : IsDatum χ (Nat.card (N ≃ₐ[k] N) • m) (galoisNorm k p) := by
    have h := IsDatum.prod Finset.univ (fun _ => m)
      (fun σ : N ≃ₐ[k] N => coeffMap (σ : N →ₐ[k] N) p) fun σ _ => hp.coeff_map _
    rwa [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card] at h
  have hinj : Function.Injective (Algebra.ofId k N) := fun x y h => (algebraMap k N).injective h
  obtain ⟨p', hp'⟩ := exists_affineMap_eq _ (mapAlgHom_injective _ hinj) (galoisNorm k p)
    (coord_galoisNorm_mem p)
  refine ⟨p', IsDatum.of_coeff_map (Algebra.ofId k N) hinj ?_⟩
  change IsDatum χ _ (Lie.affineMap Z.toGrp (AddMonoidAlgebra.mapAlgHom Λ (Algebra.ofId k N)) p')
  rw [hp']
  exact hν

end Langlands.GroupScheme.CocharacterDatum
