import Langlands.Algebra.HopfPointRigidity
import Langlands.Algebra.HopfPointClosedLocus

/-! # Kernels of bounded Hopf points are determined modulo `m` -/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.HopfPointKernel

open HopfPointExtension HopfPointRigidity HopfPointClosedLocus LatticeConfiguration

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {C : Type*} [CommRing C] [Algebra R C] {r : Type*} [Fintype r] [DecidableEq r]
  {σ : Type*}

theorem scalarExt_comp_mapDomain {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (T : M →+ N) (α : A →ₐ[R] AddMonoidAlgebra C M) :
    scalarExt ((AddMonoidAlgebra.mapDomainAlgHom R C T).comp α) =
      (AddMonoidAlgebra.mapDomainAlgHom C C T).comp (scalarExt α) := by
  apply Algebra.TensorProduct.ext'
  intro c a
  simp [scalarExt_tmul, AddMonoidAlgebra.mapDomainAlgHom_apply]

/-- Changing the basis of the character lattice does not change the kernel of the
scalar extension. -/
theorem ker_scalarExt_mapDomain_addEquiv {M : Type*} [AddCommGroup M] (T : M ≃+ M)
    (α : A →ₐ[R] AddMonoidAlgebra C M) :
    RingHom.ker (scalarExt ((AddMonoidAlgebra.mapDomainAlgHom R C T.toAddMonoidHom).comp α)) =
      RingHom.ker (scalarExt α) := by
  rw [scalarExt_comp_mapDomain]
  ext x
  simp only [RingHom.mem_ker, AlgHom.comp_apply]
  constructor
  · intro h
    have hinj : Function.Injective (AddMonoidAlgebra.mapDomainAlgHom C C T.toAddMonoidHom) := by
      intro a b hab
      apply AddMonoidAlgebra.coeff_injective
      exact Finsupp.mapDomain_injective T.injective (congrArg AddMonoidAlgebra.coeff hab)
    exact hinj (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

/-- Rigidity for kernels: under the hypotheses of `exists_addEquiv_of_red_eq`, the two
Hopf points have the same kernel after scalar extension. -/
theorem ker_scalarExt_eq_of_red_eq {n m : ℕ} (hm : rigidityBound r n ≤ m)
    {gen : σ → A} (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    {α α' : A →ₐ[R] AddMonoidAlgebra C (r → ℤ)}
    (hα : ∀ i, ↑(α (gen i)).coeff.support ⊆ (box r n : Set (r → ℤ)))
    (hα' : ∀ i, ↑(α' (gen i)).coeff.support ⊆ (box r n : Set (r → ℤ)))
    (hgα : AddSubgroup.closure (⋃ i, (↑(α (gen i)).coeff.support : Set (r → ℤ))) = ⊤)
    (hgα' : AddSubgroup.closure (⋃ i, (↑(α' (gen i)).coeff.support : Set (r → ℤ))) = ⊤)
    (γ : (r → ZMod m) ≃+ (r → ZMod m))
    (h : (AddMonoidAlgebra.mapDomainAlgHom R C (red r m)).comp α' =
      (AddMonoidAlgebra.mapDomainAlgHom R C γ.toAddMonoidHom).comp
        ((AddMonoidAlgebra.mapDomainAlgHom R C (red r m)).comp α)) :
    RingHom.ker (scalarExt α') = RingHom.ker (scalarExt α) := by
  obtain ⟨T, hT⟩ := exists_addEquiv_of_red_eq hm hgen hα hα' hgα hgα' γ h
  rw [← hT, ker_scalarExt_mapDomain_addEquiv]

/-- Freeness: a closed-immersion Hopf point over a nonzero ring is fixed by no
nontrivial automorphism of the character group. -/
theorem eq_refl_of_mapDomain_comp_eq [Nontrivial C] {M : Type*} [AddCommGroup M]
    {β : A →ₐ[R] AddMonoidAlgebra C M} (hsurj : Function.Surjective (scalarExt β))
    (ε : M ≃+ M) (h : (AddMonoidAlgebra.mapDomainAlgHom R C ε.toAddMonoidHom).comp β = β) :
    ε = AddEquiv.refl M := by
  ext χ
  obtain ⟨x, hx⟩ := hsurj (AddMonoidAlgebra.single χ 1)
  have key : scalarExt ((AddMonoidAlgebra.mapDomainAlgHom R C ε.toAddMonoidHom).comp β) x =
      scalarExt β x := by rw [h]
  rw [scalarExt_comp_mapDomain, AlgHom.comp_apply, hx,
    AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single] at key
  have h1 : (ε χ : M) = χ := by
    by_contra hne
    have := congrArg (fun y => y.coeff (ε χ)) key
    simp only [AddMonoidAlgebra.coeff_single] at this
    change (Finsupp.single (ε χ) (1 : C)) (ε χ) = (Finsupp.single χ (1 : C)) (ε χ) at this
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne] at this
    exact one_ne_zero this
  exact h1

end Langlands.Algebra.HopfPointKernel
