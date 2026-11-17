import Langlands.CommutativeAlgebra.DiagonalIsomorphismLocus
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Local character descriptions of diagonal bialgebra automorphisms -/

noncomputable section

universe u v w x y

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.CommutativeAlgebra.DiagonalAutomorphismLocality

open DiagonalIsomorphismLocus

variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}
  [AddCommGroup M] [AddCommGroup N]

/-- Scalar extension of a diagonal bialgebra equivalence remains an equivalence. -/
def scalarExtensionEquiv
    (e : AddMonoidAlgebra R N ≃ₐc[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] :
    AddMonoidAlgebra A N ≃ₐc[A] AddMonoidAlgebra A M := by
  let E : AddMonoidAlgebra A N ≃ₐ[A] AddMonoidAlgebra A M :=
    (AddMonoidAlgebra.scalarTensorEquiv R A (M := N)).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) e.toAlgEquiv).trans
        (AddMonoidAlgebra.scalarTensorEquiv R A (M := M)))
  have hE : (scalarExtension e.toBialgHom A).toAlgHom = E.toAlgHom := by
    apply AddMonoidAlgebra.algHom_ext
    · intro n
      simp [E, scalarExtension, scalarExtensionAlgHom]
    · ext
  apply BialgEquiv.ofBijective (scalarExtension e.toBialgHom A)
  have hf : (scalarExtension e.toBialgHom A : AddMonoidAlgebra A N →
      AddMonoidAlgebra A M) = E := congrArg DFunLike.coe hE
  rw [hf]
  exact E.bijective

@[simp] theorem scalarExtensionEquiv_toBialgHom
    (e : AddMonoidAlgebra R N ≃ₐc[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] :
    (scalarExtensionEquiv e A).toBialgHom = scalarExtension e.toBialgHom A := by
  ext z
  rfl

/-- At any field-valued point, one character equivalence is forced on a
principal neighborhood, uniformly after arbitrary scalar extension. -/
theorem exists_character_certificate [AddMonoid.FG N]
    (e : AddMonoidAlgebra R N ≃ₐc[R] AddMonoidAlgebra R M)
    (K : Type x) [Field K] [Algebra R K] :
    ∃ (g : N ≃+ M) (r : R), algebraMap R K r ≠ 0 ∧
      ∀ (A : Type y) [CommRing A] [Algebra R A],
        IsUnit (algebraMap R A r) →
          (scalarExtension e.toBialgHom A).toAlgHom =
            AddMonoidAlgebra.mapDomainAlgHom A A g.toAddMonoidHom := by
  classical
  obtain ⟨s, hs⟩ := AddMonoid.FG.fg_top (M := N)
  let g : N ≃+ M := characterEquiv (scalarExtensionEquiv e K)
  have hg (n : N) :
      g n = AddMonoidAlgebra.mapDomainOfBialgHom (scalarExtension e.toBialgHom K) n := by
    change AddMonoidAlgebra.mapDomainOfBialgHom
      (scalarExtensionEquiv e K).toBialgHom n = _
    rw [scalarExtensionEquiv_toBialgHom]
  refine ⟨g, generatorCoefficientProduct e.toBialgHom g.toAddMonoidHom s, ?_, ?_⟩
  · have hr : algebraMap R K
        (generatorCoefficientProduct e.toBialgHom g.toAddMonoidHom s) = 1 := by
      simp only [generatorCoefficientProduct, map_prod]
      apply Finset.prod_eq_one
      intro n _
      change algebraMap R K
        ((e (AddMonoidAlgebra.single n 1)).coeff (g n)) = 1
      rw [hg]
      exact field_character_coefficient e.toBialgHom K n
    rw [hr]
    exact one_ne_zero
  · exact fun A _ _ hr =>
      scalarExtension_eq_mapDomain_of_isUnit e.toBialgHom g.toAddMonoidHom s hs A hr

/-- The character description is valid on a principal neighborhood of any prime. -/
theorem exists_character_certificate_at_prime [AddMonoid.FG N]
    (e : AddMonoidAlgebra R N ≃ₐc[R] AddMonoidAlgebra R M)
    (p : Ideal R) [p.IsPrime] :
    ∃ (g : N ≃+ M) (r : R), r ∉ p ∧
      ∀ (A : Type x) [CommRing A] [Algebra R A],
        IsUnit (algebraMap R A r) →
          (scalarExtension e.toBialgHom A).toAlgHom =
            AddMonoidAlgebra.mapDomainAlgHom A A g.toAddMonoidHom := by
  obtain ⟨g, r, hr, hg⟩ := exists_character_certificate e p.ResidueField
  exact ⟨g, r, fun hp => hr (Ideal.algebraMap_residueField_eq_zero.mpr hp), hg⟩

/-- Chosen local character-equivalence data at a prime, with its uniform
scalar-extension identity. -/
def characterCertificateAtPrime [AddMonoid.FG N]
    (e : AddMonoidAlgebra R N ≃ₐc[R] AddMonoidAlgebra R M)
    (p : Ideal R) [p.IsPrime] :
    Σ g : N ≃+ M, {r : R // r ∉ p ∧
      ∀ (A : Type x) [CommRing A] [Algebra R A],
        IsUnit (algebraMap R A r) →
          (scalarExtension e.toBialgHom A).toAlgHom =
            AddMonoidAlgebra.mapDomainAlgHom A A g.toAddMonoidHom} :=
  let h := exists_character_certificate_at_prime e p
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

end Langlands.CommutativeAlgebra.DiagonalAutomorphismLocality
