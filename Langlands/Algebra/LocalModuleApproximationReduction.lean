import Langlands.Algebra.LocalCompatibleMapApproximation
import Langlands.Algebra.LocalModuleApproximationExistenceStatement

/-! # Stacks 00QX from Stacks 00QV (reduction) -/

universe uI uA uB uE uF uR uS uM

namespace Langlands.Algebra

section presentation

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

namespace LocalAlgebraSystem

variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S) {κ : Type uE} {ν : Type uF} [Fintype κ]

/-- The matrices `a` lifted to the component `i₀`, transported along the tail above `i₀`, as a
compatible map of finite free systems over `B.mulVecLin`. -/
def presentationMap (B : Matrix ν κ S) (i₀ : ι) (a : Matrix ν κ (D.alg i₀))
    (ha : a.map (D.algι i₀) = B) :
    LocalModuleSystem.CompatibleMap ((D.tail i₀).freeSystem κ) ((D.tail i₀).freeSystem ν)
      B.mulVecLin :=
  (D.tail i₀).matrixMap (fun j ↦ a.map (D.algMap i₀ j.1 j.2))
    (fun j _ h ↦ by
      ext r c
      exact DirectedSystem.map_map' D.algMap j.2 h (a r c))
    B (fun j ↦ by
      ext r c
      rw [← ha]
      exact D.algι_compat i₀ j.1 j.2 (a r c))

/-- The Stacks 00QX module system `Coker(A_λ)`, `λ ≥ i₀`, for a presentation matrix `B` whose
entries lift to the component `i₀`. -/
noncomputable def presentationSystem (B : Matrix ν κ S) (i₀ : ι) (a : Matrix ν κ (D.alg i₀))
    (ha : a.map (D.algι i₀) = B) :
    LocalModuleSystem (D.tail i₀) ((ν → S) ⧸ LinearMap.range B.mulVecLin) :=
  (D.presentationMap B i₀ a ha).cokernelSystem

/-- Over a ring approximation system, the presentation system is a module approximation
system for the cokernel of `B`. -/
theorem presentationSystem_isApproximation [Finite ν] (hD : D.IsApproximation) (B : Matrix ν κ S)
    (i₀ : ι) (a : Matrix ν κ (D.alg i₀)) (ha : a.map (D.algι i₀) = B) :
    (D.presentationSystem B i₀ a ha).IsApproximation := by
  have hT : (D.tail i₀).IsApproximation := D.tail_isApproximation hD i₀
  have hφ : (D.presentationMap B i₀ a ha).IsApproximation :=
    ⟨(D.tail i₀).freeSystem_isApproximation hT, (D.tail i₀).freeSystem_isApproximation hT⟩
  exact (D.presentationMap B i₀ a ha).cokernelSystem_isApproximation_of_isApproximation hφ

end LocalAlgebraSystem

end presentation

open LocalAlgebraSystem LocalModuleSystem in
/-- Stacks 00QX from Stacks 00QV: a ring approximation system for `R → ULift S` yields a joint
module approximation system for a finitely presented module, as in the Stacks proof. -/
theorem localModuleApproximationExistence_of_localAlgebraApproximationExistence
    (h : LocalAlgebraApproximationExistenceStatement.{uR, max uS uM}) :
    LocalModuleApproximationExistenceStatement.{uR, uS, uM} := by
  intro R S M _ _ _ _ _ _ _ _ hS hM
  have : IsLocalRing (ULift.{uM} S) :=
    IsLocalRing.of_surjective' (ULift.ringEquiv (R := S)).symm.toRingHom
      (ULift.ringEquiv (R := S)).symm.surjective
  have : IsLocalHom (algebraMap R (ULift.{uM} S)) := by
    refine ⟨fun r hr ↦ IsUnit.of_map (algebraMap R S) r ?_⟩
    have := hr.map (ULift.algEquiv : ULift.{uM} S ≃ₐ[R] S)
    rwa [AlgEquiv.commutes] at this
  have hS' : EssFinitePresentation R (ULift.{uM} S) := by
    obtain ⟨n, I, hI, P, ⟨e⟩⟩ := hS
    exact ⟨n, I, hI, P, ⟨e.trans ULift.algEquiv.symm⟩⟩
  obtain ⟨ι, _, _, _, D₀, hD₀⟩ := h R (ULift.{uM} S) hS'
  let D₁ := D₀.mapAlgEquiv (ULift.algEquiv : ULift.{uM} S ≃ₐ[R] S)
  have hD₁ : D₁.IsApproximation := D₀.mapAlgEquiv_isApproximation _ hD₀
  have := hM
  obtain ⟨n, m, A, ⟨eA⟩⟩ := exists_matrix_presentation S M
  obtain ⟨i₀, a, ha⟩ := D₁.exists_algι_eq_fun hD₁.1.2.2 (fun p : Fin n × Fin m ↦ A p.1 p.2)
  have ha' : (Matrix.of fun r c ↦ a (r, c)).map (D₁.algι i₀) = A := by
    ext r c
    exact ha (r, c)
  exact ⟨{j : ι // i₀ ≤ j}, inferInstance, inferInstance, inferInstance, D₁.tail i₀,
    (D₁.presentationSystem A i₀ _ ha').mapLinearEquiv eA,
    (D₁.presentationSystem A i₀ _ ha').mapLinearEquiv_isApproximation eA
      (D₁.presentationSystem_isApproximation hD₁ A i₀ _ ha')⟩

end Langlands.Algebra
