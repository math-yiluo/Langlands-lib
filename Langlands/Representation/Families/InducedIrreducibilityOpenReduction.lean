import Langlands.Representation.Families.GlobalCompressionPrincipalOpen
import Langlands.Representation.Families.InducedTwistsUniformDetectionStatement

/-! # Renard VI.8.4 from uniform detection and a global coefficient family -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenReduction

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme
open Plancherel CompactCompressionPrincipalOpen LocalizedMatrixPrincipalOpen

universe u v uB uV

/-- Uniform detection, together with a coefficient family over the actual
regular functions whose compact fixed vectors are finite free and which
specializes fully to every induced twist, gives the VI.8.4 conclusion for one
irreducible Levi representation. -/
theorem exists_principal_neighborhood_of_detection
    (hdet : InducedTwistsUniformDetectionStatement.{u, v})
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
      haveI : LocallyOfFiniteType M.X.hom := by
        have := hl.isConnectedReductive.smooth
        infer_instance
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible →
      ∀ (B : Type uB) [CommRing B] [Algebra ℂ B]
        (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G))
        [Module B A] [SMulCommClass ℂ B A] [HasCompatibleCoefficients B A.representation]
        (e : B ≃ₐ[ℂ] unramifiedRegularFunctions
          (fun χ : rationalCharacters M => (rationalNormCharacters M χ).toMul)),
        IsGlobalCoefficientFamily A M e (fun ψ =>
          (leviInductionFunctor p l r hp hr hl hmul).obj
            (ρ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))) →
        ∀ ψ₀ : unramifiedCharacters
            (fun χ : rationalCharacters M => (rationalNormCharacters M χ).toMul),
          ((leviInductionFunctor p l r hp hr hl hmul).obj
              (ρ.twist ψ₀.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ₀))).IsIrreducible →
            ∃ f : MvPolynomial (Fin (rationalImageRank M)) ℂ,
              ψ₀ ∈ rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f ∧
                ∀ ψ ∈ rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f,
                  ((leviInductionFunctor p l r hp hr hl hmul).obj
                    (ρ.twist ψ.val.toMonoidHom
                      (unramifiedCharacter_isOpen_ker _ ψ))).IsIrreducible := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul ρ hρ B _ _ A _ _ _ e hA ψ₀ hirr₀
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : LocallyOfFiniteType M.X.hom := by
    have := hl.isConnectedReductive.smooth
    infer_instance
  obtain ⟨K, hK, hKdet⟩ := hdet k G hG P M U p l r hp hl hr hmul ρ hρ
  exact exists_polynomial_principal_neighborhood_of_family A K hK
    M hl.isConnectedReductive e _ hA hKdet ψ₀ hirr₀

end Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenReduction
