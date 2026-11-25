import Langlands.Geometry.Building.UnramifiedZeroDescentStatement
import Langlands.Geometry.Building.UnramifiedCharacterValuationKernelGaloisStability
import Langlands.Geometry.Building.UnramifiedZeroPointsGaloisStability
import Langlands.Geometry.Building.UnramifiedZeroGeometry
import Langlands.Geometry.Building.UnramifiedZeroFacetNoInversionsProof
import Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceProof
import Langlands.Geometry.Building.UnramifiedApartmentDescentProof
import Mathlib.Tactic.Convert

/-! # Galois stability and descent of the unramified zero subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-! The first two clauses of `UnramifiedZeroDescentStatement`, stated as there. In the
elaborated statement some instance arguments are auxiliary proof terms; the assembly below
matches these clauses against it with `convert … using 0`, which compares the proof arguments
by proof irrelevance. -/

/-- Coefficient conjugation preserves `G(K)^1`, in the form of the first clause of
`UnramifiedZeroDescentStatement`. -/
private theorem galoisStable_characterValuationKernel (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) :
    ∀ σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F,
      ∀ x ∈ characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (UnramifiedClosure F) G),
        rationalConjugate F (UnramifiedClosure F) G σ x ∈
          characterValuationKernel (MaximalUnramified.valuation F)
            (baseChanged F (UnramifiedClosure F) G) :=
  fun σ x hx => (unramified_characterValuationKernel_galois_iff F G σ x).mpr hx

/-- Coefficient conjugation preserves `G(K)^0` for every upstairs zero datum, in the form of
the second clause of `UnramifiedZeroDescentStatement`. -/
private theorem galoisStable_zeroPoints (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G)) :
    ∀ σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F,
      ∀ x ∈ E.zeroPoints,
        rationalConjugate F (UnramifiedClosure F) G σ x ∈ E.zeroPoints :=
  fun σ _ hx => E.rationalConjugate_mem_zeroPoints F G σ hx

/-- The descent statement from `ValuationApartmentAxiomsExistenceStatement` and
`UnramifiedApartmentDescentStatement`. The two Galois-stability clauses use neither
hypothesis. -/
theorem unramifiedZeroDescent_of_geometric_inputs
    (hExists : ValuationApartmentAxiomsExistenceStatement.{u})
    (hDescent : UnramifiedApartmentDescentStatement.{u}) :
    UnramifiedZeroDescentStatement.{u} := by
  intro F _ _ _ _ G hG
  refine ⟨?_, fun E => ⟨?_, ?_⟩⟩
  · convert galoisStable_characterValuationKernel F G using 0
  · convert galoisStable_zeroPoints F G E using 0
  · intro S Z i j Z0
    exact unramifiedZeroDescentGeometricReduction
      hExists hDescent MaximalUnramified.zeroFacetNoInversions F G hG E i j Z0

/-- **KP Proposition 9.3.24 and Galois stability of `G(K)^1`, `G(K)^0`.** For a connected
reductive group over a nonarchimedean local field and its base change to the maximal
unramified extension `K`, `G(K)^1` and every zero subgroup `G(K)^0` are stable under
`Aut(K/F)`, and `G(K)^0 ∩ G(F)` is the zero subgroup `G(F)^0` of every zero datum over `F`. -/
theorem unramifiedZeroDescent : UnramifiedZeroDescentStatement.{u} :=
  unramifiedZeroDescent_of_geometric_inputs valuationApartmentAxiomsExistence
    unramifiedApartmentDescent

end Langlands.Geometry.Building
