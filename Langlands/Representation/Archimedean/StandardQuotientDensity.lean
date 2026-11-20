import Langlands.Representation.Archimedean.GKModuleDensity
import Langlands.Representation.Archimedean.PrincipalSeriesAdmissible
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Langlands.Representation.Archimedean.RealLeviDuality
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.Representation.KFiniteDual

/-!
# Density hypotheses for irreducible archimedean standard quotients

The compact representation of a standard module has finite vectors and
continuous coefficients. Compact semisimplicity splits the quotient
projection for that action, so compact admissibility descends. The
irreducible (𝔤, K)-quotients therefore satisfy the density hypotheses.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Matrix Matrix.Norms.Operator MonoidAlgebra TensorProduct

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

section Compact

variable {K V : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ K V) (R : Submodule ℂ V) (hR : ∀ k, R ≤ R.comap (ρ k))

/-- The projection to the quotient by a compact-stable subspace, as a compact intertwiner. -/
def compactQuotientProjection : ρ.IntertwiningMap (ρ.quotient R hR) where
  toLinearMap := R.mkQ
  isIntertwining' _ := LinearMap.ext fun _ => rfl

variable [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

/-- Compact finite admissible representations with continuous coefficients have
admissible quotients by stable subspaces. -/
theorem isAdmissibleGKModule_compactQuotient
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (hadm : IsAdmissibleGKModule ρ) :
    IsAdmissibleGKModule (ρ.quotient R hR) := by
  let ρq := ρ.quotient R hR
  have := KFiniteDual.isSemisimpleModule hfin hcont
  let p := Representation.IntertwiningMap.equivLinearMapAsModule ρ ρq
    (compactQuotientProjection ρ R hR)
  have hp : Function.Surjective p := R.mkQ_surjective
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property p hp
    (LinearMap.id : ρq.asModule →ₗ[ℂ[K]] ρq.asModule)
  let S := (Representation.IntertwiningMap.equivLinearMapAsModule ρq ρ).symm s
  have hS : Function.Injective S.toLinearMap := by
    intro x y hxy
    have hpx : p (s x) = x := LinearMap.congr_fun hs x
    have hpy : p (s y) = y := LinearMap.congr_fun hs y
    exact hpx.symm.trans ((congrArg p hxy).trans hpy)
  intro d τ hτ
  have := hadm d τ hτ
  let lift : gkIntertwiners ρq d τ →ₗ[ℂ] gkIntertwiners ρ d τ :=
    { toFun := fun A => ⟨S.toLinearMap ∘ₗ A.val, fun k x => by
        change S (A.val (τ k *ᵥ x)) = ρ k (S (A.val x))
        rw [A.2 k x, S.isIntertwining]⟩
      map_add' := fun A B => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c A => Subtype.ext (LinearMap.comp_smul _ _ _) }
  apply Module.Finite.of_injective lift
  intro A B hAB
  exact Subtype.ext (LinearMap.ext fun x => hS <|
    congrArg (fun U : gkIntertwiners ρ d τ => U.val x) hAB)

end Compact

section Standard

variable {K L V : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [LieRing L] [LieAlgebra ℂ L] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ K V} {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    {R : Submodule ℂ V} (hR : IsGKSubmodule ρ π R)

/-- The irreducible quotient of an admissible compact-finite module with continuous
compact coefficients satisfies the Jacobson density hypotheses. -/
theorem gkModuleDensityHyp_quotient
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (hadm : IsAdmissibleGKModule ρ)
    (hirr : IsIrreducibleGKModule (ρ.quotient R hR.1) (RealLeviDuality.quotLie π R hR.2)) :
    GKModuleDensity.Hyp (ρ.quotient R hR.1) (RealLeviDuality.quotLie π R hR.2) :=
  ⟨hirr, isAdmissibleGKModule_compactQuotient ρ R hR.1 hfin hcont hadm,
    RealLeviDuality.quotient_finite ρ R hR.1 hfin,
    RealLeviDuality.quotient_continuous ρ R hR.1 hcont⟩

end Standard

open Langlands.LocalFactor.Archimedean (RealBlock ComplexCharacterData)

/-- An irreducible quotient of a real standard module meets the density hypotheses. -/
theorem realStandardQuotient_density (n : ℕ) (ds : List RealBlock)
    {R : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))}
    (hR : IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) R)
    (hirr : IsIrreducibleGKModule ((realStandardRep n ds).quotient R hR.1)
      (RealLeviDuality.quotLie (realStandardLie n ds) R hR.2)) :
    GKModuleDensity.Hyp ((realStandardRep n ds).quotient R hR.1)
      (RealLeviDuality.quotLie (realStandardLie n ds) R hR.2) := by
  have hgk := isRealGKModule_realStandardModule n ds
  exact gkModuleDensityHyp_quotient hR hgk.1 hgk.2.1 (realStandardAdmissible n ds) hirr

/-- An irreducible quotient of a complex standard module meets the density hypotheses. -/
theorem complexStandardQuotient_density (n : ℕ) (ds : List ComplexCharacterData)
    {R : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))}
    (hR : IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) R)
    (hirr : IsIrreducibleGKModule ((complexStandardRep n ds).quotient R hR.1)
      (RealLeviDuality.quotLie (complexStandardLie n ds) R hR.2)) :
    GKModuleDensity.Hyp ((complexStandardRep n ds).quotient R hR.1)
      (RealLeviDuality.quotLie (complexStandardLie n ds) R hR.2) := by
  have hgk := isComplexGKModule_complexStandardModule n ds
  exact gkModuleDensityHyp_quotient hR hgk.1 hgk.2.1
    (PrincipalSeries.isAdmissibleGKModule_principalSeriesRep ℂ n (complexPositionCharacter ds)) hirr

end Langlands.Archimedean
