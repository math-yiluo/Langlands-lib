import Langlands.Galois.Local.AbsoluteDefinitions

/-!
# The residue projection of a separable closure: statements

Proposition definitions for the integers, residue projection and inertia of a
separable closure `Ω` of a nonarchimedean local field `K` of either characteristic,
as published in `Galois.Local.AbsoluteDefinitions` (namespace
`Langlands.LocalGalois.SepClosed`). These are targets for later proofs, not
assumptions.
-/

open ValuativeRel IsLocalRing

namespace Langlands.LocalGalois

universe uK uΩ

/-- All arithmetic, reduction and topology claims for the residue projection of a
separable closure `Ω` of `K`, in either characteristic. -/
def ResidueProjectionProperties (K : Type uK) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] : Prop :=
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  (localNormedField K).toNormedField.toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace K› ∧
  letI := localNormedField K
  letI := localNormedField_ultrametric K
  letI := localNormedField_complete K
  Finite 𝓀[K] ∧
  (valuation K).HasExtension (SepClosed.closureValuation K Ω) ∧
  (NormedField.valuation (K := K)).integer = (valuation K).integer ∧
  (∀ x : Ω, IsIntegral 𝒪[K] x ↔ x ∈ SepClosed.closureIntegers K Ω) ∧
  (∀ (σ : Ω ≃ₐ[K] Ω) (x : Ω),
    SepClosed.closureValuation K Ω (AlgEquiv.toAlgHom σ x) =
      SepClosed.closureValuation K Ω x) ∧
  (letI := SepClosed.residueAlgebra K Ω;
    IsAlgClosure 𝓀[K] (ResidueField (SepClosed.closureIntegers K Ω))) ∧
  (∀ a : 𝒪[K],
    SepClosed.residueClosureEquiv K Ω (residue _ (SepClosed.integerMap K Ω a)) =
      algebraMap 𝓀[K] (AlgebraicClosure 𝓀[K]) (residue 𝒪[K] a)) ∧
  (∀ (σ : Ω ≃ₐ[K] Ω) (x : SepClosed.closureIntegers K Ω),
    (AlgEquiv.toAlgHom (SepClosed.absoluteResidueHom K Ω σ))
        (SepClosed.residueClosureEquiv K Ω (residue _ x)) =
      SepClosed.residueClosureEquiv K Ω (residue _ (integerAut K Ω σ x))) ∧
  Continuous (SepClosed.absoluteResidueHom K Ω) ∧
  Function.Surjective (SepClosed.absoluteResidueHom K Ω) ∧
  IsOpenMap (SepClosed.absoluteResidueHom K Ω) ∧
  (SepClosed.absoluteResidueHom K Ω).ker = SepClosed.absoluteInertia K Ω ∧
  (∀ σ : Ω ≃ₐ[K] Ω, σ ∈ SepClosed.absoluteInertia K Ω ↔
    ∀ x : SepClosed.closureIntegers K Ω,
      residue _ (integerAut K Ω σ x) = residue _ x) ∧
  SepClosed.absoluteInertia K Ω =
    ((SepClosed.closureIntegers K Ω).inertiaSubgroup K).comap (decompositionHom K Ω) ∧
  (SepClosed.absoluteInertia K Ω).Normal ∧
  IsClosed (SepClosed.absoluteInertia K Ω : Set (Ω ≃ₐ[K] Ω)) ∧
  CompactSpace (SepClosed.absoluteInertia K Ω) ∧
  TotallyDisconnectedSpace (SepClosed.absoluteInertia K Ω) ∧
  T2Space (SepClosed.absoluteInertia K Ω) ∧
  (∃ e : ((Ω ≃ₐ[K] Ω) ⧸ SepClosed.absoluteInertia K Ω) ≃ₜ*
      Field.absoluteGaloisGroup 𝓀[K],
    ∀ σ : Ω ≃ₐ[K] Ω,
      e (QuotientGroup.mk σ) = SepClosed.absoluteResidueHom K Ω σ) ∧
  (∀ (E : IntermediateField K Ω) [Normal K E]
      (σ : Ω ≃ₐ[K] Ω) (y : ResidueField (extensionIntegers K E)),
    (AlgEquiv.toAlgHom (SepClosed.absoluteResidueHom K Ω σ))
        (SepClosed.residueClosureEquiv K Ω (residueInclusion K Ω E y)) =
      SepClosed.residueClosureEquiv K Ω (residueInclusion K Ω E
        (residueHom K E (σ.restrictNormal E) y)))

/-- The residue projection properties for every nonarchimedean local field `K` and
every separable closure `Ω` of `K`, in independent universes. -/
def ResidueProjectionExactness : Prop :=
  ∀ (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω],
    ResidueProjectionProperties K Ω

end Langlands.LocalGalois
