import Langlands.Galois.Local.AbsoluteDefinitions

open ValuativeRel IsLocalRing

namespace Langlands.LocalGalois

universe u

/-- All arithmetic, reduction and topology claims for the constructed local map. -/
def LocalResidueProperties (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] : Prop :=
  (localNormedField K).toNormedField.toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace K› ∧
  letI := localNormedField K
  letI := localNormedField_ultrametric K
  letI := localNormedField_complete K
  Finite 𝓀[K] ∧
  (valuation K).HasExtension (localClosureValuation K) ∧
  (NormedField.valuation (K := K)).integer = (valuation K).integer ∧
  (∀ x : AlgebraicClosure K, IsIntegral 𝒪[K] x ↔ x ∈ closureIntegers K) ∧
  (∀ (σ : Field.absoluteGaloisGroup K) (x : AlgebraicClosure K),
    localClosureValuation K (AlgEquiv.toAlgHom σ x) = localClosureValuation K x) ∧
  (letI := standardResidueAlgebra K;
    IsAlgClosure 𝓀[K] (ResidueField (closureIntegers K))) ∧
  (∀ a : 𝒪[K], localResidueClosureEquiv K (residue _ (localIntegerMap K a)) =
    algebraMap 𝓀[K] (AlgebraicClosure 𝓀[K]) (residue 𝒪[K] a)) ∧
  (∀ (σ : Field.absoluteGaloisGroup K) (x : closureIntegers K),
    (AlgEquiv.toAlgHom (absoluteResidueHom K σ))
        (localResidueClosureEquiv K (residue _ x)) =
      localResidueClosureEquiv K (residue _ (integerAut K (AlgebraicClosure K) σ x))) ∧
  Continuous (absoluteResidueHom K) ∧
  Function.Surjective (absoluteResidueHom K) ∧
  IsOpenMap (absoluteResidueHom K) ∧
  (absoluteResidueHom K).ker = absoluteInertia K ∧
  (∀ σ : Field.absoluteGaloisGroup K, σ ∈ absoluteInertia K ↔
    ∀ x : closureIntegers K,
      residue _ (integerAut K (AlgebraicClosure K) σ x) = residue _ x) ∧
  absoluteInertia K = ((closureIntegers K).inertiaSubgroup K).comap
    (decompositionHom K (AlgebraicClosure K)) ∧
  (absoluteInertia K).Normal ∧
  IsClosed (absoluteInertia K : Set (Field.absoluteGaloisGroup K)) ∧
  CompactSpace (absoluteInertia K) ∧
  TotallyDisconnectedSpace (absoluteInertia K) ∧
  T2Space (absoluteInertia K) ∧
  (∃ e : (Field.absoluteGaloisGroup K ⧸ absoluteInertia K) ≃ₜ*
      Field.absoluteGaloisGroup 𝓀[K],
    ∀ σ : Field.absoluteGaloisGroup K, e (QuotientGroup.mk σ) = absoluteResidueHom K σ) ∧
  (∀ (E : IntermediateField K (AlgebraicClosure K)) [Normal K E]
      (σ : Field.absoluteGaloisGroup K) (y : ResidueField (extensionIntegers K E)),
    (AlgEquiv.toAlgHom (absoluteResidueHom K σ))
        (localResidueClosureEquiv K (residueInclusion K (AlgebraicClosure K) E y)) =
      localResidueClosureEquiv K (residueInclusion K (AlgebraicClosure K) E
        (residueHom K E (σ.restrictNormal E) y)))

/-- The entire local residue theorem for every supplied p-adic realization. -/
def PadicResidueExactness : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Langlands.PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
    LocalResidueProperties F.Carrier

end Langlands.LocalGalois
