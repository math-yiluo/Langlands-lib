import Langlands.Representation.Families.CompactCompressionPrincipalOpen

/-! # Principal irreducibility neighborhoods from a global coefficient basis -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen

open Plancherel CompactCompressionMatrices LocalizedMatrixPrincipalOpen
  UnramifiedPolynomialWitness

universe uB uG uV uW un u

variable {B : Type uB} [CommRing B] [Algebra ℂ B]

omit [Algebra ℂ B] in
/-- A coefficient algebra is its own localization away from `1`. -/
theorem isLocalization_away_one : IsLocalization.Away (1 : B) B :=
  IsLocalization.away_of_isUnit_of_bijective _ isUnit_one (Equiv.refl B).bijective

/-- Evaluation of the trivial localization is the original evaluation. -/
theorem awayEvaluation_one (χ : B →ₐ[ℂ] ℂ) (hχ : χ 1 ≠ 0) :
    letI := isLocalization_away_one (B := B)
    awayEvaluation (S := B) (1 : B) χ hχ = χ := by
  let := isLocalization_away_one (B := B)
  ext b
  exact awayEvaluation_algebraMap (S := B) (1 : B) χ hχ b

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : SmoothRep.{0, uG, uV} ℂ G)
variable [Module B A] [SMulCommClass ℂ B A]
variable [HasCompatibleCoefficients B A.representation]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable {n : Type un} [Fintype n] [DecidableEq n]
variable (b : Module.Basis n B (fixedVectors A.representation K.toSubgroup))

section ActualCharacters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (M : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (hM : GroupScheme.IsConnectedReductive M)

local instance globalActualTopology : TopologicalSpace (GroupScheme.rationalPoints M) :=
  rationalPointTopology F M.X

include hK b in
/-- A global finite coefficient basis of compact fixed vectors, full actual
specialization at every unramified character and uniform detection give a
polynomial principal irreducibility neighborhood of an irreducible fiber. -/
theorem exists_polynomial_principal_neighborhood_of_global
    (e : B ≃ₐ[ℂ]
      unramifiedRegularFunctions (fun ψ => (rationalNormCharacters M ψ).toMul))
    (D : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul) →
      SmoothRep.{0, uG, uW} ℂ G)
    (hsp : ∀ χ, IsFullSpecialization B A (coefficientCharacter M e χ) (D χ))
    (hdet : ∀ χ (E : SmoothRep.{0, uG, uW} ℂ G),
      E.IsIrreducible → SmoothRep.IsSubquotient E (D χ) →
        ∃ v : E, v ∈ fixedVectors E.representation K.toSubgroup ∧ v ≠ 0)
    (χ₀ : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul))
    (hirr₀ : (D χ₀).IsIrreducible) :
    ∃ p : MvPolynomial (Fin (rationalImageRank M)) ℂ,
      χ₀ ∈ rationalUnramifiedPrincipalOpen M hM p ∧
      ∀ χ ∈ rationalUnramifiedPrincipalOpen M hM p, (D χ).IsIrreducible := by
  let := isLocalization_away_one (B := B)
  refine exists_polynomial_principal_neighborhood (S := B) (1 : B) A K hK b M hM e D
    ?_ hdet χ₀ (by simp) hirr₀
  intro χ hχ
  rw [awayEvaluation_one]
  exact hsp χ

/-- `A` is a global coefficient family for the fibers `D` over the actual
unramified characters of `M`: the fixed vectors of every compact open subgroup
form a finite free `B`-module, and `A` specializes fully to `D χ` at the
character `coefficientCharacter M e χ` of `B`, for every `χ`. -/
def IsGlobalCoefficientFamily
    (e : B ≃ₐ[ℂ]
      unramifiedRegularFunctions (fun ψ => (rationalNormCharacters M ψ).toMul))
    (D : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul) →
      SmoothRep.{0, uG, uW} ℂ G) : Prop :=
  (∀ K : OpenSubgroup G, IsCompact (K : Set G) →
    Module.Free B (fixedVectors A.representation K.toSubgroup) ∧
      Module.Finite B (fixedVectors A.representation K.toSubgroup)) ∧
    ∀ χ, IsFullSpecialization B A (coefficientCharacter M e χ) (D χ)

include hK in
/-- A global coefficient family and uniform detection by one compact open
subgroup give a polynomial principal irreducibility neighborhood of an
irreducible fiber. -/
theorem exists_polynomial_principal_neighborhood_of_family
    (e : B ≃ₐ[ℂ]
      unramifiedRegularFunctions (fun ψ => (rationalNormCharacters M ψ).toMul))
    (D : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul) →
      SmoothRep.{0, uG, uW} ℂ G)
    (hA : IsGlobalCoefficientFamily A M e D)
    (hdet : ∀ χ (E : SmoothRep.{0, uG, uW} ℂ G),
      E.IsIrreducible → SmoothRep.IsSubquotient E (D χ) →
        ∃ v : E, v ∈ fixedVectors E.representation K.toSubgroup ∧ v ≠ 0)
    (χ₀ : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul))
    (hirr₀ : (D χ₀).IsIrreducible) :
    ∃ p : MvPolynomial (Fin (rationalImageRank M)) ℂ,
      χ₀ ∈ rationalUnramifiedPrincipalOpen M hM p ∧
      ∀ χ ∈ rationalUnramifiedPrincipalOpen M hM p, (D χ).IsIrreducible := by
  obtain ⟨_, _⟩ := hA.1 K hK
  exact exists_polynomial_principal_neighborhood_of_global A K hK
    (Module.Free.chooseBasis B (fixedVectors A.representation K.toSubgroup))
    M hM e D hA.2 hdet χ₀ hirr₀

end ActualCharacters

end Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen
