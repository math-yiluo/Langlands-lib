import Langlands.Representation.Families.CompactCompressionSpecialization
import Langlands.Representation.Families.LocalizedMatrixPrincipalOpen

/-! # Principal irreducibility neighborhoods from actual compact compression -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen

open Plancherel CompactCompressionMatrices LocalizedMatrixPrincipalOpen
  MatrixGenerationWitness UnramifiedPolynomialWitness

universe uB uS uG uV uW uX un u

section Specialization

variable (S : Type uS) [CommRing S] [Algebra ℂ S]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : SmoothRep.{0, uG, uV} ℂ G)
variable [Module S A] [SMulCommClass ℂ S A]

/-- A full actual fiber is obtained by scalar extension of an evaluation
intertwiner. The coefficient evaluation is part of this predicate. -/
def IsFullSpecialization (χ : S →ₐ[ℂ] ℂ) (D : SmoothRep.{0, uG, uW} ℂ G) : Prop :=
  letI : Algebra S ℂ := χ.toRingHom.toAlgebra
  ∃ (f : A.representation.IntertwiningMap D.representation)
    (hf : ∀ (s : S) (v : A), f (s • v) = algebraMap S ℂ s • f v),
    Function.Bijective
      (Compact.CoefficientSpecialization.scalarExtension S A.representation D.representation f hf)

variable [HasCompatibleCoefficients S A.representation]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable {n : Type un} [Fintype n] [DecidableEq n]
variable (b : Module.Basis n S (fixedVectors A.representation K.toSubgroup))

/-- Every actual full fiber has the evaluated coefficient matrices in a
transported basis of its compact fixed vectors. -/
theorem exists_fixedBasis (χ : S →ₐ[ℂ] ℂ) (D : SmoothRep.{0, uG, uW} ℂ G)
    (hD : IsFullSpecialization S A χ D) :
    ∃ e : Module.Basis n ℂ (fixedVectors D.representation K.toSubgroup),
      fixedMatrix D K hK e = specialize (coefficientMatrix S A K hK b) χ := by
  let _ : Algebra S ℂ := χ.toRingHom.toAlgebra
  obtain ⟨f, hf, hbij⟩ := hD
  refine ⟨specializedBasis S A K hK b D f hf hbij, ?_⟩
  funext g
  exact fixedMatrix_specializedBasis S A K hK b D f hf hbij g

end Specialization

section PrincipalOpen

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
variable {S : Type uS} [CommRing S] [Algebra B S] [Algebra ℂ S]
variable [IsScalarTower ℂ B S] (g : B) [IsLocalization.Away g S]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : SmoothRep.{0, uG, uV} ℂ G)
variable [Module S A] [SMulCommClass ℂ S A]
variable [HasCompatibleCoefficients S A.representation]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable {n : Type un} [Fintype n] [DecidableEq n]
variable (b : Module.Basis n S (fixedVectors A.representation K.toSubgroup))

include hK b in
/-- A coefficient basis, actual full specialization, and uniform detection
give a principal regular irreducibility neighborhood of an irreducible fiber. -/
theorem exists_regular_principal_neighborhood
    {X : Type uX} (χ : X → B →ₐ[ℂ] ℂ)
    (D : X → SmoothRep.{0, uG, uW} ℂ G)
    (hsp : ∀ x (hx : χ x g ≠ 0),
      IsFullSpecialization S A (awayEvaluation g (χ x) hx) (D x))
    (hdet : ∀ x (E : SmoothRep.{0, uG, uW} ℂ G),
      E.IsIrreducible → SmoothRep.IsSubquotient E (D x) →
        ∃ v : E, v ∈ fixedVectors E.representation K.toSubgroup ∧ v ≠ 0)
    (x₀ : X) (hg₀ : χ x₀ g ≠ 0) (hirr₀ : (D x₀).IsIrreducible) :
    ∃ f : B, χ x₀ f ≠ 0 ∧ ∀ x, χ x f ≠ 0 → (D x).IsIrreducible := by
  obtain ⟨e₀, he₀⟩ := exists_fixedBasis S A K hK b
    (awayEvaluation g (χ x₀) hg₀) (D x₀) (hsp x₀ hg₀)
  have hself : SmoothRep.IsSubquotient (D x₀) (D x₀) :=
    SmoothRep.IsQuotient.isSubquotient ⟨𝟙 (D x₀), fun v => ⟨v, rfl⟩⟩
  obtain ⟨v₀, hv₀, hv₀ne⟩ := hdet x₀ (D x₀) hirr₀ hself
  have : Nontrivial (fixedVectors (D x₀).representation K.toSubgroup) :=
    ⟨⟨⟨v₀, hv₀⟩, 0, fun he => hv₀ne (congrArg Subtype.val he)⟩⟩
  have : Nonempty n := e₀.index_nonempty
  have hm₀ : UnitarizabilityContinuation.IsIrreducibleFamily
      (specialize (coefficientMatrix S A K hK b) (awayEvaluation g (χ x₀) hg₀)) := by
    rw [← he₀]
    exact fixedMatrix_isIrreducible (D x₀) K hK e₀ hirr₀
  obtain ⟨f, hf₀, hf⟩ :=
    LocalizedMatrixPrincipalOpen.exists_regular_principal_neighborhood g
      (coefficientMatrix S A K hK b) (χ x₀) hg₀ hm₀
  refine ⟨f, hf₀, ?_⟩
  intro x hx
  obtain ⟨hg, hm⟩ := hf (χ x) hx
  obtain ⟨e, he⟩ := exists_fixedBasis S A K hK b
    (awayEvaluation g (χ x) hg) (D x) (hsp x hg)
  have : Nontrivial (D x) := by
    let j : n := Classical.choice inferInstance
    exact ⟨⟨(e j : D x), 0, fun hz => e.ne_zero j (Subtype.ext hz)⟩⟩
  apply isIrreducible_of_fixedMatrix (D x) K hK e (hdet x)
  rwa [he]

section ActualCharacters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (M : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (hM : GroupScheme.IsConnectedReductive M)

local instance actualTopology : TopologicalSpace (GroupScheme.rationalPoints M) :=
  rationalPointTopology F M.X

include hK b in
/-- In the canonical coordinates of the actual unramified characters, a
coefficient basis, full specialization and uniform detection give a
polynomial principal irreducibility neighborhood. -/
theorem exists_polynomial_principal_neighborhood
    (e : B ≃ₐ[ℂ]
      unramifiedRegularFunctions (fun ψ => (rationalNormCharacters M ψ).toMul))
    (D : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul) →
      SmoothRep.{0, uG, uW} ℂ G)
    (hsp : ∀ χ (hχ : coefficientCharacter M e χ g ≠ 0),
      IsFullSpecialization S A (awayEvaluation g (coefficientCharacter M e χ) hχ) (D χ))
    (hdet : ∀ χ (E : SmoothRep.{0, uG, uW} ℂ G),
      E.IsIrreducible → SmoothRep.IsSubquotient E (D χ) →
        ∃ v : E, v ∈ fixedVectors E.representation K.toSubgroup ∧ v ≠ 0)
    (χ₀ : unramifiedCharacters (fun ψ => (rationalNormCharacters M ψ).toMul))
    (hg₀ : coefficientCharacter M e χ₀ g ≠ 0) (hirr₀ : (D χ₀).IsIrreducible) :
    ∃ p : MvPolynomial (Fin (rationalImageRank M)) ℂ,
      χ₀ ∈ rationalUnramifiedPrincipalOpen M hM p ∧
      ∀ χ ∈ rationalUnramifiedPrincipalOpen M hM p, (D χ).IsIrreducible := by
  obtain ⟨f, hf₀, hf⟩ := exists_regular_principal_neighborhood g A K hK b
    (coefficientCharacter M e) D hsp hdet χ₀ hg₀ hirr₀
  refine ⟨rationalRegularPolynomial M hM (e f), ?_, ?_⟩
  · rw [principalOpen_rationalRegularPolynomial]
    exact hf₀
  · intro χ hχ
    rw [principalOpen_rationalRegularPolynomial] at hχ
    exact hf χ hχ

end ActualCharacters

end PrincipalOpen

end Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen
