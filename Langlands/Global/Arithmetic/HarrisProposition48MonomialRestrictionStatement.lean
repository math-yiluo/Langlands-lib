import Langlands.Galois.AlgebraicHeckeMonomialStatement
import Langlands.Galois.ClosureRestriction
import Langlands.Global.Arithmetic.HarrisProposition48InductionData
import Langlands.Weil.Representation.DirectSum

/-! # Restriction of the actual monomial family in Harris's Proposition 4.8 -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.GaloisRepresentation Langlands.Unramified
open Langlands.Global.AdelicFunctoriality

namespace Proposition48Problem

/-- One actual automorphism representative for each of the step's double cosets. -/
def IsMackeyEnumeration (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
    {k : ℕ} (a : Fin k → Q.L ≃ₐ[Q.E] Q.L) : Prop :=
  Function.Bijective (fun i =>
    DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup (a i))

end Proposition48Problem

/-- The parent monomial collection restricted to the step field is, at every
coefficient place, the actual direct sum of the induced collections of the
Mackey characters with the same algebraic norm normalization. -/
def Proposition48MonomialMackeyRestrictionStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    IsNormalClosure Q.E Q.E' Q.L →
    ∀ (k : ℕ) (a : Fin k → Q.L ≃ₐ[Q.E] Q.L), Q.IsMackeyEnumeration D a →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →+* ℂ) (b : ℕ)
      (ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter Q.E' L lam)
      (φ : ∀ i (lam : FinitePlace L), LambdaAdicCharacter (Q.mackeyField D (a i)) L lam)
      (R : Collection.{0, 0, uV} Q.E L ∅) (T : Fin k → Collection.{0, 0, uV} D L ∅),
      (∀ lam, IsLambdaAdicRealization ι lam (algebraicNormTwist b Q.ξ) (ψ lam)) →
      (∀ i lam, IsLambdaAdicRealization ι lam
        (algebraicNormTwist b (Q.mackeyCharacter D (a i))) (φ i lam)) →
      (∀ lam, IsInducedFromLambdaAdicCharacter (algebraMap Q.E Q.E') lam.val
        (ψ lam.val) (R lam)) →
      (∀ i lam, IsInducedFromLambdaAdicCharacter
        (IntermediateField.inclusion (show D ≤ Q.mackeyField D (a i) from le_sup_left)).toRingHom
        lam.val (φ i lam.val) (T i lam)) →
      ∀ lam, Nonempty (FiniteRepresentation.Equiv (pullback (algebraMap Q.E D) (R lam)).val
        (FiniteRepresentation.directSum (fun i => (T i lam).val)))

/-- Weak associations of actual summands give a weak association of an
intertwining-equivalent actual direct sum with the product spectrum. -/
def FiniteDirectSumWeakAssociationStatement : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (ι : L →+* ℂ)
    (k : ℕ) (n : Fin k → ℕ) (T : Fin k → Collection.{0, 0, uV} K L ∅)
    (R : Collection.{0, 0, uV} K L ∅)
    (s : ∀ i, SpectralSystem (FinitePlace K) (n i)),
    (∀ i, IsWeaklyAssociatedToSpectrum ι ∅ (T i) (s i)) →
    (∀ lam, Nonempty (FiniteRepresentation.Equiv (R lam).val
      (FiniteRepresentation.directSum (fun i => (T i lam).val)))) →
    IsWeaklyAssociatedToSpectrum ι ∅ R (SpectralSystem.finiteSum s)

/-- A spectrum associated with the restriction of an actual collection from
below a finite Galois extension has unchanged Euler polynomials under
arithmetic permutation of the good finite places. -/
def GaloisRestrictionEulerInvarianceStatement : Prop :=
  ∀ (K D L : Type) [Field K] [NumberField K] [Field D] [NumberField D]
    [Algebra K D] [IsGalois K D] [Field L] [NumberField L] (ι : L →+* ℂ)
    (R : Collection.{0, 0, uV} K L ∅) (n : ℕ)
    (s : SpectralSystem (FinitePlace D) n),
    IsWeaklyAssociatedToSpectrum ι ∅ (fun lam => pullback (algebraMap K D) (R lam)) s →
    ∀ σ : D ≃ₐ[K] D, ∀ᶠ v in Filter.cofinite,
      ∀ (hv : v ∉ s.exceptional)
        (hσv : finitePlaceEquiv σ.toRingEquiv v ∉ s.exceptional),
        s.eulerPolynomial v hv = s.eulerPolynomial (finitePlaceEquiv σ.toRingEquiv v) hσv

end Langlands.Global.Harris
