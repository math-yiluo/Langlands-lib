import Langlands.Galois.Harris1999Theorem59Statement

/-!
# General-coefficient comparison at a split supercuspidal place

A derived pairwise consequence of Harris (1999), Theorem 5.9(ii), with the
normalization fixed by a common pure weight. The statement compares genuine
local smooth classes with restrictions of genuine lambda-adic families. It
requires arbitrary regular algebraic type, rather than trivial coefficients.
-/

noncomputable section

universe uK uL uV uW

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Automorphic
open NumberField (IsTotallyComplex IsCMField)

/-- Equal supercuspidal smooth classes at the same split place give isomorphic
local restrictions of pure weakly associated lambda-adic families of the same
rank and weight. This derived forward comparison is used contrapositively to
distinguish local smooth classes. -/
def HarrisSupercuspidalLocalComparisonStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [IsCMField K]
    [CompactSpace (AdeleQuotient K)] (K₀ : IntermediateField ℚ K),
    Module.finrank ℚ K₀ = 2 → IsTotallyComplex K₀ →
    ∀ (r : ℕ), 1 ≤ r →
    ∀ (S T : CuspidalOperatorRealization K r)
      (P : CuspidalSpectralPresentation.{uK, uW} S)
      (Q : CuspidalSpectralPresentation.{uK, uW} T) (v : FinitePlace K),
      S.isoClass.IsRegularAlgebraic → T.isoClass.IsRegularAlgebraic →
      S.isoClass.IsConjugateSelfDual → T.isoClass.IsConjugateSelfDual →
      Harris.conjPlace K v ≠ v →
      (P.localComponent v).IsSupercuspidal → (Q.localComponent v).IsSupercuspidal →
      ∀ (L : Type uL) [Field L] [NumberField L] (ι : L →+* ℂ)
        (R U : Collection.{uK, uL, uV} K L ∅) (m : ℤ),
        IsPureCompatible ∅ R m → IsPureCompatible ∅ U m →
        HasRank ∅ R (r + 1) → HasRank ∅ U (r + 1) →
        CuspidalOperatorRealization.IsoClass.IsWeaklyAssociated.{uK, uL, uV, uW}
          S.isoClass ι ∅ R →
        CuspidalOperatorRealization.IsoClass.IsWeaklyAssociated.{uK, uL, uV, uW}
          T.isoClass ι ∅ U →
        ∀ lam : FinitePlace L,
          residueCharacteristic v ≠ residueCharacteristic lam →
          (P.localComponent v).isoClass = (Q.localComponent v).isoClass →
          Nonempty (FiniteRepresentation.Equiv
            (atFinitePlace v (R ⟨lam, by simp⟩)).val
            (atFinitePlace v (U ⟨lam, by simp⟩)).val)

end Langlands.GaloisRepresentation
