import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationStatement

/-! # Equivalent irreducible cuspidal `L²` summands of `GL_n` have equivalent realizations

Derived from Getz–Hahn, Theorems 6.6.2, 6.6.4 and 9.7.3: the `K`-finite vectors of an
irreducible closed invariant subspace `V` of `L²_cusp([GL_n])` are cusp forms and form an
irreducible cuspidal automorphic representation, and two such subspaces are unitarily
equivalent only if these automorphic representations are equivalent. This module states the
consequence used for multiplicity one, in the Library's two models of the cuspidal spectrum:
two cuspidal operator realizations whose `L²` images are dense in isometrically equivalent
irreducible summands are equivalent. The statement contains no proof. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

local instance summandEquivalenceGeneralLinearIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance summandEquivalenceGeneralLinearSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- **Realizations of equivalent irreducible cuspidal `L²` summands are equivalent**
(derived from Getz–Hahn, Theorems 6.6.2, 6.6.4 and 9.7.3). With the data of
`GeneralLinearCuspidalMultiplicityOneStatement` in rank `r + 1` over a number field whose
adele quotient is compact, let `P` and `Q` be nonzero closed invariant subspaces of the full
almost-everywhere cuspidal subspace `S` of `L²([GL_{r+1}])`, each with no closed invariant
subspaces other than `0` and itself, and let `U : P ≃ Q` be a linear isometric equivalence
intertwining the right regular actions. Let `R` and `R'` be cuspidal operator realizations of
rank `r + 1` with linear maps `Φ` and `Φ'` from their spaces to `S` that send every vector to
the `L²` class of the function it induces on the quotient, such that the closure of the image
of `Φ` is `P` and the closure of the image of `Φ'` is `Q`. Then `R` and `R'` are equivalent
for the finite, compact and differential operators together. -/
def GeneralLinearCuspidalSummandEquivalenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant],
    let hG := GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
    let S := fullAEL2CuspidalSubmodule F _ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F _ hPD hG T i hi I e hc
    ∀ P Q : Submodule ℂ S,
      (P ≠ ⊥ ∧ IsClosed (P : Set S) ∧ (∀ a, ∀ x ∈ P, πc a x ∈ P) ∧
        ∀ P' : Submodule ℂ S, P' ≤ P → IsClosed (P' : Set S) →
          (∀ a, ∀ x ∈ P', πc a x ∈ P') → P' = ⊥ ∨ P' = P) →
      (Q ≠ ⊥ ∧ IsClosed (Q : Set S) ∧ (∀ a, ∀ x ∈ Q, πc a x ∈ Q) ∧
        ∀ Q' : Submodule ℂ S, Q' ≤ Q → IsClosed (Q' : Set S) →
          (∀ a, ∀ x ∈ Q', πc a x ∈ Q') → Q' = ⊥ ∨ Q' = Q) →
      ∀ (hPi : ∀ a, ∀ x ∈ P, πc a x ∈ P) (U : P ≃ₗᵢ[ℂ] Q),
        (∀ a (x : P), (U ⟨πc a x, hPi a x x.2⟩ : S) = πc a (U x)) →
      ∀ (R R' : Langlands.Automorphic.CuspidalOperatorRealization F r)
        (Φ : R.Space →ₗ[ℂ] S) (Φ' : R'.Space →ₗ[ℂ] S),
        (∀ f : R.Space,
          IsGeneralLinearFormClass F r T i (Φ f : Lp ℂ 2 _) (R.realization.toContinuous f)) →
        (LinearMap.range Φ).topologicalClosure = P →
        (∀ f : R'.Space,
          IsGeneralLinearFormClass F r T i (Φ' f : Lp ℂ 2 _) (R'.realization.toContinuous f)) →
        (LinearMap.range Φ').topologicalClosure = Q →
        Nonempty (R.Equivalence R')

end Langlands.Automorphic.GroupSchemeFunctions
