import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # Multiplicity one for the cuspidal spectrum of `GL_n`

Getz–Hahn, Theorem 11.4.3 (Shalika 1974, Theorem 5.5): an irreducible representation of
`GL_n(𝔸)` occurs with multiplicity at most one in `L²_cusp([GL_n])`. The space is the
Library's full almost-everywhere cuspidal subspace of `L²` of the actual positive-central
rational quotient `[GL_n]`, with its right regular representation. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

local instance multiplicityOneGeneralLinearIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance multiplicityOneGeneralLinearSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- Multiplicity one for the cuspidal spectrum of `GL_n` (Getz–Hahn, Theorem 11.4.3; Shalika
1974, Theorem 5.5). Let `T → GL_n` be a central split torus whose character restriction is
injective with finite-index image (for example the centre `G_m`), so that the positive-central
rational quotient is `[GL_n] = A_{GL_n} GL_n(F) \ GL_n(𝔸)`, and let `S` be the full
almost-everywhere cuspidal subspace of `L²([GL_n])` with its right regular representation.
If `P` and `Q` are nonzero closed invariant subspaces of `S`, each with no closed invariant
subspaces other than `0` and itself, and there is a linear isometric equivalence `P ≃ Q`
intertwining the actions of `GL_n(𝔸)`, then `P = Q`. -/
def GeneralLinearCuspidalMultiplicityOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))).IsMulRightInvariant],
    let hG := GroupScheme.isConnectedReductive_generalLinear F (Fin n)
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
        P = Q

end Langlands.Automorphic.GroupSchemeFunctions
