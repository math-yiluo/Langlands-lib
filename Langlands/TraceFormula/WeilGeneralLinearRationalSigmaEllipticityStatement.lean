import Langlands.TraceFormula.GeneralLinearBaseChangeLocal
import Langlands.TraceFormula.GeneralLinearWeilAdelicTwistStatement

/-!
# Rational σ-ellipticity from σ_v-ellipticity at a finite place of the base

Let `L/K` be a cyclic extension of number fields of degree `l` with generator `σ`, and
`W = Res_{L/K} GL_n`. If the component at a finite place `v` of `K` of a rational point
of `W` is σ_v-elliptic in `GL_n(K_v ⊗_K L)`, then the matrix of `GL_n(L)` corresponding
to the point under the identification `Φ` of `GeneralLinearWeilAdelicTwistStatement` is
σ-elliptic over `K`. Both ellipticity conditions are `IsSigmaElliptic`, over the base
fields `K_v` and `K`.

This module states the proposition and does not prove it. It is derived from the norm
lemma and the ellipticity conventions of Henniart–Lemaire (2011), I.2.2–I.2.3, and the
base-field indexing of the twisted geometric side in II.6.4. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Langlands.TraceFormula.PlaceCompletion
open Langlands.Global Langlands.GroupScheme Langlands.BaseChange
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

local instance weilGeneralLinearRationalSigmaEllipticityIsAffine (K : Type u) [Field K]
    (n : ℕ) : IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance weilGeneralLinearRationalSigmaEllipticitySmooth (K : Type u) [Field K]
    (n : ℕ) : Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The `GL_n` group scheme over `K`, for the bound variables `K` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The Weil restriction `Res_{L/K} GL_n`, for the bound variables `K`, `L` and `n`. -/
local notation "Wₙ" => weilGroup K L GLₙ

/-- Let `L/K` be a finite extension of number fields with `IsCyclicAlgebra σ l`, let
`W = Res_{L/K} GL_n`, and let `Φ : W(𝔸_K) → GL_n(𝔸_L)` be the composite of
`GeneralLinearWeilAdelicTwistStatement`. For a finite place `v` of `K` and a point `r` of
the rational subgroup of `W(𝔸_K)`: if the component of `r` at `v`, as a matrix in
`GL_n(K_v ⊗_K L)` via `localPointsEquiv`, is σ_v-elliptic for
`σ_v = localGalois K L σ (.inr v)`, then there is `δ ∈ GL_n(L)` with `Φ r = AdelicGL.rational L n δ` that is σ-elliptic over
`K`. -/
def WeilGeneralLinearRationalSigmaEllipticityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ n : ℕ,
    let Φ : AdelicGroupPoints K Wₙ → AdelicGL L n := fun g =>
      GeneralLinearGroupPoints.adelicHomeomorph L n
        (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L GLₙ)
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L))
          (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom
          (AdelicGaloisUnit.weilAdelicEquiv K L GLₙ g))
    ∀ (v : Langlands.Global.FinitePlace K) (r : AdelicGroupPoints K Wₙ),
      r ∈ AdelicGroupPoints.rationalSubgroup K Wₙ →
      IsSigmaElliptic (localGalois K L σ (.inr v)) l
        (localPointsEquiv K L n (.inr v) (AdelicGroupPoints.atPlace K Wₙ (.inr v) r)) →
      ∃ δ : RationalGL L n, Φ r = AdelicGL.rational L n δ ∧ IsSigmaElliptic σ l δ

end Langlands.TraceFormula
