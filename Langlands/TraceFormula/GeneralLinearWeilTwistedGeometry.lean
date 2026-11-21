import Langlands.TraceFormula.CyclicAdelicTests
import Langlands.TraceFormula.GeneralLinearWeilAdelicTwistStatement
import Langlands.TraceFormula.TwistedOrbital
import Langlands.Global.AdelicGroupRationalTopology
import Langlands.BaseChange.Norm

/-! # Geometry of rational sigma-elliptic twisted classes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.TraceFormula.AdelicGroupAutomorphism Langlands.BaseChange

namespace Langlands.TraceFormula

local instance twistedEllipticGLAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance twistedEllipticGLSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option hygiene false in
local notation "Θₙ" => normOneAut K (unitGaloisAut K L GLₙ σ)

section WeilCoordinates

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] (n : ℕ)

end WeilCoordinates

/-- Compactness of the rational left quotient of the twisted centralizer. -/
def IsCompactTwistedCentralizerQuotient {G : Type*} [Group G] [TopologicalSpace G]
    (Γ : Subgroup G) (θ : G ≃ₜ* G) (r : G) : Prop :=
  CompactSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ r)))

/-- The rational left quotient of the norm-one twisted centralizer is compact
for a rational sigma-elliptic matrix. The coordinate comparison is the same
one used in the twisted elliptic centralizer statement. -/
def GeneralLinearWeilTwistedCompactQuotientStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (n : ℕ) (r : rationalNormOneSubgroup K Wₙ) (δ : GeneralLinear n L),
      cyclicWeilAdelicMap K L n r.val.val = AdelicGL.rational L n δ →
      IsSigmaElliptic σ l δ →
      IsCompactTwistedCentralizerQuotient (rationalNormOneSubgroup K Wₙ) Θₙ r.val

/-- The norm-one twisted orbit of a rational sigma-elliptic matrix is closed. -/
def GeneralLinearWeilTwistedClosedOrbitStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (n : ℕ) (r : rationalNormOneSubgroup K Wₙ) (δ : GeneralLinear n L),
      cyclicWeilAdelicMap K L n r.val.val = AdelicGL.rational L n δ →
      IsSigmaElliptic σ l δ →
      IsClosed (Set.range fun x : normOneSubgroup K Wₙ => twistedConj Θₙ x r.val)

end Langlands.TraceFormula
