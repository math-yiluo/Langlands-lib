import Langlands.BaseChange.TwistedJacquet
import Langlands.Representation.Unramified.PrincipalSeries
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# The normalized σ-action on a generic unramified constituent of `GL_n(E)`

Henniart–Lemaire (2011), I.5.4, Lemma 1 and Lemma 2 with its proof, and I.5.5,
Lemma 1(3) and the proof of Lemma 2. Let `E/F` be an unramified cyclic extension of
p-adic fields with generator `σ`. A generic irreducible subquotient `π` of an unramified
normalized principal series of `GL_(r+1)(E)` has a σ-intertwiner that acts as the
identity on its actual Borel Jacquet quotient and fixes every `GL_(r+1)(O_E)`-fixed
vector. Stated as a proposition, not proved here. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open Langlands.Correspondence Langlands.Unramified

universe uF uE uV

local instance unramifiedGenericSigmaFieldTopology {p : ℕ} [Fact p.Prime]
    (E : PadicField.{uE} p) : TopologicalSpace E.Carrier :=
  E.canonicalTopologicalData.topology
local instance unramifiedGenericSigmaGeneralLinearTopology {p : ℕ} [Fact p.Prime]
    (E : PadicField.{uE} p) (n : ℕ) : TopologicalSpace (GeneralLinear n E.Carrier) :=
  E.canonicalGeneralLinearTopology n

/-- Henniart–Lemaire I.5.4, Lemma 2 and its proof, with I.5.5, Lemma 1(3). Over an
unramified cyclic extension `E/F` with generator `σ`, every generic irreducible admissible
subquotient `π` of the normalized principal series `principalSeriesOfTuple E z` of
`GL_(r+1)(E)` has a σ-intertwiner `A` whose descent `[v] ↦ [A v]` to the Borel Jacquet
quotient of `π` is the identity, and which fixes every vector of `π` fixed by the
spherical subgroup `GL_(r+1)(O_E)`. -/
def UnramifiedGenericSigmaNormalizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ),
    IsCyclicAlgebra σ l →
    E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex →
    ∀ (z : Fin (r + 1) → ℂˣ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (r + 1) E.Carrier) V)
      (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter E.Carrier),
      Whittaker.IsGeneric ψ r π →
      IsSubquotientOf (principalSeriesOfTuple E z) π →
      ∃ A : SigmaIntertwiner σ (r + 1) π,
        (∀ v : V, jacquetSigmaIntertwiner σ (borelShape r) A ((borelShape r).jacquetMk π v) =
          (borelShape r).jacquetMk π v) ∧
        ∀ v ∈ fixedVectors π (sphericalSubgroup E r), A v = v

end Langlands.BaseChange
