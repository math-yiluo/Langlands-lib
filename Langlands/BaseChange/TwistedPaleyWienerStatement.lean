import Langlands.BaseChange.TwistedPaleyWiener

/-!
# The twisted trace Paley–Wiener theorem for `GL_n` over a cyclic extension

Rogawski (1988), Proposition 11.2, in the form of Henniart–Lemaire (2011), II.5.7, Théorème,
direction (A) ⇒ (B), with condition (i) replaced by condition (i)' of Remarque (1), for
`GL_n(E)` with `E` a cyclic extension of a nonarchimedean local field `F` of characteristic
zero. The proposition concerns a linear functional `Φ` on the distributions on `GL_n(E)`,
through its values on twisted characters. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis

/-- Twisted trace Paley–Wiener theorem for `GL_n(E)` (Rogawski 1988, Proposition 11.2;
Henniart–Lemaire 2011, II.5.7, (A) ⇒ (B), with condition (i)' of Remarque (1)). Let `F` be a
nonarchimedean local field of characteristic zero, `E` a field that is a cyclic `F`-algebra of
group `⟨σ⟩` of order `l` (with its module topology), and give `GL_n(E)` its Borel σ-algebra.
Let `μ` be a Haar measure on `GL_n(E)` and `Φ` a linear functional on the distributions on
`GL_n(E)`. If `Φ` vanishes on the twisted characters `Θ^A_π` of the irreducible admissible
representations without nonzero vectors fixed by some compact open subgroup `J`, and the
values of `Φ` on the twisted characters of the induced families `Ind(Ξ ⊗ ψ)` are regular in
the σ-invariant unramified character `ψ`, then there is `φ ∈ C^∞_c(GL_n(E))` with
`Θ^A_π(φ) = Φ(Θ^A_π)` for every irreducible admissible `π` and every `A : π ≅ π^σ`.
Regularity is required for every irreducible admissible inducing pair `(Ξ, BΞ)` on every
standard Levi. The carriers of the quantified irreducible representations `π` and `Ξ`
are complex vector spaces in the universe `z`. -/
def TwistedTracePaleyWienerStatement.{u, v, z} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure]
      (Φ : Module.Dual ℂ (Distribution (GeneralLinear n E))),
      IsCompactlyDominatedFunctional.{v, z} (entrywiseAut σ n) μ Φ →
      IsSigmaInducedRegularFunctional.{u, v, z} σ μ Φ →
      IsTwistedTraceFunctional.{v, z} (entrywiseAut σ n) μ Φ

end Langlands.BaseChange
