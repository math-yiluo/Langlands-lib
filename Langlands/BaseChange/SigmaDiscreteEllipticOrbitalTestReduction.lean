import Langlands.BaseChange.ProperInducedVanishingOrbitalStatement
import Langlands.BaseChange.SigmaDiscreteEllipticOrbitalTestStatement
import Langlands.BaseChange.SigmaDiscreteProperInducedVanishingTestStatement

/-!
# σ-elliptic orbital test functions for σ-discrete series: a reduction

For a cyclic field extension `E/F` of nonarchimedean local fields of characteristic zero, the
module proves that `SigmaDiscreteEllipticOrbitalTestStatement` follows from two statements:

* `SigmaDiscreteProperInducedVanishingTestStatement`: a σ-discrete series `τ` of `GL_{r+1}(E)`
  has a test function with nonzero twisted trace at `τ` whose twisted traces vanish on the
  irreducible representations properly induced from σ-stable representations of standard
  Levi subgroups (Henniart–Lemaire 2011, II.5.13, Remarque, and II.5.14, Proposition 2 (1));
* `ProperInducedVanishingOrbitalStatement`: such a vanishing of induced twisted traces forces
  the σ-orbital integrals to vanish off the σ-elliptic set (Henniart–Lemaire 2011, II.5.14,
  proof of Proposition 2 (2); Arthur–Clozel 1989, Chapter 1, Lemma 2.12 (ii)).

The test function of the first statement satisfies the hypothesis of the second. See the
paired Markdown.
-/

namespace Langlands.BaseChange

universe u v uW

/-- `SigmaDiscreteEllipticOrbitalTestStatement` follows from the existence of test functions
with nonzero twisted trace killing the twisted traces of irreducible properly induced
representations, and from the vanishing off the σ-elliptic set of the σ-orbital integrals of
such functions, at the same universe parameters (Henniart–Lemaire 2011, II.5.14,
Proposition 2; Arthur–Clozel 1989, Chapter 1, Lemma 2.12 (ii)). -/
def SigmaDiscreteEllipticOrbitalTestReductionStatement : Prop :=
  SigmaDiscreteProperInducedVanishingTestStatement.{u, v, uW} →
    ProperInducedVanishingOrbitalStatement.{u, v, uW} →
      SigmaDiscreteEllipticOrbitalTestStatement.{u, v, uW}

/-- Proof of `SigmaDiscreteEllipticOrbitalTestReductionStatement`: the first statement gives
a test function `φ` with `tr(τ(φ) ∘ A) ≠ 0` killing the twisted traces of irreducible
properly induced representations, and the second statement, applied to `φ`, gives the
vanishing of its σ-orbital integrals off the σ-elliptic set. -/
theorem sigmaDiscreteEllipticOrbitalTestReduction :
    SigmaDiscreteEllipticOrbitalTestReductionStatement.{u, v, uW} := by
  intro htest hgeom F _ _ _ _ _ E _ _ _ _ _ σ l r hE W _ _ τ hτ hdisc A μ _
  obtain ⟨φ, hne, hind⟩ := htest F E σ l r hE τ hτ hdisc A μ
  exact ⟨φ, hgeom F E σ l r hE μ φ hind, hne⟩

end Langlands.BaseChange
