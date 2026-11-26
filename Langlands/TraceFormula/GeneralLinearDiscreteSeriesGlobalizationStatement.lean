import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Global.CompletionPadic
import Langlands.JacquetLanglands.EssentiallySquareIntegrable

/-!
# Globalization of a square-integrable representation of `GL_n` with two supercuspidal places

This module states, without proof, that an irreducible admissible square-integrable
representation `ρ` of `GL_{r+1}(K_{v₀})`, `0 < r`, prescribed at a finite place `v₀` of a number
field `K`, is up to a unitary unramified determinant twist the local component at `v₀` of a
cuspidal realization with unitary central character. The realization has a spectral presentation
with irreducible admissible finite components that are supercuspidal at two further prescribed
finite places `v₁` and `v₂`. Nothing is asserted at the other finite places.

The completion `K_{v₀}` carries its completion topology, with the valuative relation and the
nonarchimedean local-field structure of `Langlands.Global.CompletionPadic.topologicalData v₀`.
Unramified means trivial on the elements of completion valuation one.

Sources: Arthur–Clozel 1989, Chapter 1, Lemma 6.5 and its proof (printed pp. 54–55) and
§2.2 and Lemma 2.4 (printed pp. 12–13); Henniart–Lemaire 2011, II.6.7–II.6.9 (printed pp. 123–125).
See `GeneralLinearDiscreteSeriesGlobalizationStatement.md`.
-/

noncomputable section

set_option autoImplicit false

universe u uV uQ

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Automorphic

/-- **Globalization of a square-integrable representation with two supercuspidal places.**
Let `K` be a number field with compact adele quotient `𝔸_K / K`, let `v₀`, `v₁`, `v₂` be pairwise
distinct finite places and `0 < r`. Give `K_{v₀}` its completion topology and the local-field
structure of `CompletionPadic.topologicalData v₀`. For every admissible irreducible
representation `ρ` of `GL_{r+1}(K_{v₀})` that is square-integrable modulo the center, there are
a cuspidal operator realization `S` of `GL_{r+1}` over `K` and a spectral presentation `D` of `S`
such that:

1. `S` has unitary central character;
2. every finite local component of `D` is irreducible and admissible;
3. the local components of `D` at `v₁` and at `v₂` are supercuspidal;
4. for some character `χ` of `K_{v₀}ˣ`, trivial on the elements of completion valuation one and
   of absolute value one, the twist `ρ ⊗ (χ ∘ det)` is equivalent to the local action of `D`
   at `v₀`. -/
def GeneralLinearDiscreteSeriesGlobalizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (v₀ v₁ v₂ : FinitePlace K), v₀ ≠ v₁ → v₀ ≠ v₂ → v₁ ≠ v₂ →
    ∀ (r : ℕ), 0 < r →
    letI : ValuativeRel (v₀.adicCompletion K) :=
      (CompletionPadic.topologicalData v₀).valuativeRel
    haveI : IsNonarchimedeanLocalField (v₀.adicCompletion K) :=
      (CompletionPadic.topologicalData v₀).localField
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (r + 1) (v₀.adicCompletion K)) V),
      IsAdmissible ρ → ρ.IsIrreducible → JacquetLanglands.IsSquareIntegrable ρ →
      ∃ (S : CuspidalOperatorRealization K r) (D : CuspidalSpectralPresentation.{u, uQ} S),
        ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S ∧
        (∀ v, (D.localComponent v).IsIrreducible ∧ (D.localComponent v).IsAdmissible) ∧
        (D.localComponent v₁).IsSupercuspidal ∧ (D.localComponent v₂).IsSupercuspidal ∧
        ∃ χ : (v₀.adicCompletion K)ˣ →* ℂˣ,
          (∀ t : (v₀.adicCompletion K)ˣ, Valued.v (t : v₀.adicCompletion K) = 1 → χ t = 1) ∧
          (∀ t : (v₀.adicCompletion K)ˣ, ‖(χ t : ℂ)‖ = 1) ∧
          Nonempty ((twist (χ.comp GeneralLinear.determinant) ρ).Equiv
            (D.localComponent v₀).representation)

end Langlands.TraceFormula
