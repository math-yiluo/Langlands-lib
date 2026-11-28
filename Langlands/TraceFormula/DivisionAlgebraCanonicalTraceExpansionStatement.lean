import Langlands.TraceFormula.DivisionAlgebraSimpleTraceComparisonStatement
import Langlands.TraceFormula.SingleOrbitSimpleTrace

/-!
# The ordinary trace expansion for the units of a central division algebra

Let `F` be a number field, `A` a finite-dimensional central division algebra over `F` and
`G = GL₁(A)` its unit group scheme. For every smooth compactly supported test function `f` on
`G(𝔸_F)`, the proposition `DivisionAlgebraCanonicalTraceExpansionStatement` asserts that the
operator `R(f) = canonicalIntegratedAction` on the canonical `L²(A_G G(F) \ G(𝔸_F))` is trace
class, and that its trace is the finite sum, over the rational conjugacy classes `γ` on whose
`G(𝔸_F)¹`-orbit the norm-one average `f¹ = canonicalNormOneAverage` is somewhere nonzero, of
`vol(Γ_γ \ G(𝔸_F)¹_γ) · ∫_{G(𝔸_F)¹_γ \ G(𝔸_F)¹} f¹(x⁻¹ γ x) dx`, in the measure convention of
`SimpleTraceGeometricExpansion`.

This is the Selberg trace formula for compact quotient (Arthur, *An introduction to the trace
formula* (2005), §1, (1.1)–(1.4)) for `G(𝔸_F)¹` and its rational points. The quotient is compact
because `A` is a division algebra (Springer, *Reduction theory over global fields* (1994), §2.1,
(C), proved in §3.5), and `R(f)` is trace class for smooth compactly supported `f` as in
Getz–Hahn (2024), Lemma 9.3.3. The proposition is not proved in this module. See
`DivisionAlgebraCanonicalTraceExpansionStatement.md`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

set_option hygiene false in
/-- The unit group scheme `GL₁(A)` of `A`, for the bound variables `F` and `A`. -/
local notation "Gₐ" => FiniteAlgebraUnits.groupScheme (Module.finBasis F A)

/-- The action of a smooth compactly supported adelic test on the canonical automorphic
quotient of a central division algebra is trace class and has the ordinary finite
centralizer-weighted expansion of its norm-one average.

Let `F` be a number field, `A` a finite-dimensional central division algebra over `F` and
`G = Gₐ` its unit group scheme, with a connected reductivity witness `hD`. For every `f` with
`IsAdelicTestFunction F G f` and every witness `hf` of its integrability for `Measure.haar`:
`R(f) = canonicalIntegratedAction F G hD f hf` is trace class; and, writing
`H = normOneSubgroup F G`, `Γ = rationalNormOneSubgroup F G` and
`f¹ = canonicalNormOneAverage F G hD f`, there are finitely many `r j ∈ Γ`, pairwise not
`Γ`-conjugate, such that `f¹` is somewhere nonzero on the `H`-conjugacy class of each `r j`,
every `q ∈ Γ` with this property is `Γ`-conjugate to some `r j`, and
`SimpleTraceGeometricExpansion Γ (MonoidHom.id H) Measure.haar f¹ (tr R(f)) r` holds: for all
compatible centralizer and quotient measures, the volumes of `(Γ ∩ H_{r j}) \ H_{r j}` are
finite, the orbit functions of `f¹` are integrable and
`tr R(f) = ∑ j, vol((Γ ∩ H_{r j}) \ H_{r j}) · ∫_{H_{r j} \ H} f¹(x⁻¹ (r j) x) dx`. -/
def DivisionAlgebraCanonicalTraceExpansionStatement : Prop :=
  ∀ (F A : Type) [Field F] [NumberField F] [DivisionRing A] [Algebra F A]
    [FiniteDimensional F A] [Algebra.IsCentral F A]
    (hD : IsConnectedReductive Gₐ) (f : AdelicGroupPoints F Gₐ → ℂ),
    IsAdelicTestFunction F Gₐ f →
    ∀ hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints F Gₐ)),
    IsTraceClass (canonicalIntegratedAction F Gₐ hD f hf) ∧
    let H := normOneSubgroup F Gₐ
    let Γ := rationalNormOneSubgroup F Gₐ
    let fOne := canonicalNormOneAverage F Gₐ hD f
    ∃ (m : ℕ) (r : Fin m → Γ),
      (∀ i j, IsTwistedConjugate Γ (MonoidHom.id H) (r i : H) (r j : H) → i = j) ∧
      (∀ j, ∃ x : H, fOne (x⁻¹ * (r j : H) * x) ≠ 0) ∧
      (∀ q : Γ, (∃ x : H, fOne (x⁻¹ * (q : H) * x) ≠ 0) →
        ∃ j, IsTwistedConjugate Γ (MonoidHom.id H) (r j : H) (q : H)) ∧
      SimpleTraceGeometricExpansion Γ (MonoidHom.id H) (Measure.haar : Measure H) fOne
        (operatorTrace (canonicalIntegratedAction F Gₐ hD f hf)) r

end Langlands.TraceFormula
