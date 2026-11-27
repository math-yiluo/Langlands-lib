import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Analysis.OperatorIdeals
import Langlands.Analysis.OperatorTrace
import Langlands.TraceFormula.TwistedOrbital
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.AdelicGroupRationalTopology
import Langlands.Global.AdelicGroupPointTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The trace formula on a compact actual adelic quotient

Let `F` be a number field, `G` an affine group scheme over `F`, locally of finite type, and
`[G] = A⁺ G(F) \ G(𝔸_F)` the Library's positive rational quotient, for a central split torus `T`
along which restriction of rational characters is injective with image of finite index. Assume
that `[G]` is compact. Let `f = f₁ * f₂` be the Haar convolution of two compactly supported
continuous functions on `G(𝔸_F)`, `R(f)` its integrated right action on `L²([G])`, and
`f¹(x) = ∫_{A⁺} f(a x) da` on the norm-one subgroup `G(𝔸_F)¹`, with `Γ` the image of `G(F)`
there. Then `R(f)` is trace class, and:

* (geometric expansion) there are finitely many pairwise non-`Γ`-conjugate `γ ∈ Γ` covering
  every class on whose `G(𝔸_F)¹`-orbit `f¹` is somewhere nonzero, and for all compatible
  measures `tr R(f) = ∑_γ vol(Γ_γ \ G(𝔸_F)¹_γ) ∫_{G(𝔸_F)¹_γ \ G(𝔸_F)¹} f¹(x⁻¹ γ x) dx`,
  with finite volumes and absolutely convergent orbital integrals;
* (spectral expansion) for every Hilbert sum decomposition of `L²([G])` into nonzero closed
  invariant irreducible subspaces `P`, the compressions of `R(f)` to the `P` are trace class
  and `tr R(f) = ∑_P tr (R(f)|_P)`, absolutely convergent.

This is the Selberg trace formula for compact quotient, Arthur, *An introduction to the trace
formula* (2005), §1, (1.1)–(1.5), on the actual adelic quotient. For the unitary similitude
group `G` over `ℚ` of Kottwitz (1992), §1, attached to a division algebra with an involution of
the second kind, and `T = A_G`, it gives Kottwitz (1992), (4.1). His central character on
`A_G(ℝ)⁰` and his Tamagawa coefficients are normalizations explained in
`GroupSchemeCompactQuotientTraceFormulaStatement.md`; the identification of the coefficients
uses that the centralizers of rational elements of this `G` are connected.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration
open Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

/-- The trace formula on a compact actual adelic quotient. In the setting of
`GroupSchemeCompactQuotientL2DecompositionStatement`, assume that the positive rational
quotient `[G]` is compact. Let `f = f₁ * f₂` be the Haar convolution of compactly supported
continuous functions on `G(𝔸_F)`, `R(f)` its integrated right action on `L²([G])`, and
`fOne(x) = ∫ f(a x) da` its average over the positive real points `A⁺` of the central split
torus, for the Library's normalized Haar measure on `A⁺`, as a function on the norm-one subgroup
`G(𝔸_F)¹`. Then `f` is integrable, `R(f)` is trace class, and:

* there are finitely many rational norm-one points `r j`, pairwise non-conjugate under the
  rational subgroup `Γ`, such that every `q ∈ Γ` with `fOne(x⁻¹ q x) ≠ 0` for some
  `x ∈ G(𝔸_F)¹` is `Γ`-conjugate to some `r j`; and for all right-invariant Radon measures
  `μC j` on the centralizers `C j` of `r j` in `G(𝔸_F)¹` and all compatible quotient measures
  on `C j \ G(𝔸_F)¹` and on `(Γ ∩ C j) \ C j`, the volumes of `(Γ ∩ C j) \ C j` are finite, the
  orbit functions of `fOne` are integrable, and `tr R(f) = ∑ j, vol((Γ ∩ C j) \ C j) · O_{r j}(fOne)`;
* for every set `A` of nonzero closed invariant topologically irreducible subspaces of
  `L²([G])` whose inclusions form a Hilbert sum, the compression `p_P ∘ R(f) ∘ ι_P` of `R(f)` to
  each `P ∈ A` is trace class, the norms of the traces of the compressions are summable, and
  the traces sum to `tr R(f)`. -/
def GroupSchemeCompactQuotientTraceFormulaStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    CompactSpace (PositiveRationalQuotient F G T i) →
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    let π := haarQuotientL2BoundedRightAction F G T i hi I e hc
    ∀ f₁ f₂ : C_c(AdelicGroupPoints F G, ℂ),
    let f : AdelicGroupPoints F G → ℂ := fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG
    let fOne : normOneSubgroup F G → ℂ := fun x =>
      ∫ a, f (positivePointMap F G T i a * x)
        ∂normalizedPositiveHaarMeasure F G T i hi I e hc
    ∃ h : Integrable f μG,
      let Rf := haarQuotientL2IntegratedAction F G T i hi I e hc μG f h
      IsTraceClass Rf ∧
      (∃ (m : ℕ) (r : Fin m → rationalNormOneSubgroup F G),
        (∀ j k, IsTwistedConjugate (rationalNormOneSubgroup F G)
          (MonoidHom.id (normOneSubgroup F G)) (r j : normOneSubgroup F G)
          (r k : normOneSubgroup F G) → j = k) ∧
        (∀ q ∈ rationalNormOneSubgroup F G,
          (∃ x : normOneSubgroup F G, fOne (x⁻¹ * q * x) ≠ 0) →
          ∃ j, IsTwistedConjugate (rationalNormOneSubgroup F G)
            (MonoidHom.id (normOneSubgroup F G)) (r j : normOneSubgroup F G) q) ∧
        ∀ [∀ j, MeasurableSpace (LeftQuotient (twistedCentralizer
              (MonoidHom.id (normOneSubgroup F G)) (r j : normOneSubgroup F G)))]
          [∀ j, BorelSpace (LeftQuotient (twistedCentralizer
              (MonoidHom.id (normOneSubgroup F G)) (r j : normOneSubgroup F G)))]
          [∀ j, MeasurableSpace (LeftQuotient ((rationalNormOneSubgroup F G).subgroupOf
              (twistedCentralizer (MonoidHom.id (normOneSubgroup F G))
                (r j : normOneSubgroup F G))))]
          [∀ j, BorelSpace (LeftQuotient ((rationalNormOneSubgroup F G).subgroupOf
              (twistedCentralizer (MonoidHom.id (normOneSubgroup F G))
                (r j : normOneSubgroup F G))))]
          (μC : ∀ j, Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup F G))
              (r j : normOneSubgroup F G)))
          [∀ j, (μC j).IsMulRightInvariant] [∀ j, IsFiniteMeasureOnCompacts (μC j)]
          [∀ j, (μC j).IsOpenPosMeasure]
          (νC : ∀ j, Measure (LeftQuotient (twistedCentralizer
              (MonoidHom.id (normOneSubgroup F G)) (r j : normOneSubgroup F G))))
          (νΓC : ∀ j, Measure (LeftQuotient ((rationalNormOneSubgroup F G).subgroupOf
              (twistedCentralizer (MonoidHom.id (normOneSubgroup F G))
                (r j : normOneSubgroup F G))))),
          (∀ j, IsCompatible
            (twistedCentralizer (MonoidHom.id (normOneSubgroup F G))
              (r j : normOneSubgroup F G))
            (Measure.haar : Measure (normOneSubgroup F G)) (μC j) (νC j)) →
          (∀ j, IsCompatible
            ((rationalNormOneSubgroup F G).subgroupOf
              (twistedCentralizer (MonoidHom.id (normOneSubgroup F G))
                (r j : normOneSubgroup F G)))
            (μC j) Measure.count (νΓC j)) →
          (∀ j, νΓC j Set.univ ≠ ⊤) ∧
          (∀ j, Integrable (twistedOrbitFunction (MonoidHom.id (normOneSubgroup F G))
            (r j : normOneSubgroup F G) fOne) (νC j)) ∧
          operatorTrace Rf =
            ∑ j, ((νΓC j Set.univ).toReal : ℂ) *
              orbitalIntegral (r j : normOneSubgroup F G) (νC j) fOne) ∧
      ∀ (A : Set (Submodule ℂ (Lp ℂ 2 μQ)))
        [∀ P : A, CompleteSpace (P : Submodule ℂ (Lp ℂ 2 μQ))],
        (∀ P ∈ A, P ≠ ⊥ ∧ IsClosed (P : Set (Lp ℂ 2 μQ)) ∧
          (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, π a x ∈ P) ∧
          ∀ Q : Submodule ℂ (Lp ℂ 2 μQ), Q ≤ P → IsClosed (Q : Set (Lp ℂ 2 μQ)) →
            (∀ (a : AdelicGroupPoints F G), ∀ x ∈ Q, π a x ∈ Q) → Q = ⊥ ∨ Q = P) →
        IsHilbertSum ℂ (fun P : A => (P : Submodule ℂ (Lp ℂ 2 μQ)))
          (fun P => (P : Submodule ℂ (Lp ℂ 2 μQ)).subtypeₗᵢ) →
        let cR : (P : A) →
            ((P : Submodule ℂ (Lp ℂ 2 μQ)) →L[ℂ] (P : Submodule ℂ (Lp ℂ 2 μQ))) := fun P =>
          (P : Submodule ℂ (Lp ℂ 2 μQ)).orthogonalProjectionOnto ∘L Rf ∘L
            (P : Submodule ℂ (Lp ℂ 2 μQ)).subtypeL
        let tR : A → ℂ := fun P => operatorTrace (E := (P : Submodule ℂ (Lp ℂ 2 μQ))) (cR P)
        (∀ P : A, IsTraceClass (E := (P : Submodule ℂ (Lp ℂ 2 μQ))) (cR P)) ∧
        Summable (fun P : A => ‖tR P‖) ∧ HasSum tR (operatorTrace Rf)

end Langlands.TraceFormula
