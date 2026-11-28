import Langlands.TraceFormula.GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement
import Langlands.TraceFormula.GroupSchemeCuspidalLocalTraceFactorizationStatement
import Langlands.Global.AdelicIwasawaAssembly

/-!
# Restricted tensor product factorization of traces and twisted traces on an irreducible cuspidal summand

The Library statements `GroupSchemeCuspidalLocalTraceFactorizationStatement` and
`GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement` split the local characters at finitely
many places off the traces on an irreducible closed invariant subspace `P` of the cuspidal space
`S = L²_cusp` of the positive rational quotient of `G(𝔸_F)`. They leave an unknown functional `C`
of the remaining components. The statement of this module replaces `C` by a constant, for test
functions that are the unit of a fixed integral family of compact open subgroups `U p` at the
remaining finite places.

Fix compact open subgroups `U p ≤ G(F_p)` at all finite places, forming an integral family
(`AdelicGroupPoints.IsUniformlyIntegral` of the family, and every adelic point has its
`p`-component in `U p` for almost all `p`), and Haar measures `μp p` on `G(F_p)` with
`μp p (U p) = 1` for almost all `p`. Then

* (untwisted part) `P` has a local factor `ρ p` at every finite place and a unitary archimedean
  factor `σ`, realized in `P` and making `P` isotypic, as in the multi-place statement; there
  are a finite set `Ebad` of finite places, outside which `μp p (U p) = 1` and the `U p`-fixed
  vectors of `ρ p` form a line, and a constant `c > 0`, such that for every finite set
  `Σ ⊇ Ebad` the trace on `P` of the integrated action of
  `f = finf ⊗ (⊗_{p ∈ Σ} fs p) ⊗ (⊗_{p ∉ Σ} 1_{U p})` is
  `c · tr σ(finf) · ∏_{p ∈ Σ} tr ρ p (fs p)`;
* (twisted part) for an automorphism `Θ` of `G(𝔸_F)` acting through automorphisms `θ p` of the
  `G(F_p)` and `θinf` of `G(F_∞)`, with `θ p (U p) = U p` for almost all `p`, whose twisting
  operator `I_Θ` preserves `P`, there are intertwiners `A p : ρ p ≅ ρ p ∘ θ p` and
  `Ainf : σ ≅ σ ∘ θinf`, with `A p` the identity on the `U p`-fixed line outside a finite set
  `Ebad' ⊇ Ebad`, and a constant `c' ≠ 0`, such that the trace on `P` of `R(f) ∘ I_Θ` is
  `c' · tr (σ(finf) ∘ Ainf) · ∏_{p ∈ Σ} tr (ρ p (fs p) ∘ A p)` for `Σ ⊇ Ebad'`.

The reason is Flath's restricted tensor product decomposition of `P`. At the places outside
`Σ` the operator of `1_{U p}` is the projection onto the fixed line, of trace `1`; in the
twisted case `I_Θ` restricted to `P` is a nonzero multiple of the restricted tensor product of
local intertwiners normalized on the fixed lines; and the trace of a tensor product of
trace-class operators is the product of the traces.

The module contains no proof. The paired Markdown gives the sources and the argument.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula

/-- **Restricted tensor product factorization of traces and twisted traces, with unit tails, on
an irreducible cuspidal summand of the positive quotient.**

The group data `F, G, hPD, hG, T, i, hi, I, e, hc`, the right invariance of Haar measure on
`normOneSubgroup F G`, the instance binders at every finite place, the Haar measures `μinf` on
`G(F_∞)` and `ν` on `G(𝔸_F)`, the cuspidal space `S` with its right action `πc`, and the
irreducible summand `P` are those of `GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement`.
Further data: open subgroups `U v` of `G(F_v)` at all finite places, all compact, with
`IsUniformlyIntegral F G (extendFinite F G (U ·))` and with `g_v ∈ U v` for almost all `v`, for
every `g ∈ G(𝔸_F)`; Haar measures `μp v` on `G(F_v)` with `μp v (U v) = 1` for almost all `v`.

Then there are, for every finite place `p`, an admissible representation `ρ p` of `G(F_p)` on
`V p : Type u`, a norm-preserving representation `σ` of `G(F_∞)` on a complex Hilbert space
`H : Type u` with `μinf`-measurable orbit maps, and a finite set `Ebad` of finite places, with:

1–7. the clauses 1–7 of `GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement` (irreducibility,
   realization in `P` and isotypy of `P`, at every finite place and at `∞`);
8. for every `p ∉ Ebad`, `μp p (U p) = 1` and the `U p`-fixed vectors of `ρ p` form a line;
9. there is a real `c > 0` such that, for every finite set `places ⊇ Ebad` of finite places,
   every `μinf`-integrable `finf` with `σf = ∫ finf(g) σ(g) dμinf(g)` trace class and every
   family `fs p` of Schwartz–Bruhat functions on `G(F_p)`, `p ∈ places`, if
   `f g = finf (g_∞) * ∏_{p ∈ places} fs p (g_p) * 1[∀ v ∉ places, g_v ∈ U v]` is `ν`-integrable
   and the compression to `P` of `R_S(f)` is trace class, its trace is
   `c * operatorTrace σf * ∏_{p ∈ places} Character.distribution (μp p) (ρ p) (hρ p) (fs p)`;
10. for every topological automorphism `Θ` of `G(𝔸_F)` preserving
   `positiveRationalSubgroup F G T i` (`hΘ`) and the quotient measure (`hΘμ`), all topological
   automorphisms `θ v` of `G(F_v)` and `θinf` of `G(F_∞)` with `(Θ g)_v = θ v (g_v)`,
   `Θ (ofPlace x) = ofPlace (θ v x)`, `(Θ g)_∞ = θinf (g_∞)` and
   `Θ (ofInfinite x) = ofInfinite (θinf x)`, and `θ v (U v) = U v` for almost all `v`: if the
   twisting operator `I_Θ` maps `P` into `P`, there are bijective linear `A p : V p → V p` with
   `A p (ρ p y x) = ρ p (θ p y) (A p x)`, a bijective bounded `Ainf : H → H` with
   `Ainf (σ g x) = σ (θinf g) (Ainf x)`, and a finite set `Ebad' ⊇ Ebad` such that for every
   `p ∉ Ebad'`, `θ p (U p) = U p` and `A p` fixes every `U p`-fixed vector of `ρ p`; and a
   complex `c' ≠ 0` such that, for `places ⊇ Ebad'` and `finf`, `fs`, `f` as in 9, if the
   compression to `P` of the compression to `S` of `R(f) ∘ I_Θ` is trace class, its trace is
   `c' * operatorTrace (σf ∘L Ainf) *
     ∏_{p ∈ places} BaseChange.twistedDistribution (μp p) (ρ p) (hρ p) (A p) (fs p)`. -/
def GroupSchemeCuspidalRestrictedTraceFactorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    [∀ v : Langlands.Global.FinitePlace F, MeasurableSpace (PlaceGroupPoints F G (.inr v))]
    [∀ v : Langlands.Global.FinitePlace F, BorelSpace (PlaceGroupPoints F G (.inr v))]
    [∀ v : Langlands.Global.FinitePlace F, LocallyCompactSpace (PlaceGroupPoints F G (.inr v))]
    [∀ v : Langlands.Global.FinitePlace F,
      TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v))]
    (U : ∀ v : Langlands.Global.FinitePlace F, OpenSubgroup (PlaceGroupPoints F G (.inr v))),
    (∀ v, IsCompact (U v : Set (PlaceGroupPoints F G (.inr v)))) →
    IsUniformlyIntegral F G (extendFinite F G fun v => (U v).toSubgroup) →
    (∀ g : AdelicGroupPoints F G,
      ∀ᶠ v : Langlands.Global.FinitePlace F in Filter.cofinite, atPlace F G (.inr v) g ∈ U v) →
    ∀ (μp : ∀ v : Langlands.Global.FinitePlace F, Measure (PlaceGroupPoints F G (.inr v)))
      [∀ v, (μp v).IsHaarMeasure],
    (∀ᶠ v : Langlands.Global.FinitePlace F in Filter.cofinite, μp v (U v) = 1) →
    ∀ (μinf : Measure (InfiniteAdelicGroupPoints F G)) [μinf.IsHaarMeasure]
      (ν : Measure (AdelicGroupPoints F G)) [ν.IsHaarMeasure],
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
    ∀ (P : Submodule ℂ S) [CompleteSpace P], P ≠ ⊥ →
      (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P) →
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ (a : AdelicGroupPoints F G), ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) →
      ∃ (V : Langlands.Global.FinitePlace F → Type u) (_ : ∀ p, AddCommGroup (V p))
        (_ : ∀ p, Module ℂ (V p))
        (ρ : ∀ p, Representation ℂ (PlaceGroupPoints F G (.inr p)) (V p))
        (hρ : ∀ p, IsAdmissible (ρ p))
        (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H)
        (σ : InfiniteAdelicGroupPoints F G →* (H →L[ℂ] H))
        (hσnorm : ∀ g x, ‖σ g x‖ = ‖x‖)
        (hσmeas : ∀ x : H, AEStronglyMeasurable (fun g => σ g x) μinf)
        (Ebad : Finset (Langlands.Global.FinitePlace F)),
        (∀ p, (ρ p).IsIrreducible) ∧
        (∀ p, ∃ j₀ : V p →ₗ[ℂ] S, j₀ ≠ 0 ∧ LinearMap.range j₀ ≤ P ∧
          ∀ y x, j₀ (ρ p y x) = πc (ofPlace F G (.inr p) y) (j₀ x)) ∧
        (∀ (p : Langlands.Global.FinitePlace F) (V' : Type u) [AddCommGroup V'] [Module ℂ V']
            (ρ' : Representation ℂ (PlaceGroupPoints F G (.inr p)) V'),
          IsSmooth ρ' → ρ'.IsIrreducible →
          ∀ j : V' →ₗ[ℂ] S, j ≠ 0 → LinearMap.range j ≤ P →
            (∀ y x, j (ρ' y x) = πc (ofPlace F G (.inr p) y) (j x)) →
            ∃ E : V' ≃ₗ[ℂ] V p, ∀ y x, E (ρ' y x) = ρ p y (E x)) ∧
        Langlands.Archimedean.IsContinuousRepresentation σ ∧
        Langlands.Archimedean.IsTopologicallyIrreducible σ ∧
        (∃ jinf : H →ₗᵢ[ℂ] S, (∀ x, jinf x ∈ P) ∧
          ∀ g x, jinf (σ g x) = πc (ofInfinite F G g) (jinf x)) ∧
        (∀ (H' : Type u) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
            (σ' : InfiniteAdelicGroupPoints F G →* (H' →L[ℂ] H')),
          Langlands.Archimedean.IsContinuousRepresentation σ' →
          (∀ g x, ‖σ' g x‖ = ‖x‖) →
          Langlands.Archimedean.IsTopologicallyIrreducible σ' →
          ∀ j : H' →L[ℂ] S, j ≠ 0 → (∀ x, j x ∈ P) →
            (∀ g x, j (σ' g x) = πc (ofInfinite F G g) (j x)) →
            ∃ E : H' ≃ₗᵢ[ℂ] H, ∀ g x, E (σ' g x) = σ g (E x)) ∧
        (∀ p ∉ Ebad, μp p (U p) = 1 ∧
          Module.finrank ℂ (fixedVectors (ρ p) (U p).toSubgroup) = 1) ∧
        (∃ c : ℝ, 0 < c ∧
          ∀ places : Finset (Langlands.Global.FinitePlace F), Ebad ⊆ places →
          ∀ (finf : InfiniteAdelicGroupPoints F G → ℂ) (hfinf : Integrable finf μinf),
            let σf : H →L[ℂ] H :=
              Langlands.Analysis.integratedIsometricAction μinf σ hσnorm hσmeas finf hfinf
            IsTraceClass σf →
            ∀ fs : ∀ p : places, SchwartzBruhat (PlaceGroupPoints F G (.inr p.1)),
              let f : AdelicGroupPoints F G → ℂ := fun g =>
                finf (infinite F G g) * (∏ p : places, fs p (atPlace F G (.inr p.1) g)) *
                  Set.indicator {g' : AdelicGroupPoints F G |
                    ∀ v : Langlands.Global.FinitePlace F, v ∉ places →
                      atPlace F G (.inr v) g' ∈ U v}
                    (fun _ => (1 : ℂ)) g
              ∀ hf : Integrable f ν,
                let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                  fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν _ hf ∘L
                    P.subtypeL
                IsTraceClass (E := (P : Submodule ℂ S)) RPf →
                  operatorTrace (E := (P : Submodule ℂ S)) RPf =
                    (c : ℂ) * operatorTrace σf *
                      ∏ p : places, Character.distribution (μp p.1) (ρ p.1) (hρ p.1) (fs p)) ∧
        ∀ (Θ : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G)
          (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup F G T i ↔
            x ∈ positiveRationalSubgroup F G T i)
          (hΘμ : MeasurePreserving
            (quotientAutomorphism (positiveRationalSubgroup F G T i) Θ hΘ).symm
            (positiveRationalQuotientHaarMeasure F G T i)
            (positiveRationalQuotientHaarMeasure F G T i))
          (θ : ∀ v : Langlands.Global.FinitePlace F,
            PlaceGroupPoints F G (.inr v) ≃ₜ* PlaceGroupPoints F G (.inr v))
          (θinf : InfiniteAdelicGroupPoints F G ≃ₜ* InfiniteAdelicGroupPoints F G),
          (∀ v g, atPlace F G (.inr v) (Θ g) = θ v (atPlace F G (.inr v) g)) →
          (∀ v x, Θ (ofPlace F G (.inr v) x) = ofPlace F G (.inr v) (θ v x)) →
          (∀ g, infinite F G (Θ g) = θinf (infinite F G g)) →
          (∀ x, Θ (ofInfinite F G x) = ofInfinite F G (θinf x)) →
          (∀ᶠ v : Langlands.Global.FinitePlace F in Filter.cofinite,
            ∀ x, θ v x ∈ U v ↔ x ∈ U v) →
          let IΘ := twistOperator (positiveRationalSubgroup F G T i) Θ hΘ
            (positiveRationalQuotientHaarMeasure F G T i) hΘμ
          (∀ x ∈ P, ∃ y ∈ P, (y : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)) =
            IΘ (x : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i))) →
          ∃ (A : ∀ p, V p →ₗ[ℂ] V p) (Ainf : H →L[ℂ] H)
            (Ebad' : Finset (Langlands.Global.FinitePlace F)),
            (∀ p, Function.Bijective (A p)) ∧
            (∀ p y x, A p (ρ p y x) = ρ p (θ p y) (A p x)) ∧
            Function.Bijective Ainf ∧
            (∀ g x, Ainf (σ g x) = σ (θinf g) (Ainf x)) ∧
            Ebad ⊆ Ebad' ∧
            (∀ p ∉ Ebad', (∀ x, θ p x ∈ U p ↔ x ∈ U p) ∧
              ∀ x ∈ fixedVectors (ρ p) (U p).toSubgroup, A p x = x) ∧
            ∃ c' : ℂ, c' ≠ 0 ∧
              ∀ places : Finset (Langlands.Global.FinitePlace F), Ebad' ⊆ places →
              ∀ (finf : InfiniteAdelicGroupPoints F G → ℂ) (hfinf : Integrable finf μinf),
                let σf : H →L[ℂ] H :=
                  Langlands.Analysis.integratedIsometricAction μinf σ hσnorm hσmeas finf hfinf
                IsTraceClass σf →
                ∀ fs : ∀ p : places, SchwartzBruhat (PlaceGroupPoints F G (.inr p.1)),
                  let f : AdelicGroupPoints F G → ℂ := fun g =>
                    finf (infinite F G g) * (∏ p : places, fs p (atPlace F G (.inr p.1) g)) *
                      Set.indicator {g' : AdelicGroupPoints F G |
                        ∀ v : Langlands.Global.FinitePlace F, v ∉ places →
                          atPlace F G (.inr v) g' ∈ U v}
                        (fun _ => (1 : ℂ)) g
                  ∀ hf : Integrable f ν,
                    let Rf := haarQuotientL2IntegratedAction F G T i hi I e hc ν _ hf
                    let BP : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                      (S.orthogonalProjectionOnto ∘L (Rf ∘L IΘ) ∘L S.subtypeL) ∘L P.subtypeL
                    IsTraceClass (E := (P : Submodule ℂ S)) BP →
                      operatorTrace (E := (P : Submodule ℂ S)) BP =
                        c' * operatorTrace (σf ∘L Ainf) *
                          ∏ p : places, Langlands.BaseChange.twistedDistribution (μp p.1)
                            (ρ p.1) (hρ p.1) (A p.1) (fs p)

end Langlands.TraceFormula
