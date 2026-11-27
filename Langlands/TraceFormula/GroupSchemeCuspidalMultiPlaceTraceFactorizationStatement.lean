import Langlands.TraceFormula.GroupSchemeCuspidalIsotypicTraceFactorizationStatement
import Langlands.Global.InfiniteAdelicModularCharacter
import Langlands.Representation.Archimedean.SmoothVectors
import Langlands.Representation.Unitary.IntegratedOperator

/-!
# Trace factorization over a finite set of finite places and the archimedean component on an irreducible cuspidal summand

The Library statement `GroupSchemeCuspidalIsotypicTraceFactorizationStatement` splits one finite
place `v` off the traces on an irreducible closed invariant subspace `P` of the group-scheme
cuspidal space `S = L²_cusp([G])`. The statement of this module splits off, at the same time, a
finite set `places` of finite places and the archimedean component `G(F_∞) = G(F ⊗ ℝ)`
(the points `InfiniteAdelicGroupPoints F G`, inserted into `G(𝔸_F)` by
`AdelicGroupPoints.ofInfinite`):

* for each `p ∈ places`, an irreducible admissible representation `ρ_p` of `G(F_p)` with the
  realization and isotypy clauses of the one-place statement;
* an irreducible unitary representation `σ` of `G(F_∞)` on a Hilbert space, with an isometric
  `G(F_∞)`-equivariant embedding into `P`, such that every irreducible unitary representation of
  `G(F_∞)` with a nonzero bounded equivariant map into `P` is unitarily equivalent to `σ`;
* one functional `C` such that for every product test function
  `f(g) = f_∞(g_∞) · ∏_{p ∈ places} f_p(g_p) · f^w(g)`, with `f_∞` integrable on `G(F_∞)` and
  `σ(f_∞)` trace class, `f_p` Schwartz–Bruhat on `G(F_p)` and `f^w` right invariant under
  `G(F_∞)` and every `G(F_p)`, `p ∈ places`, a trace-class compression of `R_S(f)` to `P` has trace
  `tr σ(f_∞) · ∏_p Character.distribution μ_p ρ_p (f_p) · C(f^w)`.

The archimedean operator is `σ(f_∞) = ∫ f_∞(g) σ(g) dμ_∞(g)`, the Library's
`Langlands.Analysis.integratedIsometricAction`, and its character value is the Library's
`operatorTrace` of that operator. The archimedean test functions are all integrable `f_∞` with
`σ(f_∞)` trace class; by Harish-Chandra's theorems this class contains every smooth compactly
supported function.

The reason is the one for the one-place statement, iterated: `G(𝔸_F)` is the product of `G(F_∞)`,
the `G(F_p)` for `p ∈ places`, and the points away from these places; `G(F_∞)` and every `G(F_p)`
are of type I (Getz–Hahn, Theorem 3.10.2), so the irreducible unitary representation on `P` is a
Hilbert tensor product of irreducible unitary representations of the factors (Folland,
Theorem 7.17, applied repeatedly), and the trace of a tensor product of trace-class operators is
the product of their traces.

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

/-- **Trace factorization over a finite set of finite places and the archimedean component on an
irreducible cuspidal summand.**

The group data `F, G, hPD, hG, T, i, hi, I, e, hc` and the right invariance of Haar measure on
`normOneSubgroup F G` are those of `GroupSchemeCuspidalIsotypicTraceFactorizationStatement`.
Further data: a finite set `places` of finite places of `F`; the Borel, locally compact and
totally disconnected structure of `G(F_v)` for every finite place `v` (instance binders); a Haar
measure `μp p` on `G(F_p)` for each `p ∈ places`; a Haar measure `μinf` on
`G(F_∞) = InfiniteAdelicGroupPoints F G`; a Haar measure `ν` on `G(𝔸_F)`. Let `S` be the cuspidal
space with right action `πc`, and `P` a nonzero complete subspace of `S`, invariant under `πc`,
with no closed invariant subspaces other than `⊥` and `P`.

Then there are, for each `p ∈ places`, a representation `ρ p` of `G(F_p)` on a complex vector
space `V p : Type u` with `hρ p : IsAdmissible (ρ p)`, and a representation `σ` of `G(F_∞)` by
bounded operators on a complex Hilbert space `H : Type u` preserving the norm (`hσnorm`) and with
measurable orbit maps for `μinf` (`hσmeas`), such that:

1. every `ρ p` is irreducible;
2. (realization at `p`) there is a nonzero linear `j₀ : V p → S` with range in `P` and
   `j₀ (ρ p y x) = πc (ofPlace F G (.inr p) y) (j₀ x)`;
3. (isotypy at `p`) for every smooth irreducible representation `ρ'` of `G(F_p)` on
   `V' : Type u` and every nonzero linear `j : V' → S` with range in `P` and
   `j (ρ' y x) = πc (ofPlace F G (.inr p) y) (j x)`, there is a linear equivalence
   `E : V' ≃ V p` with `E (ρ' y x) = ρ p y (E x)`;
4. `σ` is jointly continuous (`Langlands.Archimedean.IsContinuousRepresentation`);
5. `σ` is topologically irreducible (`Langlands.Archimedean.IsTopologicallyIrreducible`);
6. (realization at `∞`) there is a linear isometry `jinf : H → S` with values in `P` and
   `jinf (σ g x) = πc (ofInfinite F G g) (jinf x)`;
7. (isotypy at `∞`) for every jointly continuous, norm-preserving, topologically irreducible
   representation `σ'` of `G(F_∞)` on a complex Hilbert space `H' : Type u` and every nonzero
   bounded linear `j : H' → S` with values in `P` and
   `j (σ' g x) = πc (ofInfinite F G g) (j x)`, there is a linear isometric equivalence
   `E : H' ≃ H` with `E (σ' g x) = σ g (E x)`;
8. (trace factorization) there is `C : (G(𝔸_F) → ℂ) → ℂ` such that, for every `μinf`-integrable
   `finf` on `G(F_∞)` for which `σf = ∫ finf(g) σ(g) dμinf(g)` is trace class, every family
   `fs p` of Schwartz–Bruhat functions on `G(F_p)`, `p ∈ places`, and every `fw : G(𝔸_F) → ℂ` with
   `fw (g * ofInfinite F G y) = fw g` and `fw (g * ofPlace F G (.inr p) x) = fw g` for
   `p ∈ places`, if `f g = finf (g_∞) * ∏_p fs p (g_p) * fw g` is `ν`-integrable (`hf`) and the
   compression of `R_S(f)` to `P` is trace class, then its trace is
   `operatorTrace σf * ∏_p Character.distribution (μp p) (ρ p) (hρ p) (fs p) * C fw`.

The functional `C` is one functional for all test functions. -/
def GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement : Prop :=
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
    (places : Finset (Langlands.Global.FinitePlace F))
    [∀ v : Langlands.Global.FinitePlace F, MeasurableSpace (PlaceGroupPoints F G (.inr v))]
    [∀ v : Langlands.Global.FinitePlace F, BorelSpace (PlaceGroupPoints F G (.inr v))]
    [∀ v : Langlands.Global.FinitePlace F, LocallyCompactSpace (PlaceGroupPoints F G (.inr v))]
    [∀ v : Langlands.Global.FinitePlace F,
      TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v))]
    (μp : ∀ p : places, Measure (PlaceGroupPoints F G (.inr p.1)))
    [∀ p, (μp p).IsHaarMeasure]
    (μinf : Measure (InfiniteAdelicGroupPoints F G)) [μinf.IsHaarMeasure]
    (ν : Measure (AdelicGroupPoints F G)) [ν.IsHaarMeasure],
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
    ∀ (P : Submodule ℂ S) [CompleteSpace P], P ≠ ⊥ →
      (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P) →
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ (a : AdelicGroupPoints F G), ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) →
      ∃ (V : places → Type u) (_ : ∀ p, AddCommGroup (V p)) (_ : ∀ p, Module ℂ (V p))
        (ρ : ∀ p : places, Representation ℂ (PlaceGroupPoints F G (.inr p.1)) (V p))
        (hρ : ∀ p, IsAdmissible (ρ p))
        (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H)
        (σ : InfiniteAdelicGroupPoints F G →* (H →L[ℂ] H))
        (hσnorm : ∀ g x, ‖σ g x‖ = ‖x‖)
        (hσmeas : ∀ x : H, AEStronglyMeasurable (fun g => σ g x) μinf),
        (∀ p, (ρ p).IsIrreducible) ∧
        (∀ p, ∃ j₀ : V p →ₗ[ℂ] S, j₀ ≠ 0 ∧ LinearMap.range j₀ ≤ P ∧
          ∀ y x, j₀ (ρ p y x) = πc (ofPlace F G (.inr p.1) y) (j₀ x)) ∧
        (∀ (p : places) (V' : Type u) [AddCommGroup V'] [Module ℂ V']
            (ρ' : Representation ℂ (PlaceGroupPoints F G (.inr p.1)) V'),
          IsSmooth ρ' → ρ'.IsIrreducible →
          ∀ j : V' →ₗ[ℂ] S, j ≠ 0 → LinearMap.range j ≤ P →
            (∀ y x, j (ρ' y x) = πc (ofPlace F G (.inr p.1) y) (j x)) →
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
        ∃ C : (AdelicGroupPoints F G → ℂ) → ℂ,
          ∀ (finf : InfiniteAdelicGroupPoints F G → ℂ) (hfinf : Integrable finf μinf),
            let σf : H →L[ℂ] H :=
              Langlands.Analysis.integratedIsometricAction μinf σ hσnorm hσmeas finf hfinf
            IsTraceClass σf →
            ∀ (fs : ∀ p : places, SchwartzBruhat (PlaceGroupPoints F G (.inr p.1)))
              (fw : AdelicGroupPoints F G → ℂ),
              (∀ g y, fw (g * ofInfinite F G y) = fw g) →
              (∀ g (p : places) x, fw (g * ofPlace F G (.inr p.1) x) = fw g) →
              ∀ hf : Integrable (fun g => finf (infinite F G g) *
                  (∏ p : places, fs p (atPlace F G (.inr p.1) g)) * fw g) ν,
                let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                  fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν _ hf ∘L
                    P.subtypeL
                IsTraceClass (E := (P : Submodule ℂ S)) RPf →
                  operatorTrace (E := (P : Submodule ℂ S)) RPf =
                    operatorTrace σf *
                      (∏ p : places, Character.distribution (μp p) (ρ p) (hρ p) (fs p)) *
                        C fw

end Langlands.TraceFormula
