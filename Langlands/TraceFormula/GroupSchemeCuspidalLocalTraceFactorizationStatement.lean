import Langlands.Automorphic.GroupSchemeFullAEL2Hilbert
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Analysis.OperatorIdeals
import Langlands.Analysis.OperatorTrace
import Langlands.TraceFormula.TwistedOrbital
import Langlands.Global.AdelicLocalInclusion
import Langlands.BaseChange.TwistedCharacter.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Local factorization of traces on an irreducible cuspidal summand

This module states that on an irreducible closed invariant subspace `P` of the
group-scheme cuspidal space `L²_cusp([G])` (the Library's `fullAEL2CuspidalSubmodule`), the
trace of the integrated action of a function `f = f_v ⊗ f^v`, split at a finite place `v`,
factors as `tr ρ_v(f_v) · C(f^v)` whenever the compression to `P` is trace class. Here `ρ_v`
is an irreducible admissible representation of `G(F_v)`, the local component of `P` at `v`.
The twisted form uses the same `ρ_v` for the trace-class compression of `R(f) ∘ I_Θ` to `P`,
when `I_Θ` preserves `P` and `Θ` acts at `v` through an automorphism `θ_v` of `G(F_v)`.
The local factor is then a twisted trace
`tr (ρ_v(f_v) ∘ A_v)` for a bijective `A_v` with `A_v ∘ ρ_v(y) = ρ_v(θ_v y) ∘ A_v`.

The argument splits `G(𝔸_F) = G(F_v) × G(𝔸_F^v)`. Since `G(F_v)` is of type I, the unitary
representation on `P` is a Hilbert tensor product `π_v ⊗̂ π^v` of irreducible unitary
representations (Getz–Hahn, Theorem 3.10.2 and Folland, Theorem 7.17). The representation `ρ_v`
is on the smooth vectors of `π_v` and is admissible by Harish-Chandra and Bernstein
(Getz–Hahn, Proposition 5.3.8 and Theorem 5.3.9). Henniart–Lemaire II.6.5 uses the factorization
of the global intertwining operator in cyclic base change.
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

/-- **Local trace factorization on an irreducible cuspidal summand.** For group data as in the
Library's cuspidal decomposition statement, a finite place `v` of `F` (with the measurable and
topological structure on `G(F_v)` given as instance binders), a Haar measure `μv` on `G(F_v)`,
a Haar measure `ν` on `G(𝔸_F)`, and a nonzero complete subspace `P` of the cuspidal space `S`
that is invariant under the right action `πc` of `G(𝔸_F)` and has no closed invariant
subspaces other than `⊥` and `P`, there is an irreducible admissible representation `ρ` of
`G(F_v)` on a complex vector space `V` satisfying both assertions below.

1. there is `C : (G(𝔸_F) → ℂ) → ℂ` such that, for every Schwartz–Bruhat function `fv` on
   `G(F_v)` and every `fw : G(𝔸_F) → ℂ` invariant under right translation by
   `ofPlace F G (.inr v) x` for all `x ∈ G(F_v)`, if `f g = fv (g_v) * fw g` (where
   `g_v = atPlace F G (.inr v) g`) is `ν`-integrable and the compression to `P` of its
   integrated action on `S` is trace class, then that trace equals
   `Character.distribution μv ρ hρ fv * C fw`.
2. for every topological automorphism `Θ` of `G(𝔸_F)` preserving the subgroup
   `positiveRationalSubgroup F G T i` and the quotient measure, and every topological
   automorphism `θv` of `G(F_v)` with `(Θ g)_v = θv (g_v)` and
   `Θ (ofPlace x) = ofPlace (θv x)`, if the twisting operator `I_Θ` maps `P` into `P`, then
   there are a bijective linear `Av : V → V` with `Av ∘ ρ y = ρ (θv y) ∘ Av` and
   `C : (G(𝔸_F) → ℂ) → ℂ` such that, for `fv`, `fw` and `f` as in part 1, if the compression to
   `P` of the compression to `S` of `R(f) ∘ I_Θ` is trace class, then its trace equals
   `BaseChange.twistedDistribution μv ρ hρ Av fv * C fw`.

Each part supplies one functional `C` for all test-function pairs `fv`, `fw` in that part. -/
def GroupSchemeCuspidalLocalTraceFactorizationStatement : Prop :=
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
    (v : Langlands.Global.FinitePlace F)
    [MeasurableSpace (PlaceGroupPoints F G (.inr v))]
    [BorelSpace (PlaceGroupPoints F G (.inr v))]
    [LocallyCompactSpace (PlaceGroupPoints F G (.inr v))]
    [TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v))]
    (μv : Measure (PlaceGroupPoints F G (.inr v))) [μv.IsHaarMeasure]
    (ν : Measure (AdelicGroupPoints F G)) [ν.IsHaarMeasure],
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
    ∀ (P : Submodule ℂ S) [CompleteSpace P], P ≠ ⊥ →
      (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P) →
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ (a : AdelicGroupPoints F G), ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) →
      ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V)
        (ρ : Representation ℂ (PlaceGroupPoints F G (.inr v)) V) (hρ : IsAdmissible ρ),
        ρ.IsIrreducible ∧
        (∃ C : (AdelicGroupPoints F G → ℂ) → ℂ,
          ∀ (fv : SchwartzBruhat (PlaceGroupPoints F G (.inr v)))
            (fw : AdelicGroupPoints F G → ℂ),
            (∀ g x, fw (g * ofPlace F G (.inr v) x) = fw g) →
            ∀ hf : Integrable (fun g => fv (atPlace F G (.inr v) g) * fw g) ν,
              let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν _ hf ∘L P.subtypeL
              IsTraceClass (E := (P : Submodule ℂ S)) RPf →
                operatorTrace (E := (P : Submodule ℂ S)) RPf = Character.distribution μv ρ hρ fv * C fw) ∧
        ∀ (Θ : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G)
          (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup F G T i ↔
            x ∈ positiveRationalSubgroup F G T i)
          (hΘμ : MeasurePreserving
            (quotientAutomorphism (positiveRationalSubgroup F G T i) Θ hΘ).symm
            (positiveRationalQuotientHaarMeasure F G T i)
            (positiveRationalQuotientHaarMeasure F G T i))
          (θv : PlaceGroupPoints F G (.inr v) ≃ₜ* PlaceGroupPoints F G (.inr v)),
          (∀ g, atPlace F G (.inr v) (Θ g) = θv (atPlace F G (.inr v) g)) →
          (∀ x, Θ (ofPlace F G (.inr v) x) = ofPlace F G (.inr v) (θv x)) →
          let IΘ := twistOperator (positiveRationalSubgroup F G T i) Θ hΘ
            (positiveRationalQuotientHaarMeasure F G T i) hΘμ
          (∀ x ∈ P, ∃ y ∈ P, (y : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)) =
            IΘ (x : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i))) →
          ∃ Av : V →ₗ[ℂ] V, Function.Bijective Av ∧
            (∀ y w, Av (ρ y w) = ρ (θv y) (Av w)) ∧
            ∃ C : (AdelicGroupPoints F G → ℂ) → ℂ,
              ∀ (fv : SchwartzBruhat (PlaceGroupPoints F G (.inr v)))
                (fw : AdelicGroupPoints F G → ℂ),
                (∀ g x, fw (g * ofPlace F G (.inr v) x) = fw g) →
                ∀ hf : Integrable (fun g => fv (atPlace F G (.inr v) g) * fw g) ν,
                  let Rf := haarQuotientL2IntegratedAction F G T i hi I e hc ν _ hf
                  let BP : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                    (S.orthogonalProjectionOnto ∘L (Rf ∘L IΘ) ∘L S.subtypeL) ∘L P.subtypeL
                  IsTraceClass (E := (P : Submodule ℂ S)) BP →
                    operatorTrace (E := (P : Submodule ℂ S)) BP =
                      Langlands.BaseChange.twistedDistribution μv ρ hρ Av fv * C fw

end Langlands.TraceFormula
