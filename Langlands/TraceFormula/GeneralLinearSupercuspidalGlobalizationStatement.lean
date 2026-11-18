import Langlands.Automorphic.GroupSchemeFullAEL2Hilbert
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Analysis.OperatorIdeals
import Langlands.Analysis.OperatorTrace
import Langlands.Global.AdelicLocalInclusion
import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.GroupScheme.GeneralLinearPointTopology
import Langlands.Representation.Twist.Definitions
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Character.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Globalization of supercuspidal representations of `GL_n`

This module states, without proof, that finitely many irreducible supercuspidal representations
`π_v` of `GL_n(K_v)`, prescribed at a nonempty finite set `Σ` of finite places of a number field
`K`, occur up to unramified twists as the local components of one irreducible summand `P` of the
group-scheme cuspidal space `L²_cusp([GL_n])`. The summand `P` is unramified at every finite
place outside `Σ ∪ {v_aux}`, where `v_aux ∉ Σ` is an auxiliary finite place chosen by the user.

At each `v ∈ Σ` the local component is expressed in two ways. First, the twist
`π_v ⊗ (χ_v ∘ det)` by an unramified character `χ_v` embeds `GL_n(K_v)`-equivariantly into `P`.
Second, the trace of the integrated action on `P` of a function split at `v` factors through the
distribution character of that twist, as in the Library's local trace factorization statement
for irreducible cuspidal summands.

Sources: Arthur–Clozel 1989, Chapter 1, Lemma 6.5 (printed pp. 54–55); Henniart–Lemaire 2011,
II.6.7–II.6.9 (printed pp. 123–125). The unramified twist cannot be dropped in this model: see
`GeneralLinearSupercuspidalGlobalizationStatement.md`.
-/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula

local instance generalLinearSupercuspidalGlobalizationIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance generalLinearSupercuspidalGlobalizationSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The `GL_n` group scheme over `K`, for the bound variables `K` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

/-- **Globalization of supercuspidal representations of `GL_n`.** Let `K` be a number field,
`GL_n` the general linear group scheme over `K`, with group data as in the Library's cuspidal
decomposition statement, and `S = L²_cusp([GL_n])` with the right action `πc` of
`GL_n(𝔸_K)`. Let `Sc` be a nonempty finite set of finite places, `vaux ∉ Sc` a finite place,
and for each `v ∈ Sc` let `π v` be an irreducible supercuspidal representation of `GL_n(K_v)`.
Write `incl v : GL_n(K_v) → GL_n(𝔸_K)` for the inclusion at `v`. Then there is a nonzero closed
`πc`-invariant subspace `P` of `S` without closed invariant subspaces other than `⊥` and `P`
such that:

1. some nonzero `x ∈ P` is fixed by `incl w (GL_n(𝒪_w))` for every finite place `w ∉ Sc`,
   `w ≠ vaux`;
2. for each `v ∈ Sc` there is a character `χ` of `K_vˣ`, trivial on the valuation-one units,
   such that for `ρ = π v ⊗ (χ ∘ det)`:
   (a) there is a nonzero linear map `Tv` from the space of `π v` to `P` with
       `Tv (ρ g y) = πc (incl v g) (Tv y)`;
   (b) for all Haar measures `μv` on `GL_n(K_v)` and `ν` on `GL_n(𝔸_K)`, `ρ` is admissible and
       there is `C : (GL_n(𝔸_K) → ℂ) → ℂ` such that, for every Schwartz–Bruhat function `fv` on
       `GL_n(K_v)` and every `fw` invariant under right translation by `GL_n(K_v)`, if
       `f g = fv (g_v) * fw g` is `ν`-integrable and the compression to `P` of its integrated
       action on `S` is trace class, then that trace equals `tr ρ(fv) · C fw`, where
       `tr ρ(fv)` is the Library's distribution character for `μv`. -/
def GeneralLinearSupercuspidalGlobalizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant]
    [∀ v : Langlands.Global.FinitePlace K,
      MeasurableSpace (GeneralLinear n (v.adicCompletion K))]
    [∀ v : Langlands.Global.FinitePlace K, BorelSpace (GeneralLinear n (v.adicCompletion K))]
    [∀ v : Langlands.Global.FinitePlace K,
      LocallyCompactSpace (GeneralLinear n (v.adicCompletion K))]
    [∀ v : Langlands.Global.FinitePlace K,
      TotallyDisconnectedSpace (GeneralLinear n (v.adicCompletion K))]
    (Sc : Finset (Langlands.Global.FinitePlace K)), Sc.Nonempty →
    ∀ (vaux : Langlands.Global.FinitePlace K), vaux ∉ Sc →
    ∀ (V : Langlands.Global.FinitePlace K → Type w) [∀ v, AddCommGroup (V v)]
      [∀ v, Module ℂ (V v)]
      (π : ∀ v : Langlands.Global.FinitePlace K,
        Representation ℂ (GeneralLinear n (v.adicCompletion K)) (V v)),
      (∀ v ∈ Sc, (π v).IsIrreducible ∧ GeneralLinear.IsSupercuspidal (π v)) →
    let S := fullAEL2CuspidalSubmodule K GLₙ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction K GLₙ hPD hG T i hi I e hc
    let eᵥ : ∀ v : Langlands.Global.FinitePlace K,
        PlaceGroupPoints K GLₙ (.inr v) ≃ₜ* GeneralLinear n (v.adicCompletion K) := fun v =>
      GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
        (placeCompletion K (.inr v))
    let incl : ∀ v : Langlands.Global.FinitePlace K,
        GeneralLinear n (v.adicCompletion K) →* AdelicGroupPoints K GLₙ := fun v =>
      (ofPlace K GLₙ (.inr v)).comp (eᵥ v).symm.toMulEquiv.toMonoidHom
    ∃ (P : Submodule ℂ S) (_ : CompleteSpace P), P ≠ ⊥ ∧
      (∀ (a : AdelicGroupPoints K GLₙ), ∀ x ∈ P, πc a x ∈ P) ∧
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ (a : AdelicGroupPoints K GLₙ), ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) ∧
      (∃ x ∈ P, x ≠ 0 ∧ ∀ w : Langlands.Global.FinitePlace K, w ∉ Sc → w ≠ vaux →
        ∀ k ∈ FiniteAdelicGL.localIntegral K n w, πc (incl w k) x = x) ∧
      ∀ v ∈ Sc, ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
        (∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 → χ t = 1) ∧
        let ρ := Langlands.twist (χ.comp GeneralLinear.determinant) (π v)
        (∃ Tv : V v →ₗ[ℂ] P, Tv ≠ 0 ∧ ∀ g y, (Tv (ρ g y) : S) = πc (incl v g) (Tv y)) ∧
        ∀ (μv : Measure (GeneralLinear n (v.adicCompletion K))) [μv.IsHaarMeasure]
          (ν : Measure (AdelicGroupPoints K GLₙ)) [ν.IsHaarMeasure],
          ∃ (hρ : IsAdmissible ρ) (C : (AdelicGroupPoints K GLₙ → ℂ) → ℂ),
            ∀ (fv : SchwartzBruhat (GeneralLinear n (v.adicCompletion K)))
              (fw : AdelicGroupPoints K GLₙ → ℂ),
              (∀ g x, fw (g * ofPlace K GLₙ (.inr v) x) = fw g) →
              ∀ hf : Integrable (fun g => fv (eᵥ v (atPlace K GLₙ (.inr v) g)) * fw g) ν,
                let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                  fullAEL2CuspidalIntegratedAction K GLₙ hPD hG T i hi I e hc ν _ hf ∘L
                    P.subtypeL
                IsTraceClass (E := (P : Submodule ℂ S)) RPf →
                  operatorTrace (E := (P : Submodule ℂ S)) RPf =
                    Character.distribution μv ρ hρ fv * C fw

end Langlands.TraceFormula
