import Langlands.TraceFormula.GroupSchemeCuspidalLocalTraceFactorizationStatement

/-!
# Local trace factorization on an irreducible cuspidal summand, with the local factor isotypic

This module strengthens `GroupSchemeCuspidalLocalTraceFactorizationStatement` (Task 7701). That
statement provides, for an irreducible closed invariant subspace `P` of the group-scheme
cuspidal space `L²_cusp([G])` and a finite place `v`, an irreducible admissible representation
`ρ_v` of `G(F_v)` whose character splits off the traces on `P`, in untwisted and twisted form.
It does not say how `ρ_v` is related to `P`. The present statement adds that `ρ_v` occurs in
`P` (it has a nonzero `G(F_v)`-equivariant linear map into `P`) and that `P` is
`ρ_v`-isotypic for `G(F_v)`: every smooth irreducible representation of `G(F_v)` with a
nonzero `G(F_v)`-equivariant linear map into `P` is isomorphic to `ρ_v`. Together these two
clauses determine the class of `ρ_v` by `P`, so the local factor can be compared with local
components given by other means.

The argument is that of Task 7701. Since `G(F_v)` is of type I, the unitary representation on
`P` is a Hilbert tensor product `π_v ⊗̂ π^v` with `G(F_v)` acting on the first factor
(Getz–Hahn, Theorem 3.10.2; Folland, Theorem 7.17), and `ρ_v` is the representation on the
smooth vectors of `π_v`. Composing an equivariant map into `P` with `id ⊗ λ` for a suitable
continuous functional `λ` on `π^v` gives a nonzero equivariant map into the smooth vectors of
`π_v`, which is an isomorphism by irreducibility (compare Flath 1979, Theorem 1).

The statement contains no proof. The paired Markdown gives the sources and the argument.
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

/-- **Local trace factorization on an irreducible cuspidal summand, with an isotypic local
factor.** The data and hypotheses are those of `GroupSchemeCuspidalLocalTraceFactorizationStatement`:
group data as in the Library's cuspidal decomposition statement, a finite place `v` of `F`
(with the measurable and topological structure on `G(F_v)` given as instance binders), a Haar
measure `μv` on `G(F_v)`, a Haar measure `ν` on `G(𝔸_F)`, and a nonzero complete subspace `P`
of the cuspidal space `S` that is invariant under the right action `πc` of `G(𝔸_F)` and has no
closed invariant subspaces other than `⊥` and `P`. Then there is an irreducible admissible
representation `ρ` of `G(F_v)` on a complex vector space `V` satisfying the four assertions
below.

0. (realization) there is a nonzero linear map `j₀ : V → S` with range in `P` and
   `j₀ (ρ y x) = πc (ofPlace F G (.inr v) y) (j₀ x)` for all `y ∈ G(F_v)` and `x ∈ V`;
0'. (isotypy) for every smooth irreducible representation `ρ'` of `G(F_v)` on a complex vector
   space `V' : Type u` and every nonzero linear map `j : V' → S` with range in `P` and
   `j (ρ' y x) = πc (ofPlace F G (.inr v) y) (j x)` for all `y` and `x`, there is a linear
   equivalence `E : V' ≃ V` with `E (ρ' y x) = ρ y (E x)`;
1. the untwisted trace factorization, word for word as part 1 of
   `GroupSchemeCuspidalLocalTraceFactorizationStatement`;
2. the twisted trace factorization, word for word as part 2 of
   `GroupSchemeCuspidalLocalTraceFactorizationStatement`.

Each of parts 1 and 2 supplies one functional `C` for all test-function pairs `fv`, `fw` in
that part. -/
def GroupSchemeCuspidalIsotypicTraceFactorizationStatement : Prop :=
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
        (∃ j₀ : V →ₗ[ℂ] S, j₀ ≠ 0 ∧ LinearMap.range j₀ ≤ P ∧
          ∀ y x, j₀ (ρ y x) = πc (ofPlace F G (.inr v) y) (j₀ x)) ∧
        (∀ (V' : Type u) [AddCommGroup V'] [Module ℂ V']
            (ρ' : Representation ℂ (PlaceGroupPoints F G (.inr v)) V'),
          IsSmooth ρ' → ρ'.IsIrreducible →
          ∀ j : V' →ₗ[ℂ] S, j ≠ 0 → LinearMap.range j ≤ P →
            (∀ y x, j (ρ' y x) = πc (ofPlace F G (.inr v) y) (j x)) →
            ∃ E : V' ≃ₗ[ℂ] V, ∀ y x, E (ρ' y x) = ρ y (E x)) ∧
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
