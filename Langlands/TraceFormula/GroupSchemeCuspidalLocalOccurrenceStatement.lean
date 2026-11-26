import Langlands.TraceFormula.GroupSchemeCuspidalIsotypicTraceFactorizationStatement

/-!
# An irreducible admissible local representation occurs in each irreducible cuspidal summand

Let `P` be a nonzero closed subspace of the group-scheme cuspidal space `L²_cusp([G])`,
invariant and topologically irreducible under the right action of `G(𝔸_F)`, and let `v` be
a finite place of `F`. The statement says that some irreducible admissible representation of
`G(F_v)` maps nonzero and `G(F_v)`-equivariantly into `P`.

This is clause 0 (realization) of `GroupSchemeCuspidalIsotypicTraceFactorizationStatement`
together with the irreducibility and admissibility of its representation, under the same
hypotheses without the two Haar measures. Its conclusion is word for word the occurrence
hypothesis of `IsotypicTrace.cuspidalIsotypicTraceFactorization_of_exists_occurrence`, which
derives all of `GroupSchemeCuspidalIsotypicTraceFactorizationStatement` from it.

The statement contains no proof. The paired Markdown gives the sources and the argument.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.TraceFormula

/-- **Local occurrence in an irreducible cuspidal summand.** The data and hypotheses are
those of `GroupSchemeCuspidalIsotypicTraceFactorizationStatement`, in the same order, without
its two Haar measures `μv` and `ν`: group data as in the Library's cuspidal decomposition
statement, a finite place `v` of `F` (with the measurable and topological structure on
`G(F_v)` given as instance binders), and a nonzero complete subspace `P` of the cuspidal space
`S` that is invariant under the right action `πc` of `G(𝔸_F)` and has no closed invariant
subspaces other than `⊥` and `P`. Then there are an irreducible admissible representation `ρ`
of `G(F_v)` on a complex vector space `V : Type u` and a nonzero linear map `j₀ : V → S` with
range in `P` such that `j₀ (ρ y x) = πc (ofPlace F G (.inr v) y) (j₀ x)` for all
`y ∈ G(F_v)` and `x ∈ V`. -/
def GroupSchemeCuspidalLocalOccurrenceStatement : Prop :=
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
    [TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v))],
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
    ∀ (P : Submodule ℂ S) [CompleteSpace P], P ≠ ⊥ →
      (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P) →
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ (a : AdelicGroupPoints F G), ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) →
      ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V)
        (ρ : Representation ℂ (PlaceGroupPoints F G (.inr v)) V) (_ : IsAdmissible ρ),
        ρ.IsIrreducible ∧
        ∃ j₀ : V →ₗ[ℂ] S, j₀ ≠ 0 ∧ LinearMap.range j₀ ≤ P ∧
          ∀ y x, j₀ (ρ y x) = πc (ofPlace F G (.inr v) y) (j₀ x)

end Langlands.TraceFormula
