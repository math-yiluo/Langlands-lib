import Langlands.Representation.CuspidalSupport.FiniteCuspidalEmbeddingAssembly
import Langlands.Representation.Aubert.General.CuspidalRemainderProjection
import Langlands.Representation.Aubert.General.RationalLeviCuspidalRemainderTransport

/-!
# Jacquet projections from supplied literal Levi splittings

Internal assembly of the local projection helper at the precise carrier
universes used by the actual finite induced-cuspidal embedding target.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {κ : Type uI} [Fintype κ]
  (P M U : Finset κ → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset κ) (J : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I J)).subgroupOf (M I))
      ((M (leviIndex I J)).subgroupOf (M I)) ((U (leviIndex I J)).subgroupOf (M I)))

/-- The local splitting condition restricted to the actual Jacquet modules
needed by the finite assembly. No splitting existence is asserted. -/
def LeviJacquetCuspidalRemainderSplittingTarget : Prop :=
  ∀ (A : SmoothRep.{0, uG, uV} ℂ G) (I : Finset κ),
    HasLeviCuspidalRemainderSplitting P M U hU I (hM I) (hL I)
      ((jacquetFunctor (h I) (hU I)).obj A)

omit [Fintype κ] in
/-- Supplied literal inside-Levi splittings give the exact objectwise
projection target, with target carrier universe `max uI uG uV`. -/
theorem cuspidalJacquetProjectionTarget_of_splittings
    (hsplit : LeviJacquetCuspidalRemainderSplittingTarget.{uI, uG, uV}
      P M U h hU hM hL) :
    CuspidalJacquetProjectionTarget.{uI, uG, uV} P M U h hU hM hL := by
  intro A
  have hproj (I : Finset κ) :
      ∃ C : SmoothRep.{0, uG, max uI uG uV} ℂ (M I),
        IsLeviCuspidal P M U hU I (hM I) (hL I) C ∧
        ∃ p : ((jacquetFunctor (h I) (hU I)).obj A).representation.IntertwiningMap
            C.representation,
          ∀ (B : SmoothRep.{0, uG, uV} ℂ (M I)),
            IsLeviCuspidal P M U hU I (hM I) (hL I) B →
            ∀ j : B.representation.IntertwiningMap
              ((jacquetFunctor (h I) (hU I)).obj A).representation,
              p.comp j = 0 → j = 0 := by
    let := (hM I).locallyCompactSpace
    exact HasCuspidalRemainderSplitting.exists_lifted_projection.{uI, uG, uV, uV,
      max uI uG} (hsplit A I)
  choose C hC p hp using hproj
  exact ⟨C, hC, p, hp⟩

/-- Combining supplied literal splittings with nonzero cuspidal Jacquet
detection gives the actual finite induced embedding. This remains conditional
on the stated local splitting input. -/
theorem finiteCuspidalInducedEmbedding_of_splittings
    (hδ : ∀ I, IsUnimodularModulus (U I) (hU I))
    (hlim : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (U I))
    (hdetect : ∀ B : SmoothRep.{0, uG, uV} ℂ G, Nontrivial B →
      ∃ I, Nontrivial ((jacquetFunctor (h I) (hU I)).obj B) ∧
        IsLeviCuspidal P M U hU I (hM I) (hL I)
          ((jacquetFunctor (h I) (hU I)).obj B))
    (hsplit : LeviJacquetCuspidalRemainderSplittingTarget.{uI, uG, uV}
      P M U h hU hM hL) :
    FiniteCuspidalInducedEmbeddingTarget.{uI, uG, uV} P M U h hU hM hL :=
  finiteCuspidalInducedEmbedding_of_projections P M U h hU hδ hM hL hlim hdetect
    (cuspidalJacquetProjectionTarget_of_splittings P M U h hU hM hL hsplit)

end Langlands.Aubert.General
