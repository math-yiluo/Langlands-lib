import Langlands.Representation.Aubert.General.InductionCompactVisibility
import Langlands.Representation.Category.FixedVectorConstituent

/-! # Finite compact support under actual normalized induction

Finite support at every compact open level of the inducing group passes to
actual normalized induction through its finite detecting family.
-/

noncomputable section

namespace Langlands.SmoothRep

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G] {ι : Type uI}

/-- Every compact open fixed-vector module sees only finitely many members of
the supplied family of actual smooth representations. -/
def CompactFiniteFixedVectorSupport (A : ι → SmoothRep.{0, uG, uV} ℂ G) : Prop :=
  ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
    Set.Finite {i | Nontrivial (fixedVectors (A i).representation K.toSubgroup)}

/-- Finite compact-level visibility of irreducible classes also controls
arbitrary objects all of whose irreducible subquotients have their given label. -/
theorem compactFiniteFixedVectorSupport_of_finite_constituent_classes
    (A : ι → SmoothRep.{0, uG, uV} ℂ G)
    (Q : SmoothRep.{0, uG, uV} ℂ G → Prop)
    (c : ∀ D : SmoothRep.{0, uG, uV} ℂ G, D.IsIrreducible → ι)
    (hblocks : ∀ i D hD, IsSubquotient D (A i) → Q D ∧ c D hD = i)
    (hfinite : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      Set.Finite {i | ∃ D hD, Q D ∧ c D hD = i ∧
        Nontrivial (fixedVectors D.representation K.toSubgroup)}) :
    CompactFiniteFixedVectorSupport A :=
  fun K hK => finite_fixedVectorSupport_of_finite_constituent_classes
    A K.toSubgroup Q c hblocks (hfinite K hK)

end Langlands.SmoothRep

namespace Langlands.Aubert.General

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} {ι : Type uI}

/-- Only finitely many induced objects have nonzero fixed vectors under a
given open subgroup if the inducing family has finite compact-level support. -/
theorem finite_fixedVectorSupport_normalizedInduction
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hM : IsClosed (M : Set G)) [CompactSpace (Induction.LeftQuotient P)]
    (A : ι → SmoothRep.{0, uG, uV} ℂ M)
    (hA : SmoothRep.CompactFiniteFixedVectorSupport A) (K : OpenSubgroup G) :
    Set.Finite {i | Nontrivial (fixedVectors
      ((normalizedInductionFunctor h hU).obj (A i)).representation K.toSubgroup)} := by
  obtain ⟨t, L, hLc, hvisible⟩ := finiteInductionFixedVectorVisibility.{uG, uV} h hU hM K
  have hfinite : Set.Finite
      (⋃ x : t, {i | Nontrivial (fixedVectors (A i).representation (L x).toSubgroup)}) :=
    Set.finite_iUnion fun x => hA (L x) (hLc x)
  exact hfinite.subset fun i hi => Set.mem_iUnion.mpr (hvisible (A i) hi)

/-- Actual normalized induction preserves compact-level finiteness of the
nonzero fixed-vector support of an arbitrary indexed family. -/
theorem normalizedInduction_compactFiniteFixedVectorSupport
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hM : IsClosed (M : Set G)) [CompactSpace (Induction.LeftQuotient P)]
    (A : ι → SmoothRep.{0, uG, uV} ℂ M)
    (hA : SmoothRep.CompactFiniteFixedVectorSupport A) :
    SmoothRep.CompactFiniteFixedVectorSupport
      (fun i => (normalizedInductionFunctor h hU).obj (A i)) :=
  fun K _ => finite_fixedVectorSupport_normalizedInduction h hU hM A hA K

end Langlands.Aubert.General
