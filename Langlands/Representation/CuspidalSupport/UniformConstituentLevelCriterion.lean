import Langlands.Representation.CuspidalSupport.UniformLevelDirectSum
import Langlands.Representation.Category.Subquotients

/-! # A countable-direct-sum criterion for uniform constituent detection -/

noncomputable section

namespace Langlands.SmoothRep

universe uG uV

/-- The uniform-level criterion isolates the two uses of a finite-type
characterization: centre admissibility of irreducible constituents, and
finite generation of centre-admissible countable sums of such constituents. -/
def UniformConstituentLevelCriterionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] [FirstCountableTopology G]
    (A : SmoothRep.{0, uG, uV} ℂ G),
    (∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → IsSubquotient D A → D.IsCenterAdmissible) →
    (∀ D : ℕ → SmoothRep.{0, uG, uV} ℂ G,
      (∀ n, (D n).IsIrreducible ∧ IsSubquotient (D n) A) →
      (directSum D).IsCenterAdmissible →
      Module.Finite (MonoidAlgebra ℂ G) (directSum D).representation.asModule) →
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      ∀ D : SmoothRep.{0, uG, uV} ℂ G,
        D.IsIrreducible → IsSubquotient D A →
        ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0

/-- Failure of uniform detection produces a centre-admissible countable
sum of nonzero constituents which cannot be finitely generated. -/
theorem uniformConstituentLevelCriterion :
    UniformConstituentLevelCriterionStatement.{uG, uV} := by
  classical
  intro G _ _ _ _ _ A hcenter hfinite
  by_contra hn
  push Not at hn
  obtain ⟨K, hK, hanti, hbase⟩ := Langlands.exists_antitone_compactOpen_basis G
  choose D hD hDA hzero using fun n : ℕ => hn (K n) (hK n)
  have hlocal : ∀ L : OpenSubgroup G, IsCompact (L : Set G) →
      ∃ T : Finset ℕ, ∀ n ∉ T, ∀ v : D n,
        v ∈ fixedVectors (D n).representation L.toSubgroup → v = 0 := by
    intro L _
    obtain ⟨m, hm⟩ := hbase (L : Set G) L.mem_nhds_one
    refine ⟨Finset.range m, ?_⟩
    intro n hn v hv
    have hmn : m ≤ n := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
    apply hzero n v
    intro g
    exact hv ⟨g.val, hm (hanti hmn g.property)⟩
  have hadm : (directSum D).IsCenterAdmissible :=
    locallyFiniteCenterAdmissibleDirectSum D
      (fun n => hcenter (D n) (hD n) (hDA n)) hlocal
  have hnonzero (n : ℕ) : Nontrivial (D n) := by
    by_contra h
    have : Subsingleton (D n) := not_nontrivial_iff_subsingleton.mp h
    apply (hD n).bot_ne_top
    apply top_unique
    intro v _
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _
  exact not_finite_directSum_of_infinite D hnonzero
    (hfinite D (fun n => ⟨hD n, hDA n⟩) hadm)

end Langlands.SmoothRep
