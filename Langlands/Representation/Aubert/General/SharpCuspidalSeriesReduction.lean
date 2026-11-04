import Langlands.Representation.Aubert.General.SharpConsequenceStatements

/-!
# Cuspidal-series retention from irreducibility and support retention

For the generic standard families of `Langlands.Aubert.General`, the retention
of the cuspidal series by the terminal cokernel `E#` (`SharpCuspidalSeriesTarget`)
follows from the irreducibility of `E#` (`SharpIrreducibleTarget`), the retention
of the support category (`SharpSupportRetentionTarget`), reflexivity of the
association relation at the identity (`AssociationReflexive`), and transport of
irreducible inside-Levi cuspidal representations along the association
(`AssociationCuspidalTransport`). `E#` is its own irreducible subquotient, so the
support witness of `E# ∈ Alg({I})` is a cuspidal series witness for the
associated index set.
-/

open CategoryTheory

namespace Langlands.SmoothRep

universe uR uG uV

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- Every smooth representation is a subquotient of itself. -/
theorem isSubquotient_self (A : SmoothRep.{uR, uG, uV} R G) : IsSubquotient A A :=
  isSubquotient_iff_exists.mpr
    ⟨A, 𝟙 A, 𝟙 A, by rw [hom_id]; exact fun _ _ h => h, by
      rw [hom_id]; exact fun y => ⟨y, rfl⟩⟩

end Langlands.SmoothRep

namespace Langlands.Aubert.General

universe uI uG uV uW

section Association

variable {ι : Type uI} {G : Type uG} [Group G]

/-- The association relation contains every index set, associated to itself by
the identity. -/
def AssociationReflexive (IsAssociate : Finset ι → Finset ι → G → Prop) : Prop :=
  ∀ I, IsAssociate I I 1

end Association

section Transport

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)

/-- Transport of irreducible inside-Levi cuspidal representations with carriers in
`Type uW` along the association: for every association `IsAssociate I J n` with
`M J = n (M I) n⁻¹` (as the membership equivalence `hn`), the conjugate
`(conjugationFunctor n hn).obj σ` of an irreducible `σ` of `M I` cuspidal inside
`M I` is an irreducible representation of `M J` cuspidal inside `M J`. -/
def AssociationCuspidalTransport : Prop :=
  ∀ (I J : Finset ι) (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
    IsAssociate I J n → ∀ σ : SmoothRep.{0, uG, uW} ℂ (M I),
      σ.IsIrreducible → IsLeviCuspidal P M U hclosed I (hM I) (hL I) σ →
        ((conjugationFunctor n hn).obj σ).IsIrreducible ∧
          IsLeviCuspidal P M U hclosed J (hM J) (hL J) ((conjugationFunctor n hn).obj σ)

end Transport

section Reduction

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J)}
  {hclosed : ∀ J, IsClosed (U J : Set G)}
  {hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J)}
  {hP : Monotone P} {hU : Antitone U}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}

/-- Retention of the cuspidal series by `E#`, reduced to irreducibility of `E#`,
retention of `Alg({I})`, reflexivity of the association at the identity, and
transport of irreducible inside-Levi cuspidal representations, with carriers in
the carrier universe `Type (max uG uI uV)` of the target, along the
association. -/
theorem sharpCuspidalSeries_of_irreducible_supportRetention
    (hirr : SharpIrreducibleTarget.{uI, uG, uV} P M U h hclosed hδ hP hU hM hL)
    (hret : SharpSupportRetentionTarget.{uI, uG, uV} P M U h hclosed hδ hP hU hM hL
      IsAssociate)
    (hrefl : AssociationReflexive IsAssociate)
    (htrans : AssociationCuspidalTransport.{uI, uG, max uG (max uI uV)} P M U hclosed hM hL
      IsAssociate) :
    SharpCuspidalSeriesTarget.{uI, uG, uV} P M U h hclosed hδ hP hU hM hL IsAssociate := by
  intro I E hE
  have hsharp := hirr I E hE
  obtain ⟨J, n, hn, hIJ, σ, hσ, hc, hsub⟩ :=
    hret I E (hE.isInSupportCategory (hrefl I)) _ hsharp (SmoothRep.isSubquotient_self _)
  obtain ⟨hσ', hc'⟩ := htrans I J n hn hIJ σ hσ hc
  exact ⟨J, n, hIJ, hn, hsharp, _, hσ', hc', hsub⟩

end Reduction

end Langlands.Aubert.General
