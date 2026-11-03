import Langlands.Representation.Aubert.General.GroupTransport
import Langlands.Representation.Aubert.General.SupportCategory

/-! # Cuspidality under transport of the actual Jacquet test families -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV uK uK' uI

section Jacquet

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [NonarchimedeanGroup G] [NonarchimedeanGroup H]
  {P M U : Subgroup G} {P' M' U' : Subgroup H}

/-- Vanishing of the actual normalized Jacquet module is unchanged under a
continuous group equivalence that matches its Levi and unipotent subgroups. -/
theorem jacquet_subsingleton_pullback_iff
    (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U')
    (e : H ≃ₜ* G)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    Subsingleton ((jacquetFunctor h' hU').obj ((SmoothRep.pullbackFunctor e).obj A)) ↔
      Subsingleton ((jacquetFunctor h hU).obj A) := by
  let t := (SmoothRep.equivOfIso
    (GroupTransport.jacquetIsoApp h h' e hMM' hUU' hU hU' A)).toLinearEquiv
  constructor
  · intro hs
    exact ⟨fun a b => t.injective (@Subsingleton.elim _ hs (t a) (t b))⟩
  · intro hs
    exact ⟨fun a b => t.symm.injective (@Subsingleton.elim _ hs (t.symm a) (t.symm b))⟩

end Jacquet

section Families

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [NonarchimedeanGroup G] [NonarchimedeanGroup H]
  {κ : Type uK} {κ' : Type uK'}
  {P M U : κ → Subgroup G} {P' M' U' : κ' → Subgroup H}
  {h : ∀ k, IsSemidirectDecomposition (P k) (M k) (U k)}
  {h' : ∀ k, IsSemidirectDecomposition (P' k) (M' k) (U' k)}
  {hU : ∀ k, IsClosed (U k : Set G)}
  {hU' : ∀ k, IsClosed (U' k : Set H)}

/-- Pullback preserves cuspidality when every target test triple matches one
source test triple. No surjectivity of the test-index map is needed. -/
theorem IsCuspidalFor.pullback (e : H ≃ₜ* G) (f : κ' → κ)
    (hMM' : ∀ k x, x ∈ M' k ↔ e x ∈ M (f k))
    (hUU' : ∀ k x, x ∈ U' k ↔ e x ∈ U (f k))
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (hc : IsCuspidalFor P M U h hU A) :
    IsCuspidalFor P' M' U' h' hU' ((SmoothRep.pullbackFunctor e).obj A) :=
  fun k => (jacquet_subsingleton_pullback_iff
    (h (f k)) (h' k) e (hMM' k) (hUU' k) (hU (f k)) (hU' k) A).mpr (hc (f k))

/-- A surjective matching of test triples makes cuspidality equivalent under
the same continuous group equivalence. -/
theorem isCuspidalFor_pullback_iff (e : H ≃ₜ* G) (f : κ' → κ)
    (hf : Function.Surjective f)
    (hMM' : ∀ k x, x ∈ M' k ↔ e x ∈ M (f k))
    (hUU' : ∀ k x, x ∈ U' k ↔ e x ∈ U (f k))
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    IsCuspidalFor P' M' U' h' hU' ((SmoothRep.pullbackFunctor e).obj A) ↔
      IsCuspidalFor P M U h hU A := by
  constructor
  · intro hc k
    obtain ⟨k', rfl⟩ := hf k
    exact (jacquet_subsingleton_pullback_iff
      (h (f k')) (h' k') e (hMM' k') (hUU' k') (hU (f k')) (hU' k') A).mp (hc k')
  · exact fun hc => hc.pullback e f hMM' hUU'

end Families

section Isomorphism

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {κ : Type uK} {P M U : κ → Subgroup G}
  {h : ∀ k, IsSemidirectDecomposition (P k) (M k) (U k)}
  {hU : ∀ k, IsClosed (U k : Set G)}

/-- Cuspidality for a fixed family is preserved by an actual smooth
equivariant isomorphism. -/
theorem IsCuspidalFor.of_iso {A B : SmoothRep.{0, uG, uV} ℂ G}
    (hc : IsCuspidalFor P M U h hU A) (e : B ≅ A) :
    IsCuspidalFor P M U h hU B := by
  intro k
  let t := (SmoothRep.equivOfIso ((jacquetFunctor (h k) (hU k)).mapIso e)).toLinearEquiv
  exact ⟨fun a b => t.injective (@Subsingleton.elim _ (hc k) (t a) (t b))⟩

end Isomorphism

section Levi

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {ι : Type uI} {P M U : Finset ι → Subgroup G}
  (hU : ∀ I, IsClosed (U I : Set G))
  {I J : Finset ι}
  (hMI : IsClosed (M I : Set G)) (hMJ : IsClosed (M J : Set G))
  (hI : ∀ K : Finset I,
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
  (hJ : ∀ K : Finset J,
    IsSemidirectDecomposition ((P (leviIndex J K)).subgroupOf (M J))
      ((M (leviIndex J K)).subgroupOf (M J)) ((U (leviIndex J K)).subgroupOf (M J)))

/-- Actual inverse-conjugation transport preserves the precise inside-Levi
cuspidality predicate when it matches all proper standard Levi and radical
tests through the given bijection of proper subsets. -/
theorem isLeviCuspidal_conjugation_iff
    (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I)
    (f : {K : Finset J // K ≠ Finset.univ} ≃ {K : Finset I // K ≠ Finset.univ})
    (hML : ∀ K x, x ∈ M (leviIndex J K.val) ↔
      n⁻¹ * x * n ∈ M (leviIndex I (f K).val))
    (hUL : ∀ K x, x ∈ U (leviIndex J K.val) ↔
      n⁻¹ * x * n ∈ U (leviIndex I (f K).val))
    (σ : SmoothRep.{0, uG, uV} ℂ (M I)) :
    IsLeviCuspidal P M U hU J hMJ hJ ((conjugationFunctor n hn).obj σ) ↔
      IsLeviCuspidal P M U hU I hMI hI σ := by
  let := hMI.locallyCompactSpace
  let := hMJ.locallyCompactSpace
  exact isCuspidalFor_pullback_iff (conjugationEquiv n hn) f f.surjective
    (fun K x => hML K (x : G)) (fun K x => hUL K (x : G)) σ

/-- Transport an actual irreducible cuspidal datum by the specified inverse
conjugation, retaining its smooth carrier and the same conjugating element. -/
def conjugateLeviCuspidalDatum
    (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I)
    (f : {K : Finset J // K ≠ Finset.univ} ≃ {K : Finset I // K ≠ Finset.univ})
    (hML : ∀ K x, x ∈ M (leviIndex J K.val) ↔
      n⁻¹ * x * n ∈ M (leviIndex I (f K).val))
    (hUL : ∀ K x, x ∈ U (leviIndex J K.val) ↔
      n⁻¹ * x * n ∈ U (leviIndex I (f K).val))
    (σ : {σ : SmoothRep.{0, uG, uV} ℂ (M I) //
      σ.IsIrreducible ∧ IsLeviCuspidal P M U hU I hMI hI σ}) :
    {τ : SmoothRep.{0, uG, uV} ℂ (M J) //
      τ.IsIrreducible ∧ IsLeviCuspidal P M U hU J hMJ hJ τ} :=
  ⟨(conjugationFunctor n hn).obj σ.val,
    (isIrreducible_comp_continuousMulEquiv_iff σ.val.representation
      (conjugationEquiv n hn)).mpr σ.property.1,
    (isLeviCuspidal_conjugation_iff hU hMI hMJ hI hJ n hn f hML hUL σ.val).mpr
      σ.property.2⟩

/-- Actual isomorphisms preserve the precise inside-Levi cuspidality
predicate. -/
theorem IsLeviCuspidal.of_iso {σ τ : SmoothRep.{0, uG, uV} ℂ (M I)}
    (hc : IsLeviCuspidal P M U hU I hMI hI σ) (e : τ ≅ σ) :
    IsLeviCuspidal P M U hU I hMI hI τ := by
  let := hMI.locallyCompactSpace
  exact IsCuspidalFor.of_iso hc e

end Levi

end Langlands.Aubert.General
