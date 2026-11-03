import Langlands.Representation.Smooth.LengthTwoEndpoints
import Langlands.Representation.Aubert.GeneralCorollaryTargets
import Langlands.Representation.Aubert.General.SupportCategory

/-! # Assembly of an actual rank-one Jacquet pattern from exact local data -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Aubert.General

open SmoothRep
open Langlands.Group

universe uI uG uV

private def choosePairSubtype {α β : Type*} {p : α → β → Prop}
    (h : ∃ a b, p a b) : {q : α × β // p q.1 q.2} := by
  apply Classical.choice
  obtain ⟨a, b, hab⟩ := h
  exact ⟨⟨(a, b), hab⟩⟩

section Elementary

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The predicate records a length-two series in either order. -/
theorem HasTwoConstituents.symm
    {A B C : SmoothRep.{0, uG, uV} ℂ G}
    (h : HasTwoConstituents A B C) : HasTwoConstituents A C B :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

end Elementary

section Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}

/-- The two actual formulations of Levi cuspidality differ only in the
equivalent descriptions of a zero smooth object. -/
theorem isCorollaryLeviCuspidal_iff_isLeviCuspidal
    (J : Finset ι) (hM : IsClosed (M J : Set G))
    (hJ : ∀ I : Finset J, IsSemidirectDecomposition
      ((P (leviIndex J I)).subgroupOf (M J))
      ((M (leviIndex J I)).subgroupOf (M J))
      ((U (leviIndex J I)).subgroupOf (M J)))
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M J)) :
    IsCorollaryLeviCuspidal P M U J hM hJ hU σ ↔
      IsLeviCuspidal P M U hU J hM hJ σ := by
  let := hM.locallyCompactSpace
  constructor
  · intro hc I
    exact (isZero_iff_subsingleton_carrier _).mp (hc I I.2)
  · intro hc I hI
    exact (isZero_iff_subsingleton_carrier _).mpr (hc ⟨I, hI⟩)

/-- Vanishing of the actual middle Jacquet module propagates to both
constituents of an actual length-two sequence, in either orientation. -/
theorem HasTwoConstituents.jacquet_isZero
    (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (U I))
    {E A B : SmoothRep.{0, uG, max uG uV} ℂ G}
    (hseries : HasTwoConstituents E A B) (K : Finset ι)
    (hzero : IsZero ((jacquetFunctor (h K) (hU K)).obj E)) :
    IsZero ((jacquetFunctor (h K) (hU K)).obj A) ∧
      IsZero ((jacquetFunctor (h K) (hU K)).obj B) := by
  rcases hseries.2.2 with ⟨f, g, hex⟩ | ⟨f, g, hex⟩
  · exact isZero_endpoints_of_shortExact
      (jacquetFunctor_map_isShortExact (h K) (hU K) (hUc K)
        (ofHom f) (ofHom g) hex) hzero
  · exact (isZero_endpoints_of_shortExact
      (jacquetFunctor_map_isShortExact (h K) (hU K) (hUc K)
        (ofHom f) (ofHom g) hex) hzero).symm

/-- The actual geometric short exact sequence at the supplied Levi. -/
def HasRankOneJacquetMiddleSequence
    {T : Subgroup G} (J : Finset ι)
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M J))
    (n : RelativeWeyl.normalizer T)
    (hself : ∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J) : Prop :=
  ∃ (f : ((conjugationFunctor (n : G)⁻¹
      (fun x => by simpa using hself x)).obj σ).representation.IntertwiningMap
      ((jacquetFunctor (h J) (hU J)).obj
        ((normalizedInductionFunctor (h J) (hU J)).obj σ)).representation)
    (g : ((jacquetFunctor (h J) (hU J)).obj
      ((normalizedInductionFunctor (h J) (hU J)).obj σ)).representation.IntertwiningMap
      σ.representation),
    IsShortExact f g

variable [Fintype ι]

/-- Actual local geometric and nonvanishing data determine the two
constituents in the order required by the rank-one Jacquet pattern. -/
theorem exists_rankOneJacquetPattern_of_exact_data
    (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (U I))
    {T : Subgroup G} (J : Finset ι)
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M J))
    (hσ : σ.IsIrreducible)
    (n : RelativeWeyl.normalizer T)
    (hself : ∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J)
    (A B : FiniteLengthObject.{0, uG, max uG uV} ℂ G)
    (hseries : HasTwoConstituents
      ((normalizedInductionFunctor (h J) (hU J)).obj σ) A.val B.val)
    (hA : Nontrivial ((jacquetFunctor (h J) (hU J)).obj A.val))
    (hB : Nontrivial ((jacquetFunctor (h J) (hU J)).obj B.val))
    (hgeometry : HasRankOneJacquetMiddleSequence (h := h) (hU := hU)
      J σ n hself)
    (hvanish : ∀ K : Finset ι, K ≠ Finset.univ → K ≠ J →
      IsZero ((jacquetFunctor (h K) (hU K)).obj
        ((normalizedInductionFunctor (h J) (hU J)).obj σ))) :
    ∃ ρplus ρminus : FiniteLengthObject.{0, uG, max uG uV} ℂ G,
      HasTwoConstituents ((normalizedInductionFunctor (h J) (hU J)).obj σ)
        ρplus.val ρminus.val ∧
      RankOneJacquetPattern P M U h hU T J σ ρplus.val ρminus.val n hself := by
  let τ := (conjugationFunctor (n : G)⁻¹
    (fun x => by simpa using hself x)).obj σ
  have hτ : τ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff σ.representation
      (conjugationEquiv (n : G)⁻¹ (fun x => by simpa using hself x))).mpr hσ
  obtain ⟨i, p, hgeom⟩ := hgeometry
  have hmatch :
      (Nonempty (((jacquetFunctor (h J) (hU J)).obj A.val) ≅ σ) ∧
        Nonempty (((jacquetFunctor (h J) (hU J)).obj B.val) ≅ τ)) ∨
      (Nonempty (((jacquetFunctor (h J) (hU J)).obj A.val) ≅ τ) ∧
        Nonempty (((jacquetFunctor (h J) (hU J)).obj B.val) ≅ σ)) := by
    rcases hseries.2.2 with ⟨f, g, hex⟩ | ⟨f, g, hex⟩
    · exact (endpoints_iso_of_shortExact_two_irreducibles
        (jacquetFunctor_map_isShortExact (h J) (hU J) (hUc J)
          (ofHom f) (ofHom g) hex) hgeom hτ hσ hA hB).symm
    · rcases endpoints_iso_of_shortExact_two_irreducibles
        (jacquetFunctor_map_isShortExact (h J) (hU J) (hUc J)
          (ofHom f) (ofHom g) hex) hgeom hτ hσ hB hA with
        ⟨hBt, hAs⟩ | ⟨hBs, hAt⟩
      · exact Or.inl ⟨hAs, hBt⟩
      · exact Or.inr ⟨hAt, hBs⟩
  have hz (K : Finset ι) (hK : K ≠ Finset.univ) (hKJ : K ≠ J) :=
    hseries.jacquet_isZero hUc K (hvanish K hK hKJ)
  rcases hmatch with ⟨hAs, hBt⟩ | ⟨hAt, hBs⟩
  · exact ⟨A, B, hseries, hAs, hBt, hz⟩
  · exact ⟨B, A, hseries.symm, hBs, hAt, fun K hK hKJ => (hz K hK hKJ).symm⟩

/-- Choose the actual finite-length constituent pair with the prescribed
Jacquet pattern from the explicit local exact data. -/
def rankOneJacquetConstituentsOfExactData
    (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (U I))
    {T : Subgroup G} (J : Finset ι)
    (σ : SmoothRep.{0, uG, max uG uV} ℂ (M J))
    (hσ : σ.IsIrreducible)
    (n : RelativeWeyl.normalizer T)
    (hself : ∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J)
    (A B : FiniteLengthObject.{0, uG, max uG uV} ℂ G)
    (hseries : HasTwoConstituents
      ((normalizedInductionFunctor (h J) (hU J)).obj σ) A.val B.val)
    (hA : Nontrivial ((jacquetFunctor (h J) (hU J)).obj A.val))
    (hB : Nontrivial ((jacquetFunctor (h J) (hU J)).obj B.val))
    (hgeometry : HasRankOneJacquetMiddleSequence (h := h) (hU := hU)
      J σ n hself)
    (hvanish : ∀ K : Finset ι, K ≠ Finset.univ → K ≠ J →
      IsZero ((jacquetFunctor (h K) (hU K)).obj
        ((normalizedInductionFunctor (h J) (hU J)).obj σ))) :
    {ρ : FiniteLengthObject.{0, uG, max uG uV} ℂ G ×
        FiniteLengthObject.{0, uG, max uG uV} ℂ G //
      HasTwoConstituents ((normalizedInductionFunctor (h J) (hU J)).obj σ)
        ρ.1.val ρ.2.val ∧
      RankOneJacquetPattern P M U h hU T J σ ρ.1.val ρ.2.val n hself} := by
  exact choosePairSubtype
    (exists_rankOneJacquetPattern_of_exact_data
      (P := P) (M := M) (U := U) (h := h) (hU := hU) (T := T)
      hUc J σ hσ n hself A B hseries hA hB hgeometry hvanish)

end Jacquet

end Langlands.Aubert.General
