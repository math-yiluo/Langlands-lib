import Langlands.Representation.Aubert.General.RationalCuspidalJacquetFactorTarget
import Langlands.Representation.Filtration.ActualGradedExtraction

/-! # Cuspidal-factor extraction from supplied actual graded pieces -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

private theorem iso_of_irreducible_subquotient
    {H : Type uG} [Group H] [TopologicalSpace H]
    {D A : SmoothRep.{0, uG, max uG uV} ℂ H}
    (hD : D.IsIrreducible) (hA : A.IsIrreducible)
    (hDA : SmoothRep.IsSubquotient D A) : Nonempty (D ≅ A) := by
  let := hD
  let := hA
  let : Nontrivial D :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) D.representation.asModule
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
  have hi0 : SmoothRep.hom i ≠ 0 := by
    intro hz
    obtain ⟨d, hd⟩ := exists_ne (0 : D)
    obtain ⟨c, rfl⟩ := hq d
    have hc : c = 0 := hi (by rw [hz]; rfl)
    exact hd (by rw [hc]; exact (SmoothRep.hom q).toLinearMap.map_zero)
  have his : Function.Surjective (SmoothRep.hom i) :=
    (Representation.IsIrreducible.surjective_or_eq_zero
      (SmoothRep.hom i)).resolve_right hi0
  let e : C ≅ A := SmoothRep.mkIso ((SmoothRep.hom i).ofBijective ⟨hi, his⟩)
  let f : A ⟶ D := e.inv ≫ q
  have hfs : Function.Surjective (SmoothRep.hom f) :=
    hq.comp (SmoothRep.hom_hom_surjective e.symm)
  have hf0 : SmoothRep.hom f ≠ 0 := by
    intro hz
    obtain ⟨d, hd⟩ := exists_ne (0 : D)
    obtain ⟨a, rfl⟩ := hfs d
    exact hd (by rw [hz]; rfl)
  exact ⟨(SmoothRep.mkIso ((SmoothRep.hom f).ofBijective
    ((Representation.IsIrreducible.bijective_or_eq_zero
      (SmoothRep.hom f)).resolve_right hf0))).symm⟩

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {ι : Type uI}

omit [LocallyCompactSpace G] in
/-- A supplied finite filtration extracts a single associated conjugate when
each actual grade either excludes the chosen constituent or is such a
conjugate. The representative and its dependent membership witness are
preserved in the resulting actual isomorphism. -/
theorem exists_conjugation_iso_of_finiteFiltration
    {M : Finset ι → Subgroup G}
    {IsAssociate : Finset ι → Finset ι → G → Prop}
    {I J : Finset ι}
    {σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)}
    {τ A : SmoothRep.{0, uG, max uG uV} ℂ (M J)}
    {r : ℕ} (s : ObjectRepFiltration A.obj r)
    (hσ : σ.IsIrreducible) (hτ : τ.IsIrreducible)
    (hτA : SmoothRep.IsSubquotient τ A)
    (hgrades : ∀ j : Fin r,
      (¬ SmoothRep.IsSubquotient τ (s.smoothGradedObject j)) ∨
      ∃ (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
        IsAssociate I J n ∧
        Nonempty (s.smoothGradedObject j ≅ (conjugationFunctor n hn).obj σ)) :
    ∃ (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n ∧ Nonempty (τ ≅ (conjugationFunctor n hn).obj σ) := by
  obtain ⟨j, hτj⟩ := s.exists_smoothGradedObject_subquotient hτ hτA
  rcases hgrades j with hno | ⟨n, hn, hassoc, ⟨e⟩⟩
  · exact (hno hτj).elim
  · have hσn : ((conjugationFunctor n hn).obj σ).IsIrreducible :=
      (Langlands.isIrreducible_comp_continuousMulEquiv_iff
        σ.representation (conjugationEquiv n hn)).mpr hσ
    exact ⟨n, hn, hassoc,
      iso_of_irreducible_subquotient hτ hσn (hτj.of_iso_right e)⟩

/-- The explicit graded-piece input needed for the cuspidal extraction
argument. Each grade either has no irreducible inside-Levi cuspidal
subquotient, or is actually isomorphic to a conjugate of the inducing datum.
This definition does not supply the filtration or prove the exclusion. -/
def CuspidalJacquetGradedPieces
    (P M U : Finset ι → Subgroup G)
    (hU : ∀ I, IsClosed (U I : Set G))
    (hM : ∀ I, IsClosed (M I : Set G))
    (hL : ∀ (I : Finset ι) (K : Finset I),
      IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
        ((M (leviIndex I K)).subgroupOf (M I))
        ((U (leviIndex I K)).subgroupOf (M I)))
    (IsAssociate : Finset ι → Finset ι → G → Prop)
    (I J : Finset ι) (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I))
    {A : SmoothRep.{0, uG, max uG uV} ℂ (M J)}
    {r : ℕ} (s : ObjectRepFiltration A.obj r) : Prop :=
  ∀ j : Fin r,
    (∀ τ : SmoothRep.{0, uG, max uG uV} ℂ (M J),
      τ.IsIrreducible → IsLeviCuspidal P M U hU J (hM J) (hL J) τ →
      ¬ SmoothRep.IsSubquotient τ (s.smoothGradedObject j)) ∨
    ∃ (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n ∧
      Nonempty (s.smoothGradedObject j ≅ (conjugationFunctor n hn).obj σ)

/-- Extract an actual cuspidal conjugate from the supplied actual finite
filtration and graded-piece condition, without finite length of the ambient
representation or simplicity of the excluded grades. -/
theorem cuspidalJacquetFactor_of_finiteFiltration
    {P M U : Finset ι → Subgroup G}
    {hU : ∀ I, IsClosed (U I : Set G)}
    {hM : ∀ I, IsClosed (M I : Set G)}
    {hL : ∀ (I : Finset ι) (K : Finset I),
      IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
        ((M (leviIndex I K)).subgroupOf (M I))
        ((U (leviIndex I K)).subgroupOf (M I))}
    {IsAssociate : Finset ι → Finset ι → G → Prop}
    {I J : Finset ι}
    {σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)}
    {τ A : SmoothRep.{0, uG, max uG uV} ℂ (M J)}
    {r : ℕ} (s : ObjectRepFiltration A.obj r)
    (hσ : σ.IsIrreducible) (hτ : τ.IsIrreducible)
    (hcτ : IsLeviCuspidal P M U hU J (hM J) (hL J) τ)
    (hτA : SmoothRep.IsSubquotient τ A)
    (hgrades : CuspidalJacquetGradedPieces P M U hU hM hL IsAssociate I J σ s) :
    ∃ (n : G) (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n ∧ Nonempty (τ ≅ (conjugationFunctor n hn).obj σ) := by
  apply exists_conjugation_iso_of_finiteFiltration s hσ hτ hτA
  intro j
  rcases hgrades j with hno | hconj
  · exact Or.inl (hno τ hτ hcτ)
  · exact Or.inr hconj

end Langlands.Aubert.General
