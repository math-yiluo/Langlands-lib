import Langlands.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.Representation.Filtration.LengthTwoMatching
import Langlands.Representation.CuspidalSupport.LeviAssociation
import Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.Representation.CuspidalSupport.AssociationForwardStatement
import Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
import Langlands.Representation.CuspidalSupport.AssociatedProof
import Langlands.Representation.CuspidalSupport.AssociationForwardHomProof

/-!
# Matching composition factors for associated two-block cuspidal inductions

The summed Jacquet length over the shapes associated to the source block shape
is a strictly monotone count, bounded by two, on the subrepresentations of both
normalized inductions. A subrepresentation of count one with nonzero maps on
the Jacquet side to both inducing representations forces those inducing
representations, and hence the inductions, to be equivalent. The length-two
matching theorem then gives the same composition factors.
-/

noncomputable section

open Representation

namespace Langlands.CuspidalSupport.JacquetLength

open GeneralLinear

universe uF uU uV uW

section Schur

variable {k : Type*} [Field k] {G : Type*} [Monoid G]
  {U : Type*} {V : Type*} {W : Type*}
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- A nonzero intertwiner has a nonzero source. -/
theorem nontrivial_of_ne_zero {ρ : Representation k G U} {σ : Representation k G V}
    (g : ρ.IntertwiningMap σ) (hg : g ≠ 0) : Nontrivial U := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply hg
  ext x
  rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- An intertwiner with a nonzero value is nonzero. -/
theorem ne_zero_of_apply_ne_zero {ρ : Representation k G U} {σ : Representation k G V}
    {g : ρ.IntertwiningMap σ} (x : U) (hx : g x ≠ 0) : g ≠ 0 := by
  rintro rfl
  exact hx rfl

/-- Two nonzero intertwiners out of one irreducible representation into two
irreducible representations make those two equivalent. -/
theorem nonempty_equiv_of_ne_zero {ρ : Representation k G U} {σ : Representation k G V}
    {τ : Representation k G W} (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hτ : τ.IsIrreducible) (g : ρ.IntertwiningMap σ) (hg : g ≠ 0)
    (g' : ρ.IntertwiningMap τ) (hg' : g' ≠ 0) : Nonempty (σ.Equiv τ) := by
  have := hρ
  have := hσ
  have := hτ
  have h₁ := (IsIrreducible.bijective_or_eq_zero g).resolve_right hg
  have h₂ := (IsIrreducible.bijective_or_eq_zero g').resolve_right hg'
  exact ⟨(g.ofBijective h₁).symm.trans (g'.ofBijective h₂)⟩

end Schur

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- **Detection.** Let `X` have summed Jacquet length one over `I`, and let
`B, C ∈ I`. Nonzero maps from the Jacquet modules of `X` along `B` and `C` to
irreducible representations `σ` and `τ` force `B = C` and an actual
equivalence of the normalized inductions of `σ` and `τ`. -/
theorem nonempty_equiv_of_jacquetLength_eq_one (I : Finset (BlockShape n))
    {U : Type uU} {V : Type uV} {W : Type uW}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {X : Representation ℂ (GeneralLinear n F.Carrier) U}
    (hX : jacquetLength T I X = 1) {B C : BlockShape n} (hB : B ∈ I) (hC : C ∈ I)
    {σ : Representation ℂ (B.Levi F.Carrier) V} {τ : Representation ℂ (C.Levi F.Carrier) W}
    (hσ : σ.IsIrreducible) (hτ : τ.IsIrreducible)
    (g : (T.normalizedJacquet B X).IntertwiningMap σ) (hg : g ≠ 0)
    (g' : (T.normalizedJacquet C X).IntertwiningMap τ) (hg' : g' ≠ 0) :
    Nonempty ((T.normalizedParabolicInduced B σ).Equiv (T.normalizedParabolicInduced C τ)) := by
  have hpos : ∀ D ∈ I, Nontrivial (D.JacquetModule X) →
      (1 : ℕ∞) ≤ repLength (T.normalizedJacquet D X) := fun D _ h =>
    Order.one_le_iff_pos.mpr (repLength_pos_iff.mpr h)
  have hBpos := hpos B hB (nontrivial_of_ne_zero g hg)
  have hCpos := hpos C hC (nontrivial_of_ne_zero g' hg')
  have hBC : B = C := by
    classical
    by_contra hne
    have hsub : ({B, C} : Finset (BlockShape n)) ⊆ I := Finset.insert_subset hB
      (Finset.singleton_subset_iff.mpr hC)
    have hle := Finset.sum_le_sum_of_subset
      (f := fun D => repLength (T.normalizedJacquet D X)) hsub
    rw [Finset.sum_pair hne] at hle
    have h2 : (1 : ℕ∞) + 1 ≤ 1 := by
      calc (1 : ℕ∞) + 1 ≤ _ := add_le_add hBpos hCpos
        _ ≤ jacquetLength T I X := hle
        _ = 1 := hX
    exact absurd h2 (by norm_num)
  subst hBC
  have hlen : repLength (T.normalizedJacquet B X) = 1 := by
    refine le_antisymm ?_ hBpos
    calc repLength (T.normalizedJacquet B X) ≤ jacquetLength T I X :=
          Finset.single_le_sum (f := fun D => repLength (T.normalizedJacquet D X))
            (fun _ _ => zero_le) hB
      _ = 1 := hX
  obtain ⟨e⟩ := nonempty_equiv_of_ne_zero (repLength_eq_one_iff.mp hlen) hσ hτ g hg g' hg'
  exact ⟨T.normalizedParabolicInducedEquiv B e⟩

/-- **Count-one detection on a subrepresentation.** Inside the normalized
induction of `σ` from `B`, a subrepresentation `S` of count one on which an
intertwiner `A` to the normalized induction of `τ` from `C` does not vanish
forces the two inductions to be equivalent, when `B, C ∈ I`. -/
theorem nonempty_equiv_of_count_eq_one (I : Finset (BlockShape n))
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {B C : BlockShape n} (hB : B ∈ I) (hC : C ∈ I)
    {σ : Representation ℂ (B.Levi F.Carrier) V} {τ : Representation ℂ (C.Levi F.Carrier) W}
    (hσ : σ.IsIrreducible) (hτ : τ.IsIrreducible)
    (A : (T.normalizedParabolicInduced B σ).IntertwiningMap (T.normalizedParabolicInduced C τ))
    (S : Subrepresentation (T.normalizedParabolicInduced B σ))
    (hS : count T I S = 1) (hAS : ∃ v ∈ S, A v ≠ 0) :
    Nonempty ((T.normalizedParabolicInduced B σ).Equiv (T.normalizedParabolicInduced C τ)) := by
  obtain ⟨v, hv, hAv⟩ := hAS
  have hJ : jacquetLength T I S.toRepresentation = 1 := by
    have h := (ENat.toNat_eq_iff one_ne_zero).mp hS
    rwa [Nat.cast_one] at h
  have hv0 : subtypeMap S ⟨v, hv⟩ ≠ 0 := fun h => hAv (by
    have h' : v = 0 := h
    rw [h', map_zero])
  obtain ⟨g, hg⟩ := exists_ne_zero_normalizedJacquet_hom T B (subtypeMap S)
    (ne_zero_of_apply_ne_zero _ hv0)
  obtain ⟨g', hg'⟩ := exists_ne_zero_normalizedJacquet_hom T C (A.comp (subtypeMap S))
    (ne_zero_of_apply_ne_zero (g := A.comp (subtypeMap S)) ⟨v, hv⟩ hAv)
  exact nonempty_equiv_of_jacquetLength_eq_one T I hJ hB hC hσ hτ g hg g' hg'

/-- **Two-block matching from the analytic inputs.** For associated block
shapes `B` and `C` with `B.length = 2`, irreducible quasicuspidal data `σ` on
`B` and `τ` on `C`, and nonzero intertwiners in both directions between their
normalized inductions, the two inductions have the same composition factors
with multiplicities, provided the two Jacquet statements for quasicuspidal
induction hold at rank `n` in both carrier universes. -/
theorem haveSameJordanHolderFactors_of_hypotheses
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (hnon' : NonassociatedJacquetSubquotientsTheorem.{uF, uW} F T n)
    (hfilt : AssociatedJacquetFiltrationTheorem.{uF, uV} F T n)
    (hfilt' : AssociatedJacquetFiltrationTheorem.{uF, uW} F T n)
    (B C : BlockShape n) (hassoc : LevisAssociated (F := F.Carrier) B C)
    (hB2 : B.length = 2) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      σ.IsIrreducible → IsLeviQuasicuspidal B σ.representation →
      τ.IsIrreducible → IsLeviQuasicuspidal C τ.representation →
      ∀ (A : (T.normalizedParabolicInduced B σ.representation).IntertwiningMap
          (T.normalizedParabolicInduced C τ.representation))
        (A' : (T.normalizedParabolicInduced C τ.representation).IntertwiningMap
          (T.normalizedParabolicInduced B σ.representation)), A ≠ 0 → A' ≠ 0 →
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced B σ.representation))
        (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  let := T.topology
  intro σ τ hσ hσq hτ hτq A A' hA0 hA'0
  have hmin := minimalNonzeroJacquet.{uF, max uF uV}
  have hmin' := minimalNonzeroJacquet.{uF, max uF uW}
  have hcount := totalConjugatingCount.{uF}
  let I := associatedShapes F.Carrier B
  have hBI : B ∈ I := mem_associatedShapes.mpr (LevisAssociated.refl B)
  have hCI : C ∈ I := mem_associatedShapes.mpr hassoc
  have hI₁ : ∀ D, LevisAssociated (F := F.Carrier) B D → D ∈ I :=
    fun D h => mem_associatedShapes.mpr h
  have hI₂ : ∀ D ∈ I, LevisAssociated (F := F.Carrier) B D :=
    fun D h => mem_associatedShapes.mp h
  have hI₃ : ∀ D, LevisAssociated (F := F.Carrier) C D → D ∈ I :=
    fun D h => mem_associatedShapes.mpr (hassoc.trans h)
  have hI₄ : ∀ D ∈ I, LevisAssociated (F := F.Carrier) C D :=
    fun D h => hassoc.symm.trans (mem_associatedShapes.mp h)
  have hC2 : C.length = 2 := hassoc.length_eq ▸ hB2
  have hπ : IsSmooth (T.normalizedParabolicInduced B σ.representation) :=
    T.isSmooth_normalizedParabolicInduced B σ.representation
  have hπ' : IsSmooth (T.normalizedParabolicInduced C τ.representation) :=
    T.isSmooth_normalizedParabolicInduced C τ.representation
  have hle : jacquetLength T I (T.normalizedParabolicInduced B σ.representation) ≤ (2 : ℕ) := by
    have h := jacquetLength_induced_le T hfilt hcount B I hI₂ σ hσ hσq
    have h2 : B.length.factorial = 2 := by rw [hB2]; rfl
    rw [h2] at h
    exact h
  have hle' : jacquetLength T I (T.normalizedParabolicInduced C τ.representation) ≤ (2 : ℕ) := by
    have h := jacquetLength_induced_le T hfilt' hcount C I hI₄ τ hτ hτq
    have h2 : C.length.factorial = 2 := by rw [hC2]; rfl
    rw [h2] at h
    exact h
  have hfin := ne_top_of_le_ne_top (ENat.natCast_ne_top 2) hle
  have hfin' := ne_top_of_le_ne_top (ENat.natCast_ne_top 2) hle'
  have hμ := count_strictMono T I hπ hfin
    (one_le_jacquetLength_stepQuotient T hmin hnon B I hI₁ σ hσq)
  have hν := count_strictMono T I hπ' hfin'
    (one_le_jacquetLength_stepQuotient T hmin' hnon' C I hI₃ τ hτq)
  have hμ2 : count T I (⊤ : Subrepresentation (T.normalizedParabolicInduced B σ.representation))
      ≤ 2 := by
    rw [count_top]
    exact ENat.toNat_le_of_le_natCast hle
  have hν2 : count T I (⊤ : Subrepresentation (T.normalizedParabolicInduced C τ.representation))
      ≤ 2 := by
    rw [count_top]
    exact ENat.toNat_le_of_le_natCast hle'
  refine LengthTwo.haveSameJordanHolderFactors_of_count_le_two (count T I) (count T I)
    hμ hν (count_bot T I) (count_bot T I) hμ2 hν2 A A' hA0 hA'0
    (count_top_eq_ker_add_range T I hπ hfin A) (count_top_eq_ker_add_range T I hπ' hfin' A')
    ?_ ?_
  · intro S hS hAS
    exact nonempty_equiv_of_count_eq_one T I hBI hCI hσ hτ A S hS hAS
  · intro S hS hAS
    obtain ⟨e⟩ := nonempty_equiv_of_count_eq_one T I hCI hBI hτ hσ A' S hS hAS
    exact ⟨e.symm⟩

end Langlands.CuspidalSupport.JacquetLength

namespace Langlands.CuspidalSupport

open GeneralLinear JacquetLength

universe uF uV uW

/-- **BZ77 §2.16(1), two-block case, from the remaining inputs.** The
two-block factor matching for associated irreducible cuspidal data holds,
provided the nonassociated vanishing and associated filtration statements for
Jacquet modules of quasicuspidal induction hold in positive rank for both
carrier universes, and associated irreducible cuspidal data give nonzero
intertwiners in both directions. -/
theorem twoBlockAssociatedCuspidalInductionFactors_of_hypotheses
    (hnon : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
      (n : ℕ), 0 < n → NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (hnon' : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
      (n : ℕ), 0 < n → NonassociatedJacquetSubquotientsTheorem.{uF, uW} F T n)
    (hfilt : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
      (n : ℕ), 0 < n → AssociatedJacquetFiltrationTheorem.{uF, uV} F T n)
    (hfilt' : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
      (n : ℕ), 0 < n → AssociatedJacquetFiltrationTheorem.{uF, uW} F T n)
    (hHom : AssociatedCuspidalInductionHomTheorem.{uF, uV, uW})
    (hHom' : AssociatedCuspidalInductionHomTheorem.{uF, uW, uV}) :
    TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW} := by
  intro p _ F T n hn
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro B C σ τ hB2 hσ hσc hτ hτc hassoc
  have hL : LevisAssociated (F := F.Carrier) B C := by
    obtain ⟨w, hw, _⟩ := hassoc
    exact ⟨⟨w, hw⟩⟩
  obtain ⟨A, hA⟩ := hHom p F T n hn B C σ τ hσ hσc hτ hτc hassoc
  obtain ⟨A', hA'⟩ := hHom' p F T n hn C B τ σ hτ hτc hσ hσc hassoc.symm
  exact haveSameJordanHolderFactors_of_hypotheses T (hnon p F T n hn) (hnon' p F T n hn)
    (hfilt p F T n hn) (hfilt' p F T n hn) B C hL hB2 σ τ hσ hσc.2 hτ hτc.2 A A' hA hA'

/-- **BZ77 §2.16(1), two-block case.** For associated irreducible cuspidal
data on a two-block Levi, the normalized inductions have the same
Jordan–Hölder factors with multiplicities. -/
theorem twoBlockAssociatedCuspidalInductionFactors :
    TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW} :=
  twoBlockAssociatedCuspidalInductionFactors_of_hypotheses
    (fun _ _ F T n _ => nonassociatedJacquetSubquotients F T n)
    (fun _ _ F T n _ => nonassociatedJacquetSubquotients F T n)
    (fun _ _ F T n _ => associatedJacquetFiltration F T n)
    (fun _ _ F T n _ => associatedJacquetFiltration F T n)
    associatedCuspidalInductionHomTheorem
    associatedCuspidalInductionHomTheorem

end Langlands.CuspidalSupport
