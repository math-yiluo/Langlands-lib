import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetLengthDetector
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.MinimalJacquetStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.TotalConjugatingCountStatement
import Langlands.Representation.CuspidalSupport.InducedJacquetCount

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.InducedJacquetCount`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.InducedJacquetCount` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open Representation
open CategoryTheory
namespace Langlands.AllFieldBZ.CuspidalSupport.JacquetLength
open Langlands.CuspidalSupport.JacquetLength hiding count count_bot count_strictMono count_top count_top_eq_ker_add_range isIrreducible_transport jacquetLength jacquetLength_congr jacquetLength_eq_add_of_exact jacquetLength_eq_zero_of_subsingleton jacquetLength_induced_le jacquetLength_le jacquetLength_step jacquetLength_top normalizedJacquetEquiv one_le_jacquetLength_of_isSubquotient one_le_jacquetLength_stepQuotient stepQuotient subtypeMap subtypeMap_injective topEquiv
open Langlands.GeneralLinear
universe uF uV uW

section Irreducible
variable {k : Type*} [Field k] {G H : Type*} [Monoid G] [Monoid H]
  {V : Type*} [AddCommGroup V] [Module k V]

end Irreducible
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData) {n : ℕ}

/-- Weyl transport preserves irreducibility. -/
theorem isIrreducible_transport {B C : BlockShape n} (w : Equiv.Perm (Fin n))
    (hw : Langlands.CuspidalSupport.ConjugatesLevi (F := F.Carrier) B C w) {V : Type uV} [AddCommGroup V]
    [Module ℂ V] {ρ : Representation ℂ (B.Levi F.Carrier) V} (hρ : ρ.IsIrreducible) :
    (Langlands.CuspidalSupport.transport B C w hw ρ).IsIrreducible :=
  isIrreducible_comp (Langlands.CuspidalSupport.leviConjugation B C w hw).symm.toMonoidHom
    (Langlands.CuspidalSupport.leviConjugation B C w hw).symm.surjective hρ

/-- **Positivity.** If `I` contains every shape associated to `B`, then every
nontrivial smooth subquotient of the normalized induction of quasicuspidal data
on `B` has summed Jacquet length at least one. -/
theorem one_le_jacquetLength_of_isSubquotient
    (hmin : MinimalNonzeroJacquetTheorem.{uF, max uF uV})
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (B : BlockShape n) (I : Finset (BlockShape n))
    (hI : ∀ C, Langlands.CuspidalSupport.LevisAssociated (F := F.Carrier) B C → C ∈ I) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      Langlands.CuspidalSupport.IsLeviQuasicuspidal B σ.representation →
      ∀ Q : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        SmoothRep.IsSubquotient Q ((T.normalizedParabolicInductionFunctor B).obj σ) →
        Nontrivial Q → 1 ≤ jacquetLength T I Q.representation := by
  let := T.topology
  intro σ hσ Q hQ hnt
  obtain ⟨C, hJ, hJq⟩ := hmin F T n Q hnt
  by_cases hC : Langlands.CuspidalSupport.LevisAssociated (F := F.Carrier) B C
  · have hCI := hI C hC
    have hpos : 0 < repLength (T.normalizedJacquet C Q.representation) :=
      repLength_pos_iff.mpr hJ
    calc (1 : ℕ∞) ≤ repLength (T.normalizedJacquet C Q.representation) :=
          Order.one_le_iff_pos.mpr hpos
      _ ≤ jacquetLength T I Q.representation :=
          Finset.single_le_sum (f := fun C => repLength (T.normalizedJacquet C Q.representation))
            (fun _ _ => zero_le) hCI
  · exfalso
    have hsub := normalizedJacquetSubquotient F T n C _ _ hQ
    have hss := hnon B C σ hσ hC _ hsub hJq
    exact not_subsingleton _ hss

/-- **Positivity on step quotients.** Every nonzero step quotient of the
normalized induction of quasicuspidal data on `B` has summed Jacquet length at
least one, when `I` contains every shape associated to `B`. -/
theorem one_le_jacquetLength_stepQuotient
    (hmin : MinimalNonzeroJacquetTheorem.{uF, max uF uV})
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (B : BlockShape n) (I : Finset (BlockShape n))
    (hI : ∀ C, Langlands.CuspidalSupport.LevisAssociated (F := F.Carrier) B C → C ∈ I) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      Langlands.CuspidalSupport.IsLeviQuasicuspidal B σ.representation →
      ∀ S S' : Subrepresentation (T.normalizedParabolicInduced B σ.representation), S ≤ S' →
        Nontrivial (S'.toSubmodule ⧸ S.toSubmodule.comap S'.toSubmodule.subtype) →
        1 ≤ jacquetLength T I (stepQuotient S S') := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro σ hσ S S' _ hnt
  let A := (T.normalizedParabolicInductionFunctor B).obj σ
  have hA : IsSmooth (T.normalizedParabolicInduced B σ.representation) :=
    T.isSmooth_normalizedParabolicInduced B σ.representation
  have hS' : IsSmooth S'.toRepresentation :=
    isSmooth_of_injective (subtypeMap S') (subtypeMap_injective S') hA
  let qS : S'.toRepresentation.IntertwiningMap (stepQuotient S S') :=
    { toLinearMap := (S.toSubmodule.comap S'.toSubmodule.subtype).mkQ
      isIntertwining' := fun _ => rfl }
  have hqS : Function.Surjective qS := Submodule.mkQ_surjective _
  have hQ : IsSmooth (stepQuotient S S') := isSmooth_of_surjective qS hqS hS'
  let Cs : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) := SmoothRep.of _ hS'
  let Qs : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) := SmoothRep.of _ hQ
  have hsub : SmoothRep.IsSubquotient Qs A :=
    SmoothRep.isSubquotient_iff_exists.mpr
      ⟨Cs, SmoothRep.ofHom (A := Cs) (B := A) (subtypeMap S'),
        SmoothRep.ofHom (A := Cs) (B := Qs) qS, subtypeMap_injective S', hqS⟩
  exact one_le_jacquetLength_of_isSubquotient T hmin hnon B I hI σ hσ Qs hsub hnt

/-- **Bound.** If every shape of `I` is associated to `B`, the summed Jacquet
length of the normalized induction of irreducible quasicuspidal data on `B` is
at most `B.length!`. -/
theorem jacquetLength_induced_le
    (hfilt : AssociatedJacquetFiltrationTheorem.{uF, uV} F T n)
    (hcount : TotalConjugatingCountTheorem.{uF})
    (B : BlockShape n) (I : Finset (BlockShape n))
    (hI : ∀ C ∈ I, Langlands.CuspidalSupport.LevisAssociated (F := F.Carrier) B C) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      σ.IsIrreducible → Langlands.CuspidalSupport.IsLeviQuasicuspidal B σ.representation →
      jacquetLength T I (T.normalizedParabolicInduced B σ.representation) ≤
        (B.length.factorial : ℕ∞) := by
  let := T.topology
  intro σ hirr hσ
  have := Fintype.ofFinite (BlockShape n)
  have hC : ∀ C ∈ I,
      repLength (T.normalizedJacquet C (T.normalizedParabolicInduced B σ.representation)) =
        (Nat.card (Langlands.CuspidalSupport.MinimalConjugatingPermutations (F := F.Carrier) B C) : ℕ∞) := by
    intro C hCI
    obtain ⟨_, r, e, s, hs⟩ := hfilt B C σ hσ (hI C hCI)
    have hsimple : s.HasSimpleFactors := fun i => by
      obtain ⟨φ⟩ := hs i
      exact isIrreducible_of_equiv φ.symm
        (isIrreducible_transport _ (e i).property hirr)
    have hr : Nat.card (Langlands.CuspidalSupport.MinimalConjugatingPermutations (F := F.Carrier) B C) = r :=
      (Nat.card_congr e).symm.trans (Nat.card_eq_fintype_card.trans (Fintype.card_fin r))
    rw [hr]
    exact repLength_eq_of_hasSimpleFactors s hsimple
  obtain ⟨hfin, hcard⟩ := hcount F n B
  rw [jacquetLength, Finset.sum_congr rfl hC, ← Nat.cast_sum, ← hcard, Nat.card_sigma]
  exact_mod_cast Finset.sum_le_sum_of_subset (Finset.subset_univ I)

end Langlands.AllFieldBZ.CuspidalSupport.JacquetLength
