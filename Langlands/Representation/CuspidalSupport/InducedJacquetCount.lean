import Langlands.Representation.CuspidalSupport.JacquetLengthDetector
import Langlands.Representation.CuspidalSupport.MinimalJacquetStatement
import Langlands.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement
import Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.Representation.CuspidalSupport.FiniteBlockShapes

/-!
# Summed Jacquet lengths of quasicuspidal inductions

For quasicuspidal inducing data on a block shape `B` and a finite set `I` of
block shapes, the summed Jacquet length over `I` is positive on every nonzero
step quotient of the induced representation as soon as `I` contains every
shape associated to `B`, and it is at most `B.length!` as soon as every shape
of `I` is associated to `B`. The first bound uses minimal nonzero Jacquet
descent and the vanishing of quasicuspidal subquotients for nonassociated
Levis; the second uses the associated Jacquet filtration and the total count of
minimal conjugating permutations. These four theorems enter as hypotheses.
-/

noncomputable section

open Representation CategoryTheory

namespace Langlands.CuspidalSupport.JacquetLength

open GeneralLinear

universe uF uV uW

/-- The finite set of block shapes whose standard Levi is associated to that
of `B`. -/
def associatedShapes (F : Type uF) [Field F] {n : ℕ} (B : BlockShape n) :
    Finset (BlockShape n) :=
  (Set.toFinite {C : BlockShape n | LevisAssociated (F := F) B C}).toFinset

theorem mem_associatedShapes {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n} :
    C ∈ associatedShapes F B ↔ LevisAssociated (F := F) B C :=
  Set.Finite.mem_toFinset _

section Irreducible

variable {k : Type*} [Field k] {G H : Type*} [Monoid G] [Monoid H]
  {V : Type*} [AddCommGroup V] [Module k V]

/-- Invariant subspaces do not change under composition with a surjective
homomorphism of monoids. -/
def compSubrepresentationOrderIso (ρ : Representation k G V) (f : H →* G)
    (hf : Function.Surjective f) :
    Subrepresentation ρ ≃o Subrepresentation (ρ.comp f) where
  toFun S := ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (f h) hv⟩
  invFun S := ⟨S.toSubmodule, fun g _ hv => by
    obtain ⟨h, rfl⟩ := hf g
    exact S.apply_mem_toSubmodule h hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Composition with a surjective homomorphism preserves irreducibility. -/
theorem isIrreducible_comp {ρ : Representation k G V} (f : H →* G)
    (hf : Function.Surjective f) (hρ : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp f) :=
  (OrderIso.isSimpleOrder_iff (compSubrepresentationOrderIso ρ f hf)).mp hρ

/-- An equivalence of representations preserves irreducibility. -/
theorem isIrreducible_of_equiv {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : ρ.Equiv σ)
    (hρ : ρ.IsIrreducible) : σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at hρ ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    e.bijective).1 hρ

end Irreducible

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- Weyl transport preserves irreducibility. -/
theorem isIrreducible_transport {B C : BlockShape n} (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F.Carrier) B C w) {V : Type uV} [AddCommGroup V]
    [Module ℂ V] {ρ : Representation ℂ (B.Levi F.Carrier) V} (hρ : ρ.IsIrreducible) :
    (transport B C w hw ρ).IsIrreducible :=
  isIrreducible_comp (leviConjugation B C w hw).symm.toMonoidHom
    (leviConjugation B C w hw).symm.surjective hρ

/-- **Positivity.** If `I` contains every shape associated to `B`, then every
nontrivial smooth subquotient of the normalized induction of quasicuspidal data
on `B` has summed Jacquet length at least one. -/
theorem one_le_jacquetLength_of_isSubquotient
    (hmin : MinimalNonzeroJacquetTheorem.{uF, max uF uV})
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (B : BlockShape n) (I : Finset (BlockShape n))
    (hI : ∀ C, LevisAssociated (F := F.Carrier) B C → C ∈ I) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      IsLeviQuasicuspidal B σ.representation →
      ∀ Q : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        SmoothRep.IsSubquotient Q ((T.normalizedParabolicInductionFunctor B).obj σ) →
        Nontrivial Q → 1 ≤ jacquetLength T I Q.representation := by
  let := T.topology
  intro σ hσ Q hQ hnt
  obtain ⟨C, hJ, hJq⟩ := hmin p F T n Q hnt
  by_cases hC : LevisAssociated (F := F.Carrier) B C
  · have hCI := hI C hC
    have hpos : 0 < repLength (T.normalizedJacquet C Q.representation) :=
      repLength_pos_iff.mpr hJ
    calc (1 : ℕ∞) ≤ repLength (T.normalizedJacquet C Q.representation) :=
          Order.one_le_iff_pos.mpr hpos
      _ ≤ jacquetLength T I Q.representation :=
          Finset.single_le_sum (f := fun C => repLength (T.normalizedJacquet C Q.representation))
            (fun _ _ => zero_le) hCI
  · exfalso
    have hsub := normalizedJacquetSubquotient p F T n C _ _ hQ
    have hss := hnon B C σ hσ hC _ hsub hJq
    exact not_subsingleton _ hss

/-- **Positivity on step quotients.** Every nonzero step quotient of the
normalized induction of quasicuspidal data on `B` has summed Jacquet length at
least one, when `I` contains every shape associated to `B`. -/
theorem one_le_jacquetLength_stepQuotient
    (hmin : MinimalNonzeroJacquetTheorem.{uF, max uF uV})
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (B : BlockShape n) (I : Finset (BlockShape n))
    (hI : ∀ C, LevisAssociated (F := F.Carrier) B C → C ∈ I) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      IsLeviQuasicuspidal B σ.representation →
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
    (hI : ∀ C ∈ I, LevisAssociated (F := F.Carrier) B C) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      σ.IsIrreducible → IsLeviQuasicuspidal B σ.representation →
      jacquetLength T I (T.normalizedParabolicInduced B σ.representation) ≤
        (B.length.factorial : ℕ∞) := by
  let := T.topology
  intro σ hirr hσ
  have := Fintype.ofFinite (BlockShape n)
  have hC : ∀ C ∈ I,
      repLength (T.normalizedJacquet C (T.normalizedParabolicInduced B σ.representation)) =
        (Nat.card (MinimalConjugatingPermutations (F := F.Carrier) B C) : ℕ∞) := by
    intro C hCI
    obtain ⟨_, r, e, s, hs⟩ := hfilt B C σ hσ (hI C hCI)
    have hsimple : s.HasSimpleFactors := fun i => by
      obtain ⟨φ⟩ := hs i
      exact isIrreducible_of_equiv φ.symm
        (isIrreducible_transport _ (e i).property hirr)
    have hr : Nat.card (MinimalConjugatingPermutations (F := F.Carrier) B C) = r :=
      (Nat.card_congr e).symm.trans (Nat.card_eq_fintype_card.trans (Fintype.card_fin r))
    rw [hr]
    exact repLength_eq_of_hasSimpleFactors s hsimple
  obtain ⟨hfin, hcard⟩ := hcount p F n B
  rw [jacquetLength, Finset.sum_congr rfl hC, ← Nat.cast_sum, ← hcard, Nat.card_sigma]
  exact_mod_cast Finset.sum_le_sum_of_subset (Finset.subset_univ I)

end Langlands.CuspidalSupport.JacquetLength
