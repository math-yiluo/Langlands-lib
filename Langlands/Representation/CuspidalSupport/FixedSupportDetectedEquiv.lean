import Langlands.Representation.Derivative.CuspidalProductDetectedConstituent
import Langlands.Representation.CuspidalSupport.AssociationForwardFactorsProof
import Langlands.Representation.CuspidalSupport.BlockPermutationTensor
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Actual equivalences between detected constituents with the same support. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport

open GeneralLinear PadicField.TopologicalData

universe uF uV

private theorem count_ofFn_eq_sum {α : Type*} [DecidableEq α]
    {k : ℕ} (f : Fin k → α) (a : α) :
    (List.ofFn f).count a = ∑ i, if f i = a then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    simp only [beq_iff_eq, Nat.add_comm]

private theorem fiber_card {α : Type*} [DecidableEq α]
    {k : ℕ} (f : Fin k → α) (a : α) :
    Fintype.card {i : Fin k // f i = a} = (List.ofFn f).count a := by
  simp only [count_ofFn_eq_sum, Finset.sum_boole, Fintype.card_subtype, Nat.cast_id]

private def reindexingOfMultiset {α : Type*} {k l : ℕ}
    (f : Fin k → α) (g : Fin l → α)
    (h : (List.ofFn f : Multiset α) = (List.ofFn g : Multiset α)) :
    {e : Fin k ≃ Fin l // ∀ i, g (e i) = f i} := by
  classical
  have hc (a : α) : Fintype.card {i : Fin k // f i = a} =
      Fintype.card {i : Fin l // g i = a} := by
    rw [fiber_card f a, fiber_card g a]
    simpa only [Multiset.coe_count] using congrArg (Multiset.count a) h
  let e := fun a => Fintype.equivOfCardEq (hc a)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

private theorem subquotient_of_matching
    {G : Type uF} [Group G] [TopologicalSpace G]
    {A B D : SmoothRep.{0,uF,uV} ℂ G}
    (h : HaveSameJordanHolderFactors A.obj B.obj)
    (hD : D.IsIrreducible) (hDA : SmoothRep.IsSubquotient D A) :
    SmoothRep.IsSubquotient D B := by
  obtain ⟨r, s, t, hs, ht, e, he⟩ := h
  obtain ⟨S, U, ⟨E⟩⟩ := hDA
  obtain ⟨j, ⟨f⟩⟩ := simpleSubquotientFactor ℂ G A r s hs D S U hD
    ⟨SmoothRep.equivOfIso E⟩
  obtain ⟨g⟩ := he j
  exact SmoothRep.IsSubquotient.of_iso_left
    (SmoothRep.mkIso (f.trans g).symm)
    (t.smoothGradedObject_isSubquotient (e j))

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

private theorem cuspidalProduct_factors_permute {n : ℕ} (hn : 0 < n)
    (B : BlockShape n) (e : Equiv.Perm (Fin B.length))
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :
    letI := T.topology
    HaveSameJordanHolderFactors
      (((T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)).obj)
      (((T.normalizedProductInductionFunctor (B.permute e)).obj
        (fun i => (A (e i)).obj)).obj) := by
  let := T.topology
  let σ := FiniteTensor.externalSmoothObject (fun i => (A i).obj)
  let τ := FiniteTensor.externalSmoothObject (fun i => (A (e i)).obj)
  have hσ := glCuspidalTensor p F T n hn B A
  have hτ := glCuspidalTensor p F T n hn (B.permute e) (fun i => A (e i))
  have ha : RepresentationsAssociated B (B.permute e)
      σ.representation τ.representation :=
    ⟨B.blockPermutation e, conjugatesLevi_blockPermutation B e,
      ⟨blockPermutationTensorEquiv B e (conjugatesLevi_blockPermutation B e)
        (fun i => (A i).obj.representation)⟩⟩
  exact associatedCuspidalInductionFactorsTheorem p F T n hn
    B (B.permute e) σ τ hσ.1 hσ.2 hτ.1 hτ.2 ha

/-- Construct an actual equivalence between positive-rank irreducible
constituents with the same supercuspidal support and nonzero top derivatives. -/
def fixedSupportDetectedEquiv
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (hn : 0 < n)
    (D E : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (s : Multiset (CuspidalDatum.{uV,uF} T))
    (hD : T.IsSupercuspidalSupport D s)
    (hE : T.IsSupercuspidalSupport E s)
    (hJD : letI := T.topology
      Nontrivial ((Derivative.generalLinearDerivative T ψ n n le_rfl).obj D))
    (hJE : letI := T.topology
      Nontrivial ((Derivative.generalLinearDerivative T ψ n n le_rfl).obj E)) :
    letI := T.topology
    D.representation.Equiv E.representation := by
  classical
  letI := T.topology
  apply Classical.choice
  obtain ⟨k, ρ, hρ, h, A, hA, hirrD, hDA⟩ := hD
  obtain ⟨l, ρ', hρ', h', A', hA', hirrE, hEA'⟩ := hE
  have hkl : k = l := by
    simpa only [Multiset.coe_card, List.length_ofFn] using
      congrArg Multiset.card (hρ.trans hρ'.symm)
  subst l
  obtain ⟨e, he'⟩ := reindexingOfMultiset ρ' ρ (hρ'.trans hρ.symm)
  have he : ρ' = fun i => ρ (e i) :=
    funext fun i => (he' i).symm
  subst ρ'
  have hEA : SmoothRep.IsSubquotient E
      (T.cuspidalProductInduced (fun i => ρ (e i)) h'
        (fun i => A (e i))) :=
    SmoothRep.IsSubquotient.of_iso_right hEA'
      (T.cuspidalProductInducedIsoOfRepresented h' hA'
        (fun i => hA (e i)))
  have hEP : SmoothRep.IsSubquotient E (T.cuspidalProductInduced ρ h A) :=
    subquotient_of_matching
      (haveSameJordanHolderFactors_symm
        (cuspidalProduct_factors_permute T hn (T.cuspidalShape ρ h) e A))
      hirrE hEA
  let c := Derivative.chooseCuspidalProductDetectedConstituent T ψ hn
    (T.cuspidalShape ρ h) A
  exact ⟨(c.detected.equivalence D hirrD hDA hJD).symm.trans
    (c.detected.equivalence E hirrE hEP hJE)⟩

end Langlands.CuspidalSupport
