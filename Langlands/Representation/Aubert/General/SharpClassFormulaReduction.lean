import Langlands.Representation.Aubert.General.SharpConsequenceStatements
import Langlands.Representation.Aubert.General.StandardExactness
import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Aubert.FiniteProductGrothendieck
import Langlands.Representation.Smooth.FiniteExactEuler

/-!
# Signed class formula from exactness before the terminal degree

A generic conditional reduction of `SharpClassFormulaTarget`: exactness of the actual
standard-subset complex before its terminal degree, together with vanishing of the actual
Jacquet modules at standard subsets with fewer than `|I|` roots, gives
`D_G[E] = (-1)^{|I|} [E#]` in the actual finite-length Grothendieck group.
See the paired Markdown.
-/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped BigOperators

namespace Langlands.Aubert.General.SharpClassFormula

open SmoothRep SmoothRep.FiniteLengthGrothendieckGroup

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)
  (hfl : ∀ J, ParabolicFiniteLength.{uG, max uG (max uI uV)} (h J) (hclosed J))

include hfl in
/-- Every homogeneous degree of the actual complex of a finite-length object has
finite length. -/
theorem degree_hasFiniteLength (E : SmoothRep.{0, uG, max uI uG uV} ℂ G)
    (hE : E.HasFiniteLength) (k : ℕ) :
    (StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed E k).HasFiniteLength :=
  FiniteProduct.finiteLength _ fun s =>
    inductionJacquet_hasFiniteLength.{uI, uG, max uI uV} P M U h hclosed hfl
      (Finset.univ \ s.1) E hE

/-- The exact class of a homogeneous degree is the sum of the classes of its
actual normalized coordinates. -/
theorem degree_class (E : SmoothRep.{0, uG, max uI uG uV} ℂ G)
    (hE : E.HasFiniteLength) (k : ℕ) :
    ofRepresentation (StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed E k)
        (degree_hasFiniteLength P M U h hclosed hfl E hE k) =
      ∑ s : {s : Finset ι // s.card = k},
        ofRepresentation
          ((inductionJacquetFunctor.{uG, max uI uV} (h (Finset.univ \ s.1))
            (hclosed (Finset.univ \ s.1))).obj E)
          (inductionJacquet_hasFiniteLength.{uI, uG, max uI uV} P M U h hclosed hfl
            (Finset.univ \ s.1) E hE) := by
  let S := {s : Finset ι // s.card = k}
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let A : Fin (Fintype.card S) → FiniteLengthObject.{0, uG, max uI uG uV} ℂ G := fun j =>
    ⟨(inductionJacquetFunctor.{uG, max uI uV} (h (Finset.univ \ (e j).1))
      (hclosed (Finset.univ \ (e j).1))).obj E,
      inductionJacquet_hasFiniteLength.{uI, uG, max uI uV} P M U h hclosed hfl
        (Finset.univ \ (e j).1) E hE⟩
  have eq : (StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed E k).representation.Equiv
      (FiniteProduct.object A).val.representation :=
    Representation.Equiv.mk
      (LinearEquiv.piCongrLeft ℂ
        (fun s : S => Complex.Term (StandardComplex.removedFamily P)
          (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
          (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) E s.1) e).symm
      (fun _ => rfl)
  rw [ofRepresentation_eq_of_equiv _ (FiniteProduct.object A).property eq]
  change ofObject (FiniteProduct.object A) = _
  rw [FiniteProduct.class_eq_sum]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

omit [LinearOrder ι] [Fintype ι] in
include hfl in
/-- An actual normalized coordinate whose Jacquet module is zero has zero
exact class. -/
theorem term_vanish (E : SmoothRep.{0, uG, max uI uG uV} ℂ G) (hE : E.HasFiniteLength)
    (J : Finset ι)
    (hJ : Subsingleton ((jacquetFunctor.{uG, max uG (max uI uV)} (h J) (hclosed J)).obj E)) :
    ofRepresentation ((inductionJacquetFunctor.{uG, max uI uV} (h J) (hclosed J)).obj E)
        (inductionJacquet_hasFiniteLength.{uI, uG, max uI uV} P M U h hclosed hfl J E hE) =
      0 := by
  have h0 : ofRepresentation ((jacquetFunctor.{uG, max uG (max uI uV)} (h J) (hclosed J)).obj E)
      ((hfl J).2.2.1 E hE) = 0 :=
    IrreducibleGrothendieckProof.ofRepresentation_eq_zero_of_subsingleton _ _
  have hi := inductionK0_ofRepresentation.{uG, max uI uV} (h J) (hclosed J) (hfl J).1 (hfl J).2.1 _
    ((hfl J).2.2.1 E hE)
  rw [h0, map_zero] at hi
  exact hi.symm

/-- The homogeneous degrees as actual finite-length objects. -/
def degreeFL (E : SmoothRep.{0, uG, max uI uG uV} ℂ G) (hE : E.HasFiniteLength) (k : ℕ) :
    FiniteLengthObject.{0, uG, max uI uG uV} ℂ G :=
  ⟨StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed E k,
    degree_hasFiniteLength P M U h hclosed hfl E hE k⟩

/-- The signed differentials of the standard-subset complex. -/
def degreeMap (E : SmoothRep.{0, uG, max uI uG uV} ℂ G) (k : ℕ) :
    StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed E k ⟶
      StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed E (k + 1) :=
  Complex.degreeMorphism.{uI, uG, max uI uV} (StandardComplex.removedFamily P) (StandardComplex.removedFamily M)
    (StandardComplex.removedFamily U) (fun s => h (Finset.univ \ s))
    (fun s => hclosed (Finset.univ \ s)) (fun s => hδ (Finset.univ \ s))
    (StandardComplex.removedFamily_antitone hP) (StandardComplex.removedFamily_monotone hU) E k

/-- The terminal homology of the finite exact sequence is the actual terminal
cokernel of the complex. -/
theorem terminal_class (E : SmoothRep.{0, uG, max uI uG uV} ℂ G) (hE : E.HasFiniteLength)
    (k : ℕ)
    (hk : (Complex.terminalObject.{uI, uG, max uI uV} (StandardComplex.removedFamily P)
      (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
      (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
      (fun s => hδ (Finset.univ \ s)) (StandardComplex.removedFamily_antitone hP)
      (StandardComplex.removedFamily_monotone hU) E k).HasFiniteLength) :
    ofObject (FiniteExactEuler.terminal (degreeFL P M U h hclosed hfl E hE)
        (degreeMap P M U h hclosed hδ hP hU E) k) =
      ofRepresentation (Complex.terminalObject.{uI, uG, max uI uV} (StandardComplex.removedFamily P)
        (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
        (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
        (fun s => hδ (Finset.univ \ s)) (StandardComplex.removedFamily_antitone hP)
        (StandardComplex.removedFamily_monotone hU) E k) hk := by
  cases k with
  | zero =>
    exact ofRepresentation_eq_of_equiv _ _
      (Representation.Equiv.mk (Submodule.quotEquivOfEqBot ⊥ rfl).symm
        (fun _ => LinearMap.ext fun _ => rfl))
  | succ k =>
    exact ofRepresentation_eq_of_equiv _ _
      (Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun _ => rfl))

/-- Reindexing by removed roots and grouping by cardinality writes `D_G` on an
actual finite-length class as the descending-sign sum of the degree classes. -/
theorem alternatingOperator_degree_sum (E : SmoothRep.{0, uG, max uI uG uV} ℂ G)
    (hE : E.HasFiniteLength) :
    alternatingOperator.{uI, uG, max uI uV} P M U h hclosed hfl (ofRepresentation E hE) =
      ∑ i ∈ Finset.range (Fintype.card ι + 1), (-1 : ℤ) ^ (Fintype.card ι - i) •
        ofObject (degreeFL P M U h hclosed hfl E hE i) := by
  rw [alternatingOperator_ofRepresentation]
  let F : Finset ι → FiniteLengthGrothendieckGroup.{0, uG, max uI uG uV} ℂ G := fun J =>
    ofRepresentation ((inductionJacquetFunctor.{uG, max uI uV} (h J) (hclosed J)).obj E)
      (inductionJacquet_hasFiniteLength.{uI, uG, max uI uV} P M U h hclosed hfl J E hE)
  change ∑ J : Finset ι, (-1 : ℤ) ^ J.card • F J = _
  rw [← Fintype.sum_equiv (Function.Involutive.toPerm (fun s : Finset ι => Finset.univ \ s)
      (fun s => Finset.sdiff_sdiff_eq_self (Finset.subset_univ s)))
    (fun s => (-1 : ℤ) ^ (Finset.univ \ s).card • F (Finset.univ \ s)) _ (fun _ => rfl)]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (Fintype.card ι + 1))
    (g := Finset.card) (fun s _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ s)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsign : ∀ s ∈ (Finset.univ.filter fun s : Finset ι => s.card = i),
      (-1 : ℤ) ^ (Finset.univ \ s).card • F (Finset.univ \ s) =
        (-1 : ℤ) ^ (Fintype.card ι - i) • F (Finset.univ \ s) := by
    intro s hs
    rw [Finset.card_univ_sdiff, (Finset.mem_filter.mp hs).2]
  rw [Finset.sum_congr rfl hsign, ← Finset.smul_sum,
    Finset.sum_subtype (p := fun s : Finset ι => s.card = i) _ (fun s => by simp)]
  change _ = (-1 : ℤ) ^ (Fintype.card ι - i) • ofRepresentation
    (StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed E i)
    (degree_hasFiniteLength P M U h hclosed hfl E hE i)
  rw [degree_class P M U h hclosed hfl E hE i]

/-- Above the terminal degree every coordinate has removed roots complementary
to a set of fewer than `|I|` roots, so the degree class vanishes. -/
theorem degree_class_eq_zero (I : Finset ι) (E : SmoothRep.{0, uG, max uI uG uV} ℂ G)
    (hE : E.HasFiniteLength)
    (hvan : ∀ K : Finset ι, K.card < I.card →
      Subsingleton ((jacquetFunctor.{uG, max uG (max uI uV)} (h K) (hclosed K)).obj E))
    (i : ℕ) (hi : Complex.terminalDegree I < i) :
    ofObject (degreeFL P M U h hclosed hfl E hE i) = 0 := by
  change ofRepresentation
    (StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed E i)
    (degree_hasFiniteLength P M U h hclosed hfl E hE i) = 0
  rw [degree_class P M U h hclosed hfl E hE i]
  refine Finset.sum_eq_zero fun s _ => term_vanish P M U h hclosed hfl E hE _ (hvan _ ?_)
  have hs := Finset.card_le_univ s.1
  have hI := Finset.card_le_univ I
  rw [Finset.card_univ_sdiff, s.2]
  unfold Complex.terminalDegree at hi
  omega

/-- The signed class formula, assuming exactness before the terminal degree and
vanishing of the Jacquet modules at all standard subsets with fewer than `|I|`
roots. -/
theorem class_formula_of_exact (I : Finset ι) (E : SmoothRep.{0, uG, max uI uG uV} ℂ G)
    (hE : E.HasFiniteLength)
    (hE' : (StandardComplex.sharpObject.{uI, uG, max uI uV}
      P M U h hclosed hδ hP hU E I).HasFiniteLength)
    (hexact : StandardComplex.IsExactBeforeTerminal.{uI, uG, max uI uV}
      P M U h hclosed hδ hP hU E I)
    (hvan : ∀ K : Finset ι, K.card < I.card →
      Subsingleton ((jacquetFunctor.{uG, max uG (max uI uV)} (h K) (hclosed K)).obj E)) :
    alternatingOperator.{uI, uG, max uI uV} P M U h hclosed hfl (ofRepresentation E hE) =
      ((-1 : ℤ) ^ I.card) •
        ofRepresentation (StandardComplex.sharpObject.{uI, uG, max uI uV}
          P M U h hclosed hδ hP hU E I) hE' := by
  have hI := Finset.card_le_univ I
  have htn : Complex.terminalDegree I = Fintype.card ι - I.card := rfl
  have heuler := FiniteExactEuler.signed_descending_class
    (degreeFL P M U h hclosed hfl E hE) (degreeMap P M U h hclosed hδ hP hU E)
    (Complex.terminalDegree I) (Fintype.card ι + 1) (by omega)
    (fun hpos => LinearMap.ker_eq_bot.mp (hexact 0 hpos))
    (fun i hi => (hexact (i + 1) hi).symm)
  rw [terminal_class P M U h hclosed hδ hP hU hfl E hE _ hE'] at heuler
  have hsign : Fintype.card ι + 1 - (Complex.terminalDegree I + 1) = I.card := by omega
  simp only [hsign, Nat.add_sub_add_right] at heuler
  change _ = _ • ofRepresentation (Complex.terminalObject.{uI, uG, max uI uV}
    (StandardComplex.removedFamily P) (StandardComplex.removedFamily M)
    (StandardComplex.removedFamily U) (fun s => h (Finset.univ \ s))
    (fun s => hclosed (Finset.univ \ s)) (fun s => hδ (Finset.univ \ s))
    (StandardComplex.removedFamily_antitone hP) (StandardComplex.removedFamily_monotone hU) E
    (Complex.terminalDegree I)) hE'
  rw [← heuler, smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul,
    alternatingOperator_degree_sum P M U h hclosed hfl E hE]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i _ hi => ?_
  rw [degree_class_eq_zero P M U h hclosed hfl I E hE hvan i
    (by simpa [Finset.mem_range] using hi), smul_zero]

end Langlands.Aubert.General.SharpClassFormula
