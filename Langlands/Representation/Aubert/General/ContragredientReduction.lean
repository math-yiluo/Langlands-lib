import Langlands.Representation.Aubert.General.ContragredientTarget

/-! # Exact-K0 reduction of contragredient commutation -/

noncomputable section

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
  (hcof : CompactOpenCofinal G)
  (hc : ContragredientPreservesFiniteLength.{uG, max uG uV} G)

/-- The two generator sums whose equality is equivalent to contragredient
commutation on the whole exact finite-length Grothendieck group. -/
def ContragredientGeneratorComparison : Prop :=
  ∀ (A : SmoothRep.{0, uG, max uG uV} ℂ G) (hA : A.HasFiniteLength),
    (∑ I : Finset ι, ((-1 : ℤ) ^ I.card) •
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((inductionJacquetFunctor.{uG, uV} (h I) (hU I)).obj A.contragredient)
        (inductionJacquet_hasFiniteLength P M U h hU hfl I A.contragredient (hc A hA))) =
    ∑ I : Finset ι, ((-1 : ℤ) ^ I.card) •
      FiniteLengthGrothendieckGroup.ofRepresentation
        (((inductionJacquetFunctor.{uG, uV} (h I) (hU I)).obj A).contragredient)
        (hc _ (inductionJacquet_hasFiniteLength P M U h hU hfl I A hA))

/-- Commutation on exact K0 is equivalent to equality of the displayed sums
on all actual finite-length smooth representations. -/
theorem contragredientCommutation_iff_generatorComparison :
    ContragredientCommutationStatement P M U h hU hfl hcof hc ↔
      ContragredientGeneratorComparison P M U h hU hfl hc := by
  have generator (A : SmoothRep.{0, uG, max uG uV} ℂ G) (hA : A.HasFiniteLength) :
      ((alternatingOperator P M U h hU hfl).comp (contragredientK0 G hcof hc))
          (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
        ∑ I : Finset ι, ((-1 : ℤ) ^ I.card) •
          FiniteLengthGrothendieckGroup.ofRepresentation
            ((inductionJacquetFunctor.{uG, uV} (h I) (hU I)).obj A.contragredient)
            (inductionJacquet_hasFiniteLength P M U h hU hfl I A.contragredient
              (hc A hA)) := by
    rw [LinearMap.comp_apply, contragredientK0_ofRepresentation,
      alternatingOperator_ofRepresentation]
  have dualGenerator (A : SmoothRep.{0, uG, max uG uV} ℂ G)
      (hA : A.HasFiniteLength) :
      ((contragredientK0 G hcof hc).comp (alternatingOperator P M U h hU hfl))
          (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
        ∑ I : Finset ι, ((-1 : ℤ) ^ I.card) •
          FiniteLengthGrothendieckGroup.ofRepresentation
            (((inductionJacquetFunctor.{uG, uV} (h I) (hU I)).obj A).contragredient)
            (hc _ (inductionJacquet_hasFiniteLength P M U h hU hfl I A hA)) := by
    rw [LinearMap.comp_apply, alternatingOperator_ofRepresentation, map_sum]
    simp only [map_smul, contragredientK0_ofRepresentation]
  constructor
  · intro heq A hA
    exact (generator A hA).symm.trans
      ((LinearMap.congr_fun heq _).trans (dualGenerator A hA))
  · intro heq
    apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ G
    intro A
    exact (generator A.val A.property).trans
      ((heq A.val A.property).trans (dualGenerator A.val A.property).symm)

/-- A sufficient representation-theoretic comparison: a cardinality-preserving
reindexing identifies the actual classes of the induction-Jacquet terms after
duality. The comparison is a hypothesis, not a general duality theorem. -/
def ContragredientTermComparison : Prop :=
  ∃ e : Finset ι ≃ Finset ι, (∀ I, (e I).card = I.card) ∧
    ∀ (I : Finset ι) (A : SmoothRep.{0, uG, max uG uV} ℂ G)
      (hA : A.HasFiniteLength),
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((inductionJacquetFunctor.{uG, uV} (h I) (hU I)).obj A.contragredient)
        (inductionJacquet_hasFiniteLength P M U h hU hfl I A.contragredient (hc A hA)) =
      FiniteLengthGrothendieckGroup.ofRepresentation
        (((inductionJacquetFunctor.{uG, uV} (h (e I)) (hU (e I))).obj A).contragredient)
        (hc _ (inductionJacquet_hasFiniteLength P M U h hU hfl (e I) A hA))

/-- The reindexing comparison implies equality of generator sums, with the
original coefficients `(-1)^|I|`. -/
theorem ContragredientTermComparison.generatorComparison
    (hcompare : ContragredientTermComparison P M U h hU hfl hc) :
    ContragredientGeneratorComparison P M U h hU hfl hc := by
  obtain ⟨e, hcard, he⟩ := hcompare
  intro A hA
  calc
    _ = ∑ I : Finset ι, ((-1 : ℤ) ^ (e I).card) •
        FiniteLengthGrothendieckGroup.ofRepresentation
          (((inductionJacquetFunctor.{uG, uV} (h (e I)) (hU (e I))).obj A).contragredient)
          (hc _ (inductionJacquet_hasFiniteLength P M U h hU hfl (e I) A hA)) := by
      apply Finset.sum_congr rfl
      intro I _
      rw [hcard I, he I A hA]
    _ = _ := Equiv.sum_comp e (fun I : Finset ι => ((-1 : ℤ) ^ I.card) •
      FiniteLengthGrothendieckGroup.ofRepresentation
        (((inductionJacquetFunctor.{uG, uV} (h I) (hU I)).obj A).contragredient)
        (hc _ (inductionJacquet_hasFiniteLength P M U h hU hfl I A hA)))

/-- Once the actual term comparisons have been proved, exact-K0 commutation
follows on every class, including every short-exact-sequence relation. -/
theorem contragredientCommutation_of_termComparison
    (hcompare : ContragredientTermComparison P M U h hU hfl hc) :
    ContragredientCommutationStatement P M U h hU hfl hcof hc :=
  (contragredientCommutation_iff_generatorComparison P M U h hU hfl hcof hc).2
    (hcompare.generatorComparison P M U h hU hfl hc)

end Langlands.Aubert.General
