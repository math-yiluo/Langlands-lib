import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociation
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card

/-! # Finite sums over actual semistandard association representatives -/

noncomputable section

universe u uV uX

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.Association

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

set_option hygiene false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
local notation "Q" => AssociationClass.{u, uV} a ha mu

/-- The association class of a literal semistandard spectral index. -/
def classOf (t : Θ) : Q := Quotient.mk (associationSetoid a ha mu) t

@[simp] theorem classOf_eq_iff {t t' : Θ} :
    classOf a ha mu t = classOf a ha mu t' ↔ Associated a ha mu t t' :=
  Quotient.eq

/-- One representative of each actual association class. -/
structure Representatives where
  select : Q → Θ
  classOf_select : Function.RightInverse select (classOf a ha mu)

/-- The quotient provides one possible representative choice. -/
def Representatives.ofQuotient : Representatives.{u, uV} a ha mu where
  select c := c.out
  classOf_select c := Quotient.out_eq c

variable (r : Representatives.{u, uV} a ha mu) {X : Type uX} [AddCommMonoid X]

@[simp] theorem mem_associatedIndices_select (c : Q) (t : Θ) :
    t ∈ associatedIndices a ha mu (r.select c) ↔ classOf a ha mu t = c := by
  change Associated a ha mu (r.select c) t ↔ _
  rw [← classOf_eq_iff, r.classOf_select c, eq_comm]

/-- Sum a function over one representative in each association class. -/
def representativeSum (f : Θ → X) : X := ∑ᶠ c : Q, f (r.select c)

/-- Every contributing representative belongs to a class meeting the input support. -/
theorem support_representativeSummand_subset {f : Θ → X} {s : Set Θ}
    (hf : Function.support f ⊆ s) :
    Function.support (fun c => f (r.select c)) ⊆ classOf a ha mu '' s :=
  fun c hc => ⟨r.select c, hf hc, r.classOf_select c⟩

/-- The representative sum is finite on the classes meeting any finite support bound. -/
theorem representativeSum_eq_sum (f : Θ → X) {s : Set Θ} (hs : s.Finite)
    (hf : Function.support f ⊆ s) :
    representativeSum a ha mu r f =
      ∑ c ∈ (hs.image (classOf a ha mu)).toFinset, f (r.select c) :=
  finsum_eq_sum_of_support_subset_of_finite _ (support_representativeSummand_subset a ha mu r hf) _

/-- Regroup a finite sum of class-constant values using any representatives
and the cardinality of the actual association class of each representative. -/
theorem finsum_eq_representativeSum (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hcontain : SemistandardLeviCentralizerContainmentStatement.{u})
    (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
    (f : Θ → X) (hf : (Function.support f).Finite)
    (hconstant : ∀ t t', Associated a ha mu t t' → f t = f t') :
    (∑ᶠ t, f t) = representativeSum a ha mu r
      (fun t => Nat.card (associatedIndices a ha mu t) • f t) := by
  classical
  let classes := classOf a ha mu '' Function.support f
  let fiber (c : Q) := associatedIndices a ha mu (r.select c)
  have hfinite (c : Q) : (fiber c).Finite :=
    finite_associatedIndices a ha mu hG hi hfin (r.select c)
      (hcontain F G hG S i hi (r.select c).1.toLevi)
  have hdisjoint : classes.PairwiseDisjoint fiber := by
    intro b _ c _ hne
    apply Set.disjoint_left.mpr
    intro t ht hu
    exact hne (((mem_associatedIndices_select a ha mu r b t).mp ht).symm.trans
      ((mem_associatedIndices_select a ha mu r c t).mp hu))
  have hsubset : Function.support f ⊆ ⋃ c ∈ classes, fiber c := by
    intro t ht
    exact Set.mem_iUnion₂.mpr ⟨classOf a ha mu t, ⟨t, ht, rfl⟩,
      (mem_associatedIndices_select a ha mu r _ t).mpr rfl⟩
  calc
    (∑ᶠ t, f t) = ∑ᶠ t ∈ ⋃ c ∈ classes, fiber c, f t := by
      rw [← finsum_mem_univ f]
      exact finsum_mem_inter_support_eq' f _ _ fun t ht =>
        iff_of_true (Set.mem_univ t) (hsubset ht)
    _ = ∑ᶠ c ∈ classes, ∑ᶠ t ∈ fiber c, f t :=
      finsum_mem_biUnion hdisjoint (hf.image _) (fun c _ => hfinite c)
    _ = ∑ᶠ c ∈ classes, Nat.card (fiber c) • f (r.select c) := by
      apply finsum_mem_congr rfl
      intro c _
      rw [finsum_mem_eq_finite_toFinset_sum _ (hfinite c)]
      calc
        _ = ∑ t ∈ (hfinite c).toFinset, f (r.select c) :=
          Finset.sum_congr rfl fun t ht => (hconstant _ _ ((hfinite c).mem_toFinset.mp ht)).symm
        _ = _ := by
          rw [Finset.sum_const, ← Set.ncard_eq_toFinset_card (fiber c) (hfinite c),
            Nat.card_coe_set_eq]
    _ = representativeSum a ha mu r (fun t => Nat.card (associatedIndices a ha mu t) • f t) := by
      unfold representativeSum
      conv_rhs => rw [← finsum_mem_univ]
      apply finsum_mem_inter_support_eq'
      intro c hc
      have hnonzero : f (r.select c) ≠ 0 := fun h => hc (by simp [h])
      exact iff_of_true ⟨r.select c, hnonzero, r.classOf_select c⟩ (Set.mem_univ c)

end Langlands.HarishChandraSchwartz.RationalSemistandard.Association
