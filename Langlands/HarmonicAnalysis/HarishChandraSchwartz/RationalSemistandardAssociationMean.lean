import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociationCount
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociationSums

/-! # The arithmetic mean over an actual association class -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.Association

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (Z p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu

/-- The ordinary arithmetic mean over the actual association class. -/
def associationMean (f : Θ → ℂ) (t : Θ) : ℂ :=
  (Nat.card (associatedIndices a ha mu t) : ℂ)⁻¹ *
    ∑ᶠ q ∈ associatedIndices a ha mu t, f q

theorem associatedIndices_eq {t q : Θ} (h : Associated a ha mu t q) :
    associatedIndices a ha mu t = associatedIndices a ha mu q := by
  let e := (associationSetoid a ha mu).iseqv
  exact Set.ext fun z => ⟨fun hz => e.trans (e.symm h) hz, fun hz => e.trans h hz⟩

theorem associationMean_eq_of_associated (f : Θ → ℂ) {t q : Θ} (h : Associated a ha mu t q) :
    associationMean a ha mu f t = associationMean a ha mu f q := by
  unfold associationMean
  rw [associatedIndices_eq a ha mu h]

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hfin : SemistandardSpectralFiberFinitenessStatement.{u})

section WeylPairs

variable [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (hD : SemistandardSpectralDynamicCoverageStatement.{u})
  (t : Θ) (hM : torusCentralizer i ≤ t.1.levi)

set_option hygiene false in
local notation "Pairs" => WeylParabolicPair hG hi hD t.1.toLevi hM
set_option hygiene false in
local notation "target" => weylParabolicTarget hG hi hD a ha mu t hM

include hfin in
/-- Each actual associated target occurs with the same transporter
multiplicity in the Weyl-parabolic sum. The normalized sum is its class mean. -/
theorem weylParabolicMean_eq_associationMean (f : Θ → ℂ) :
    (Nat.card Pairs : ℂ)⁻¹ * (∑ᶠ x : Pairs, f (target x)) =
      associationMean a ha mu f t := by
  classical
  let U := associatedIndices a ha mu t
  let W := weylOrbitStabilizerSubgroup a ha mu t
  let : Finite Pairs := finite_weylParabolicPair hG hi hD hfin t.1.toLevi hM
  let : Finite U := finite_associatedIndices a ha mu hG hi hfin t hM
  let := hG.finite_relativeWeylGroup i hi
  let : Fintype Pairs := Fintype.ofFinite Pairs
  let : Fintype U := Fintype.ofFinite U
  let : Fintype W := Fintype.ofFinite W
  let e := (weylParabolicPairEquivTransporters hG hi hD a ha mu t hM).trans
    (Equiv.sigmaEquivProdOfEquiv fun q : U =>
      (weylTransporterEquivStabilizer a ha mu q.property.choose_spec).symm)
  have hsum : (∑ᶠ x : Pairs, f (target x)) =
      (Nat.card W : ℂ) * ∑ᶠ q ∈ associatedIndices a ha mu t, f q := by
    rw [finsum_eq_sum_of_fintype]
    calc
      (∑ x : Pairs, f (target x)) = ∑ z : U × W, f z.1.val :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by
        have hU : (∑ᶠ q ∈ U, f q) = ∑ q : U, f q :=
          (finsum_set_coe_eq_finsum_mem (f := f) U).symm.trans
            (finsum_eq_sum_of_fintype (fun q : U => f q))
        rw [Fintype.sum_prod_type, hU]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card, ← Finset.mul_sum]
  have hW : (Nat.card W : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [hsum, card_weylParabolicPair_eq_association_mul_stabilizer hG hi hD a ha mu t hM,
    Nat.cast_mul]
  change ((Nat.card U : ℂ) * (Nat.card W : ℂ))⁻¹ *
    ((Nat.card W : ℂ) * ∑ᶠ q ∈ U, f q) =
      (Nat.card U : ℂ)⁻¹ * ∑ᶠ q ∈ U, f q
  rw [← mul_assoc, mul_inv_rev, mul_right_comm (Nat.card W : ℂ)⁻¹ (Nat.card U : ℂ)⁻¹,
    inv_mul_cancel₀ hW, one_mul]

end WeylPairs

variable (hc : SemistandardLeviCentralizerContainmentStatement.{u})

include hG hi hfin hc in
theorem support_associationMean_subset (f : Θ → ℂ) :
    Function.support (associationMean a ha mu f) ⊆
      associationSaturation a ha mu (Function.support f) := by
  intro t ht
  by_contra hn
  have hz (q : Θ) (hq : q ∈ associatedIndices a ha mu t) : f q = 0 := by
    by_contra hq'
    exact hn ((mem_associationSaturation a ha mu _ t).mpr
      ⟨q, hq', (associationSetoid a ha mu).iseqv.symm hq⟩)
  have hf := finite_associatedIndices a ha mu hG hi hfin t (hc F G hG S i hi t.1.toLevi)
  apply ht
  rw [associationMean, finsum_mem_eq_finite_toFinset_sum _ hf,
    Finset.sum_eq_zero (fun q hq => hz q (hf.mem_toFinset.mp hq)), mul_zero]

include hG hi hfin hc in
/-- Regroup any finitely supported function by the actual association
classes, taking the full sum over each class at its representative. -/
theorem finsum_eq_representativeClassSum {X : Type*} [AddCommMonoid X]
    (R : Representatives.{u, uV} a ha mu) (f : Θ → X) (hf : (Function.support f).Finite) :
    (∑ᶠ t, f t) = representativeSum a ha mu R
      (fun t => ∑ᶠ q ∈ associatedIndices a ha mu t, f q) := by
  classical
  let classes := classOf a ha mu '' Function.support f
  let fiber (c : AssociationClass a ha mu) := associatedIndices a ha mu (R.select c)
  have hfinite (c : AssociationClass a ha mu) : (fiber c).Finite :=
    finite_associatedIndices a ha mu hG hi hfin (R.select c)
      (hc F G hG S i hi (R.select c).1.toLevi)
  have hdisjoint : classes.PairwiseDisjoint fiber := by
    intro b _ c _ hne
    apply Set.disjoint_left.mpr
    intro t ht hu
    exact hne (((mem_associatedIndices_select a ha mu R b t).mp ht).symm.trans
      ((mem_associatedIndices_select a ha mu R c t).mp hu))
  have hsubset : Function.support f ⊆ ⋃ c ∈ classes, fiber c := by
    intro t ht
    exact Set.mem_iUnion₂.mpr ⟨classOf a ha mu t, ⟨t, ht, rfl⟩,
      (mem_associatedIndices_select a ha mu R _ t).mpr rfl⟩
  calc
    (∑ᶠ t, f t) = ∑ᶠ t ∈ ⋃ c ∈ classes, fiber c, f t := by
      rw [← finsum_mem_univ f]
      exact finsum_mem_inter_support_eq' f _ _ fun t ht =>
        iff_of_true (Set.mem_univ t) (hsubset ht)
    _ = ∑ᶠ c ∈ classes, ∑ᶠ t ∈ fiber c, f t :=
      finsum_mem_biUnion hdisjoint (hf.image _) (fun c _ => hfinite c)
    _ = representativeSum a ha mu R (fun t => ∑ᶠ q ∈ associatedIndices a ha mu t, f q) := by
      unfold representativeSum
      conv_rhs => rw [← finsum_mem_univ]
      apply finsum_mem_inter_support_eq'
      intro c hnonzero
      refine iff_of_true ?_ (Set.mem_univ c)
      by_contra hn
      apply hnonzero
      change (∑ᶠ q ∈ fiber c, f q) = 0
      rw [finsum_mem_eq_finite_toFinset_sum _ (hfinite c)]
      apply Finset.sum_eq_zero
      intro q hq
      by_contra hq'
      exact hn ⟨q, hq', (mem_associatedIndices_select a ha mu R c q).mp
        ((hfinite c).mem_toFinset.mp hq)⟩

include hG hi hfin hc in
/-- Taking class means preserves the finite weighted total for any weight
which is constant on the actual association classes. -/
theorem finsum_mul_associationMean (f w : Θ → ℂ) (hf : (Function.support f).Finite)
    (hw : ∀ t q : Θ, Associated a ha mu t q → w t = w q) :
    (∑ᶠ t, w t * associationMean a ha mu f t) = ∑ᶠ t, w t * f t := by
  let R := Representatives.ofQuotient a ha mu
  let f' t := w t * associationMean a ha mu f t
  have hs : (Function.support (associationMean a ha mu f)).Finite :=
    (finite_associationSaturation a ha mu hG hi hc hfin hf).subset
      (support_associationMean_subset a ha mu hG hi hfin hc f)
  have hsupport (g : Θ → ℂ) :
      Function.support (fun t => w t * g t) ⊆ Function.support g := by
    intro t ht hz
    exact ht (by simp only [hz, mul_zero])
  have hf' : (Function.support f').Finite := hs.subset (hsupport _)
  have hconstant (t q : Θ) (h : Associated a ha mu t q) : f' t = f' q :=
    congrArg₂ (· * ·) (hw t q h) (associationMean_eq_of_associated a ha mu f h)
  rw [finsum_eq_representativeSum a ha mu R hG hi hc hfin f' hf' hconstant,
    finsum_eq_representativeClassSum a ha mu hG hi hfin hc R _ (hf.subset (hsupport f))]
  unfold representativeSum
  apply finsum_congr
  intro c
  let t := R.select c
  let U := associatedIndices a ha mu t
  let : Finite U := finite_associatedIndices a ha mu hG hi hfin t (hc F G hG S i hi t.1.toLevi)
  let : Nonempty U := ⟨⟨t, (associationSetoid a ha mu).iseqv.refl t⟩⟩
  have hn : (Nat.card U : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  change Nat.card U • (w t * associationMean a ha mu f t) =
    ∑ᶠ q ∈ U, w q * f q
  have he : (∑ᶠ q ∈ U, w q * f q) = w t * (∑ᶠ q ∈ U, f q) := by
    have hU : U.Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hU, finsum_mem_eq_finite_toFinset_sum _ hU,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun q hq =>
      congrArg (· * f q) (hw t q (hU.mem_toFinset.mp hq)).symm
  rw [he, associationMean, nsmul_eq_mul]
  change (Nat.card U : ℂ) * (w t * ((Nat.card U : ℂ)⁻¹ * ∑ᶠ q ∈ U, f q)) =
    w t * ∑ᶠ q ∈ U, f q
  rw [mul_left_comm (Nat.card U : ℂ) (w t), ← mul_assoc (Nat.card U : ℂ),
    mul_inv_cancel₀ hn, one_mul]

end Langlands.HarishChandraSchwartz.RationalSemistandard.Association
