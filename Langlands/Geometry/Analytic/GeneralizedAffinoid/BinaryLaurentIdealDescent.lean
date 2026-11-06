import Langlands.Geometry.Analytic.GeneralizedAffinoid.SplitSquareIdealDescent
import Langlands.Geometry.Analytic.GeneralizedAffinoid.BinaryLaurentGluingProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.BinaryLaurentOverlapComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Noetherian

/-! # Closed-ideal effectiveness for the actual binary Laurent diagram -/

noncomputable section

universe u v w

namespace Langlands.Analytic

namespace BoundedAlgEquiv

variable {K : Type u} [NormedField K] {B : Type v} {C : Type w}
  [NormedCommRing B] [NormedCommRing C] [NormedAlgebra K B] [NormedAlgebra K C]

/-- Closedness of all ideals transfers along a bounded algebra equivalence. -/
theorem isClosed_ideal (e : BoundedAlgEquiv K B C)
    (hB : ∀ I : Ideal B, IsClosed (I : Set B)) (I : Ideal C) : IsClosed (I : Set C) := by
  have h := (hB (I.comap e.toAlgEquiv)).preimage e.symm.toBoundedAlgHom.continuous
  convert h using 1
  ext x
  change x ∈ I ↔ e.toAlgEquiv (e.toAlgEquiv.symm x) ∈ I
  rw [AlgEquiv.apply_symm_apply]

end BoundedAlgEquiv

namespace PresentedAffinoidAlgebra

namespace RelativeRationalPresentation

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))

/-- An intrinsic relative rational quotient is equivalent to a scalar presented affinoid. -/
theorem exists_boundedAlgEquiv (g : A) (f : Fin m → A) :
    ∃ B : PresentedAffinoidAlgebra K, Nonempty (BoundedAlgEquiv K B (Algebra K A s g f)) := by
  obtain ⟨g', rfl⟩ := presentationMap_surjective K A g
  choose f' hf' using fun j => presentationMap_surjective K A (f j)
  obtain rfl : (fun j => presentationMap K A (f' j)) = f := funext hf'
  exact ⟨_, ⟨RationalPresentation.relativeEquiv K A s g' f'⟩⟩

theorem isNoetherianRing (g : A) (f : Fin m → A) : IsNoetherianRing (Algebra K A s g f) := by
  obtain ⟨B, ⟨e⟩⟩ := exists_boundedAlgEquiv K A s g f
  exact isNoetherianRing_of_ringEquiv B e.toAlgEquiv.toRingEquiv

theorem isClosed_ideal (g : A) (f : Fin m → A) (I : Ideal (Algebra K A s g f)) :
    IsClosed (I : Set (Algebra K A s g f)) := by
  obtain ⟨B, ⟨e⟩⟩ := exists_boundedAlgEquiv K A s g f
  exact e.isClosed_ideal (PresentedAffinoidAlgebra.isClosed_ideal B) I

end RelativeRationalPresentation

namespace BinaryLaurent

open GeneralizedTateAlgebra RelativeUnitAnnulus

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) (f : A)

theorem isNoetherianRing_upper : IsNoetherianRing (Upper K A f) :=
  RelativeRationalPresentation.isNoetherianRing K A _ _ _

theorem isNoetherianRing_lower : IsNoetherianRing (Lower K A f) :=
  RelativeRationalPresentation.isNoetherianRing K A _ _ _

theorem isClosed_upper_ideal (I : Ideal (Upper K A f)) : IsClosed (I : Set (Upper K A f)) :=
  RelativeRationalPresentation.isClosed_ideal K A _ _ _ I

theorem isClosed_lower_ideal (I : Ideal (Lower K A f)) : IsClosed (I : Set (Lower K A f)) :=
  RelativeRationalPresentation.isClosed_ideal K A _ _ _ I

theorem isClosed_overlap_ideal (I : Ideal (Overlap K A f)) :
    IsClosed (I : Set (Overlap K A f)) :=
  (productOverlapEquiv K A f).isClosed_ideal
    (RelativeRationalPresentation.isClosed_ideal K A _ _ _) I

/-- Every overlap element is a sum of images from the two sides, with norms at
most twice its norm. -/
theorem exists_split (o : Overlap K A f) :
    ∃ h₁ h₂, o = left K A f h₁ + right K A f h₂ ∧ ‖h₁‖ ≤ 2 * ‖o‖ ∧ ‖h₂‖ ≤ 2 * ‖o‖ := by
  rcases eq_or_ne o 0 with rfl | ho
  · exact ⟨0, 0, by simp, by simp, by simp⟩
  obtain ⟨z, rfl, hz⟩ := exists_toOverlap_norm_lt K A f o (norm_pos_iff.mpr ho)
  obtain ⟨e, -, -, hY, -, hpos, hneg⟩ := normal_form K A
  set r := PrincipalRelations.upperSeries K A (e z)
  set s := PrincipalRelations.lowerSeries K A (e z)
  have hzrs : z = positive K A r + annulusY K A * negative K A s := by
    refine e.injective (ZeroAtInftyContinuousMap.ext fun n => ?_)
    rw [map_add, ZeroAtInftyContinuousMap.add_apply, hY, hpos, hneg]
    by_cases hn : 0 ≤ n
    · rw [ite_eq_left hn, ite_eq_right (by omega), add_zero,
        PrincipalRelations.coeff_upperSeries, Int.toNat_of_nonneg hn]
    · rw [ite_eq_right hn, ite_eq_left (by omega), zero_add,
        PrincipalRelations.coeff_lowerSeries]
      congr 1
      omega
  have hcoeff (c : ℕ → A) (hc : ∀ k, ‖c k‖ ≤ ‖e z‖) (t : GeneralizedTateAlgebra
      (PositivePolyradius.unit (Fin 1)) A)
      (ht : ∀ k, MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) k)
        (series _ A t) = c k) : ‖t‖ ≤ ‖z‖ := by
    rw [← e.norm_map z]
    refine (norm_le_iff _ A t (norm_nonneg _)).mpr fun d => ?_
    obtain ⟨k, rfl⟩ := NormalForm.exists_single_eq d
    rw [PositivePolyradius.unit_weight, mul_one, ht]
    exact hc k
  have hr : ‖r‖ ≤ ‖z‖ := hcoeff (fun k => e z k)
    (fun k => NormalForm.norm_apply_le _ _) r (PrincipalRelations.coeff_upperSeries K A _)
  have hs : ‖s‖ ≤ ‖z‖ := hcoeff (fun k => e z (-(k : ℤ) - 1))
    (fun k => NormalForm.norm_apply_le _ _) s (PrincipalRelations.coeff_lowerSeries K A _)
  have hz2 : ‖z‖ ≤ 2 * ‖toOverlap K A f z‖ := by linarith
  refine ⟨RelativeRationalPresentation.quotientMap K A _ 1 (fun _ => f) r,
    lowerY K A f * RelativeRationalPresentation.quotientMap K A _ f (fun _ => 1) s,
    ?_, ?_, ?_⟩
  · conv_lhs => rw [hzrs]
    rw [map_add, map_mul, toOverlap_positive, toOverlap_negative, toOverlap_annulusY, map_mul,
      right_lowerY]
  · exact (RelativeRationalPresentation.norm_quotientMap_le K A _ _ _ r).trans (hr.trans hz2)
  · calc _ ≤ ‖lowerY K A f‖ *
          ‖RelativeRationalPresentation.quotientMap K A _ f (fun _ => 1) s‖ := norm_mul_le _ _
      _ ≤ 1 * ‖s‖ := mul_le_mul (norm_lowerY_le K A f)
          (RelativeRationalPresentation.norm_quotientMap_le K A _ _ _ s) (norm_nonneg _)
          zero_le_one
      _ ≤ 2 * ‖toOverlap K A f z‖ := by rw [one_mul]; exact hs.trans hz2

/-- The left image of every upper element is a limit of right images. -/
theorem left_mem_closure_range_right (h : Upper K A f) :
    left K A f h ∈ closure (Set.range (right K A f)) := by
  obtain ⟨r, rfl⟩ := RelativeRationalPresentation.quotientMap_surjective K A _ 1 (fun _ => f) h
  let φ := (left K A f).comp
    (RelativeRationalPresentation.quotientMap K A (PositivePolyradius.unit (Fin 1)) 1
      (fun _ => f))
  have hsum := (hasSum_monomials _ A r).map φ.toAlgHom.toRingHom.toAddMonoidHom φ.continuous
  have hmono (d : Fin 1 →₀ ℕ) (a : A) :
      φ (monomial _ A d a) ∈ Set.range (right K A f) := by
    refine ⟨lowerBase K A f (a * f ^ d 0), ?_⟩
    change right K A f (lowerBase K A f (a * f ^ d 0)) =
      left K A f (RelativeRationalPresentation.quotientMap K A _ 1 (fun _ => f)
        (monomial _ A d a))
    rw [right_lowerBase, ← toOverlap_positive, NormalForm.positive_monomial]
    simp only [map_mul, map_pow, toOverlap_baseMap, toOverlap_annulusX, overlapX_eq]
  apply mem_closure_of_tendsto hsum
  refine Filter.Eventually.of_forall fun t => ?_
  obtain ⟨b, hb⟩ : ∃ b : Lower K A f, ∑ d ∈ t, φ (monomial _ A d
      (MvPowerSeries.coeff d (series _ A r))) = right K A f b := by
    choose b hb using fun d => hmono d (MvPowerSeries.coeff d (series _ A r))
    exact ⟨∑ d ∈ t, b d, by rw [map_sum]; exact Finset.sum_congr rfl fun d _ => (hb d).symm⟩
  exact ⟨b, hb.symm⟩

theorem denseRange_right : DenseRange (right K A f) := by
  intro o
  obtain ⟨h₁, h₂, rfl, -, -⟩ := exists_split K A f o
  let G : AddSubgroup (Overlap K A f) := (right K A f).toAlgHom.toRingHom.toAddMonoidHom.range
  have hG : (G.topologicalClosure : Set (Overlap K A f)) = closure (Set.range (right K A f)) := by
    rw [AddSubgroup.topologicalClosure_coe]
    rfl
  have h₁' : left K A f h₁ ∈ (G.topologicalClosure : Set (Overlap K A f)) := by
    rw [hG]
    exact left_mem_closure_range_right K A f h₁
  rw [← hG]
  exact G.topologicalClosure.add_mem h₁' (G.le_topologicalClosure ⟨h₂, rfl⟩)

/-- The actual binary Laurent square is split, given scalar gluing of
compatible upper and lower elements; the splitting constant is `2`. -/
def splitSquare
    (hglue : ∀ (s : Upper K A f) (t : Lower K A f), left K A f s = right K A f t →
      ∃ a : A, upperBase K A f a = s ∧ lowerBase K A f a = t) :
    BoundedAlgHom.SplitSquare (upperBase K A f) (lowerBase K A f) (left K A f) (right K A f) where
  comm a := by rw [left_upperBase, right_lowerBase]
  glue := hglue
  dense := denseRange_right K A f
  bound := 2
  bound_nonneg := zero_le_two
  split := exists_split K A f

/-- Closed-ideal effectiveness for the actual binary Laurent diagram, given
scalar gluing of compatible upper and lower elements. -/
theorem closedIdealMap_inf_comap_eq_of_gluing
    (hglue : ∀ (s : Upper K A f) (t : Lower K A f), left K A f s = right K A f t →
      ∃ a : A, upperBase K A f a = s ∧ lowerBase K A f a = t)
    (I₁ : Ideal (Upper K A f)) (I₂ : Ideal (Lower K A f))
    (hI : (left K A f).closedIdealMap I₁ = (right K A f).closedIdealMap I₂) :
    (upperBase K A f).closedIdealMap
        (I₁.comap (upperBase K A f).toAlgHom.toRingHom ⊓
          I₂.comap (lowerBase K A f).toAlgHom.toRingHom) = I₁ ∧
      (lowerBase K A f).closedIdealMap
        (I₁.comap (upperBase K A f).toAlgHom.toRingHom ⊓
          I₂.comap (lowerBase K A f).toAlgHom.toRingHom) = I₂ := by
  have := isNoetherianRing_upper K A f
  have := isNoetherianRing_lower K A f
  exact (splitSquare K A f hglue).closedIdealMap_inf_comap_eq (isClosed_upper_ideal K A f)
    (isClosed_lower_ideal K A f) (isClosed_overlap_ideal K A f) I₁ I₂ hI

/-- Over a strict base and a nontrivially normed field, the published scalar
gluing theorem makes the binary Laurent square split. -/
def splitSquareOfStrict (hK : ∃ c : K, 1 < ‖c‖) (P : PresentedStrictAffinoidAlgebra K)
    (f : ofStrict K P) :
    BoundedAlgHom.SplitSquare (upperBase K (ofStrict K P) f) (lowerBase K (ofStrict K P) f)
      (left K (ofStrict K P) f) (right K (ofStrict K P) f) :=
  splitSquare K (ofStrict K P) f fun s t hst => (gluing K hK P f s t hst).exists

/-- Closed-ideal effectiveness for the binary Laurent diagram over a strict base
and a nontrivially normed field. -/
theorem closedIdealMap_inf_comap_eq_ofStrict (hK : ∃ c : K, 1 < ‖c‖)
    (P : PresentedStrictAffinoidAlgebra K) (f : ofStrict K P)
    (I₁ : Ideal (Upper K (ofStrict K P) f)) (I₂ : Ideal (Lower K (ofStrict K P) f))
    (hI : (left K (ofStrict K P) f).closedIdealMap I₁ =
      (right K (ofStrict K P) f).closedIdealMap I₂) :
    (upperBase K (ofStrict K P) f).closedIdealMap
        (I₁.comap (upperBase K (ofStrict K P) f).toAlgHom.toRingHom ⊓
          I₂.comap (lowerBase K (ofStrict K P) f).toAlgHom.toRingHom) = I₁ ∧
      (lowerBase K (ofStrict K P) f).closedIdealMap
        (I₁.comap (upperBase K (ofStrict K P) f).toAlgHom.toRingHom ⊓
          I₂.comap (lowerBase K (ofStrict K P) f).toAlgHom.toRingHom) = I₂ :=
  closedIdealMap_inf_comap_eq_of_gluing K (ofStrict K P) f
    (fun s t hst => (gluing K hK P f s t hst).exists) I₁ I₂ hI

end BinaryLaurent

end PresentedAffinoidAlgebra

end Langlands.Analytic
