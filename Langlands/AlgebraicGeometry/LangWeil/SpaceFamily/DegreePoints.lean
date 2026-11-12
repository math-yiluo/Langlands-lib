import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.SeparatedChart
import Langlands.AlgebraicGeometry.AlgebraicSpace.ConnectedFibreTargetAtlas
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleQuasiFinite

/-!
# Field points of a separated algebraic space and its symmetric tuple charts

For a separated algebraic space `X` with an affine étale chart (a `SepChart`), every point of
`X` with values in an algebraically closed field `Ω` is the image under the chart
`e_n : V_n → X` of an `Ω`-point of `V_n` outside the threshold open of `n + 2` distinct
coordinates, and such a point is unique: an `Ω`-point of `V_n` outside that threshold and an
`Ω`-point of `V_k` with the same image in `X` satisfy `k ≤ n`, with equality of the points
when `k = n`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil.SpaceFamily

open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry (EtaleEquivalenceRelation)

set_option backward.isDefEq.respectTransparency false

/-- A morphism from a scheme to the underlying scheme of a scheme over the base, as a morphism
over the base. -/
def homOver {T : Scheme.{u}} {Y : Over S0.{u}} (f : T ⟶ Y.left) : toOver T ⟶ Y :=
  Over.homMk f (specULiftZIsTerminal.hom_ext _ _)

@[simp]
theorem homOver_left {T : Scheme.{u}} {Y : Over S0.{u}} (f : T ⟶ Y.left) :
    (homOver f).left = f := rfl

theorem homOver_comp {T T' : Scheme.{u}} {Y : Over S0.{u}} (g : T ⟶ T') (f : T' ⟶ Y.left) :
    homOver (g ≫ f) = toOverHom g ≫ homOver f := by
  ext; rfl

theorem homOver_comp_left {T : Scheme.{u}} {Y Y' : Over S0.{u}} (f : T ⟶ Y.left) (h : Y ⟶ Y') :
    homOver (f ≫ h.left) = homOver f ≫ h := by
  ext; rfl

namespace SepChart

variable (c : SepChart.{u})

/-- The image in `X` of a point of the chart. -/
def ptA {T : Scheme.{u}} (o : T ⟶ c.U.left) :
    (schemeYoneda S0).obj (toOver T) ⟶ c.X.presheaf :=
  (schemeYoneda S0).map (homOver o) ≫ c.a

/-- The image in `X` of a point of `V_n` under `e_n`. -/
def ptE (n : ℕ) {T : Scheme.{u}} (v : T ⟶ c.E.tupleSymmetricScheme n) :
    (schemeYoneda S0).obj (toOver T) ⟶ c.X.presheaf :=
  (schemeYoneda S0).map (homOver (Y := c.quot n) v) ≫ c.e n

theorem ptA_comp {T T' : Scheme.{u}} (g : T' ⟶ T) (o : T ⟶ c.U.left) :
    c.ptA (g ≫ o) = (schemeYoneda S0).map (toOverHom g) ≫ c.ptA o := by
  rw [ptA, ptA, homOver_comp, Functor.map_comp, Category.assoc]

theorem ptE_comp (n : ℕ) {T T' : Scheme.{u}} (g : T' ⟶ T)
    (v : T ⟶ c.E.tupleSymmetricScheme n) :
    c.ptE n (g ≫ v) = (schemeYoneda S0).map (toOverHom g) ≫ c.ptE n v := by
  rw [ptE, ptE, homOver_comp, Functor.map_comp, Category.assoc]

/-- The image of a symmetric tuple is the image of its first coordinate. -/
theorem ptE_symmetricMap (n : ℕ) {T : Scheme.{u}} (w : T ⟶ c.E.tupleDistinctScheme n) :
    c.ptE n (w ≫ c.E.tupleSymmetricMap n) =
      c.ptA (w ≫ c.E.tupleDistinctProjection n 0) := by
  have h1 : homOver (Y := c.quot n) (w ≫ c.E.tupleSymmetricMap n) =
      homOver (Y := c.tupleOver n) w ≫ c.quotMap n := by
    ext; rfl
  have h2 : homOver (Y := c.U) (w ≫ c.E.tupleDistinctProjection n 0) =
      homOver (Y := c.tupleOver n) w ≫ c.projOver n 0 := by
    ext; rfl
  rw [ptE, ptA, h1, h2, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    quotMap_e]

/-- All coordinates of a distinct related tuple have the same image in `X`. -/
theorem ptA_projection (n : ℕ) {T : Scheme.{u}} (w : T ⟶ c.E.tupleDistinctScheme n)
    (i j : Fin (n + 1)) :
    c.ptA (w ≫ c.E.tupleDistinctProjection n i) =
      c.ptA (w ≫ c.E.tupleDistinctProjection n j) := by
  have h : ∀ k, homOver (Y := c.U) (w ≫ c.E.tupleDistinctProjection n k) =
      homOver (Y := c.tupleOver n) w ≫ c.projOver n k := fun k => by ext; rfl
  rw [ptA, ptA, h, h, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    map_projOver]

/-- Two points of the chart with the same image in `X` are related. -/
theorem exists_rel_of_ptA_eq {T : Scheme.{u}} {o o' : T ⟶ c.U.left}
    (h : c.ptA o = c.ptA o') :
    ∃ r : T ⟶ c.E.R, r ≫ c.E.t = o ∧ r ≫ c.E.s = o' := by
  let ℓ := c.pb.lift _ _ h
  let φ : toOver T ⟶ c.R := (schemeYoneda S0).preimage ℓ
  have hφ : (schemeYoneda S0).map φ = ℓ := Functor.map_preimage _ _
  have ht : φ ≫ c.t = homOver o := by
    apply (schemeYoneda S0).map_injective
    rw [Functor.map_comp, hφ, IsPullback.lift_fst]
  have hs : φ ≫ c.s = homOver o' := by
    apply (schemeYoneda S0).map_injective
    rw [Functor.map_comp, hφ, IsPullback.lift_snd]
  exact ⟨φ.left, congrArg CommaMorphism.left ht, congrArg CommaMorphism.left hs⟩

/-- Related points of the chart have the same image in `X`. -/
theorem ptA_eq_of_rel {T : Scheme.{u}} (r : T ⟶ c.E.R) :
    c.ptA (r ≫ c.E.t) = c.ptA (r ≫ c.E.s) := by
  have ht : homOver (Y := c.U) (r ≫ c.E.t) = homOver (Y := c.R) r ≫ c.t := by ext; rfl
  have hs : homOver (Y := c.U) (r ≫ c.E.s) = homOver (Y := c.R) r ≫ c.s := by ext; rfl
  rw [ptA, ptA, ht, hs, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    c.pb.w]

variable {c}

/-- The coordinates of a distinct related tuple with values in a field are pairwise
different. -/
theorem injective_coordinates (n : ℕ) {K : Type u} [Field K]
    (a : Spec (CommRingCat.of K) ⟶ c.E.tupleDistinctScheme n) :
    Function.Injective (fun i => a ≫ c.E.tupleDistinctProjection n i) := by
  have h := (c.E.range_subset_tupleDistinctOpen_iff_of_field n K
    (a ≫ (c.E.tupleDistinctOpen n).ι)).1 (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact (a x).2)
  simpa only [Category.assoc] using h

/-- Two coordinate tuples over an algebraically closed field with the same image in `X`,
the first outside the next threshold: every coordinate of the second is a coordinate of the
first. -/
theorem exists_coordinate_eq {Ω : Type u} [Field Ω] {n k : ℕ}
    (a : Spec (CommRingCat.of Ω) ⟶ c.E.tupleDistinctScheme n)
    (b : Spec (CommRingCat.of Ω) ⟶ c.E.tupleDistinctScheme k)
    (ha : c.E.tupleDistinctProjection n 0 (a (IsLocalRing.closedPoint Ω)) ∉
      c.E.tupleThresholdOpen (n + 1))
    (h : c.ptA (a ≫ c.E.tupleDistinctProjection n 0) =
      c.ptA (b ≫ c.E.tupleDistinctProjection k 0)) (j : Fin (k + 1)) :
    ∃ i, a ≫ c.E.tupleDistinctProjection n i = b ≫ c.E.tupleDistinctProjection k j := by
  have hAA : ∀ i i', c.ptA (a ≫ c.E.tupleDistinctProjection n i) =
      c.ptA (a ≫ c.E.tupleDistinctProjection n i') := fun i i' => c.ptA_projection n a i i'
  have hAB : ∀ i, c.ptA (a ≫ c.E.tupleDistinctProjection n i) =
      c.ptA (b ≫ c.E.tupleDistinctProjection k j) := fun i => by
    rw [hAA i 0, h, c.ptA_projection k b 0 j]
  exact c.E.tupleField_coordinates_exhaust n Ω (fun i => a ≫ c.E.tupleDistinctProjection n i)
    (fun i i' => c.exists_rel_of_ptA_eq (hAA i i')) (injective_coordinates n a)
    (b ≫ c.E.tupleDistinctProjection k j) (fun i => c.exists_rel_of_ptA_eq (hAB i))
    (by simpa only [Scheme.Hom.comp_apply,
      Subsingleton.elim (IsLocalRing.closedPoint Ω) (default : Spec (CommRingCat.of Ω))] using ha)

/-- Comparison of degrees: an `Ω`-point of `V_n` outside the next threshold and an `Ω`-point
of `V_k` with the same image in `X` satisfy `k ≤ n`. -/
theorem le_of_ptE_eq {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {n k : ℕ}
    (w : Spec (CommRingCat.of Ω) ⟶ c.E.tupleSymmetricScheme n)
    (hw : w (IsLocalRing.closedPoint Ω) ∉ c.E.tupleSymmetricThresholdOpen n (n + 1))
    (v : Spec (CommRingCat.of Ω) ⟶ c.E.tupleSymmetricScheme k)
    (h : c.ptE n w = c.ptE k v) : k ≤ n := by
  obtain ⟨a, rfl⟩ := exists_lift_of_surjective (c.E.tupleSymmetricMap n) w
  obtain ⟨b, rfl⟩ := exists_lift_of_surjective (c.E.tupleSymmetricMap k) v
  rw [c.ptE_symmetricMap, c.ptE_symmetricMap] at h
  have ha : c.E.tupleDistinctProjection n 0 (a (IsLocalRing.closedPoint Ω)) ∉
      c.E.tupleThresholdOpen (n + 1) := by
    rw [← c.E.tupleSymmetricMap_mem_threshold_iff]
    simpa only [Scheme.Hom.comp_apply] using hw
  choose f hf using exists_coordinate_eq a b ha h
  have hinj : Function.Injective f := fun j j' hjj => injective_coordinates k b
    (by simp only [← hf, hjj])
  simpa using Fintype.card_le_of_injective f hinj

/-- Uniqueness: two `Ω`-points of `V_n` outside the next threshold with the same image in
`X` are equal. Only the first needs to lie outside the threshold. -/
theorem eq_of_ptE_eq {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {n : ℕ}
    (w : Spec (CommRingCat.of Ω) ⟶ c.E.tupleSymmetricScheme n)
    (hw : w (IsLocalRing.closedPoint Ω) ∉ c.E.tupleSymmetricThresholdOpen n (n + 1))
    (v : Spec (CommRingCat.of Ω) ⟶ c.E.tupleSymmetricScheme n)
    (h : c.ptE n w = c.ptE n v) : w = v := by
  obtain ⟨a, rfl⟩ := exists_lift_of_surjective (c.E.tupleSymmetricMap n) w
  obtain ⟨b, rfl⟩ := exists_lift_of_surjective (c.E.tupleSymmetricMap n) v
  rw [c.ptE_symmetricMap, c.ptE_symmetricMap] at h
  have ha : c.E.tupleDistinctProjection n 0 (a (IsLocalRing.closedPoint Ω)) ∉
      c.E.tupleThresholdOpen (n + 1) := by
    rw [← c.E.tupleSymmetricMap_mem_threshold_iff]
    simpa only [Scheme.Hom.comp_apply] using hw
  exact c.E.tupleSymmetricMap_eq_of_coordinate_matching n a b (exists_coordinate_eq a b ha h)

/-- An `Ω`-point of the chart whose underlying point lies in the threshold open of `k + 1`
distinct coordinates is the first coordinate of a distinct related `Ω`-tuple of length
`k + 1`. -/
theorem exists_tuple_of_mem_threshold {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (k : ℕ)
    (o : Spec (CommRingCat.of Ω) ⟶ c.U.left)
    (ho : o (IsLocalRing.closedPoint Ω) ∈ c.E.tupleThresholdOpen k) :
    ∃ a : Spec (CommRingCat.of Ω) ⟶ c.E.tupleDistinctScheme k,
      a ≫ c.E.tupleDistinctProjection k 0 = o := by
  classical
  obtain ⟨y, ⟨w', hw'⟩, r, hrs, hrt⟩ :=
    (c.E.mem_pointSaturationOpen _ _).mp ho
  have : Etale c.E.t := c.E.etale_t
  have : Etale c.E.s := c.E.etale_s
  have : LocallyQuasiFinite c.E.t := Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale _
  have : LocallyQuasiFinite (c.E.tupleDistinctProjection k 0) :=
    Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale _
  obtain ⟨ρ, hρ, hρpt⟩ := exists_lift_at_point c.E.t o r hrt
  obtain ⟨a', ha', -⟩ := exists_lift_at_point (c.E.tupleDistinctProjection k 0) (ρ ≫ c.E.s) w'
    (by
      have hc : (ρ ≫ c.E.s) (IsLocalRing.closedPoint Ω) = c.E.s (ρ (IsLocalRing.closedPoint Ω)) :=
        rfl
      rw [hw', hc, hρpt, hrs])
  have hall : ∀ i, c.ptA (a' ≫ c.E.tupleDistinctProjection k i) = c.ptA o := fun i => by
    rw [c.ptA_projection k a' i 0, ha', ← c.ptA_eq_of_rel, hρ]
  by_cases hmem : ∃ i, a' ≫ c.E.tupleDistinctProjection k i = o
  · obtain ⟨i, hi⟩ := hmem
    let σ := Equiv.swap (0 : Fin (k + 1)) i
    refine ⟨a' ≫ c.E.tupleDistinctReindex σ σ.injective, ?_⟩
    rw [Category.assoc, c.E.tupleDistinctReindex_projection]
    simpa [σ] using hi
  · push Not at hmem
    let A : Fin (k + 1) → (Spec (CommRingCat.of Ω) ⟶ c.U.left) :=
      Function.update (fun i => a' ≫ c.E.tupleDistinctProjection k i) 0 o
    have hA : ∀ i, c.ptA (A i) = c.ptA o := fun i => by
      by_cases hi : i = 0
      · subst hi; simp [A]
      · simp only [A, Function.update_of_ne hi]; exact hall i
    have hinj : Function.Injective A := by
      intro i j hij
      by_cases hi : i = 0 <;> by_cases hj : j = 0
      · rw [hi, hj]
      · simp only [A, hi, Function.update_self, Function.update_of_ne hj] at hij
        exact absurd hij.symm (hmem j)
      · simp only [A, hj, Function.update_self, Function.update_of_ne hi] at hij
        exact absurd hij (hmem i)
      · simp only [A, Function.update_of_ne hi, Function.update_of_ne hj] at hij
        exact injective_coordinates k a' hij
    refine ⟨c.E.tupleDistinctFieldLift k Ω A
      (fun i j => c.exists_rel_of_ptA_eq ((hA i).trans (hA j).symm)) hinj, ?_⟩
    rw [c.E.tupleDistinctFieldLift_projection]
    simp [A]

/-- Existence: every point of `X` with values in an algebraically closed field is the image
of a point of some `V_n`, `n` below the tuple-length bound, outside the next threshold. -/
theorem exists_ptE_eq {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (z : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of Ω))) ⟶ c.X.presheaf) :
    ∃ n < c.N, ∃ v : Spec (CommRingCat.of Ω) ⟶ c.E.tupleSymmetricScheme n,
      v (IsLocalRing.closedPoint Ω) ∉ c.E.tupleSymmetricThresholdOpen n (n + 1) ∧
        c.ptE n v = z := by
  obtain ⟨t, ht⟩ := exists_lift_atlas_algClosed c.a c.etale_a c.surj_a Ω _ z
  have hz : c.ptA t.left = z := by
    rw [← ht, ptA]
    congr 2
  obtain ⟨n, ⟨hn, hmem, hnot⟩, -⟩ :=
    c.E.exists_unique_tupleDegreeLocus (t.left (IsLocalRing.closedPoint Ω))
  obtain ⟨a, ha⟩ := exists_tuple_of_mem_threshold n t.left hmem
  refine ⟨n, hn, a ≫ c.E.tupleSymmetricMap n, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, c.E.tupleSymmetricMap_mem_threshold_iff, ← Scheme.Hom.comp_apply,
      ha]
    exact hnot
  · rw [c.ptE_symmetricMap, ha, hz]

end SepChart

end Langlands.AlgebraicGeometry.LangWeil.SpaceFamily
