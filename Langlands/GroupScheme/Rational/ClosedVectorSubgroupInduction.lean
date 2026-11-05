import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.AffineLineRigidity

/-! # Ambient retractions for closed vector subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClosedVectorSubgroup

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- A closed subgroup of a standard vector group is affine. -/
theorem isAffine_of_closed_into_vector
    {H : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
    (i : H ⟶ VectorGroup.groupScheme (CommRingCat.of k) n)
    (hi : IsClosedSubgroup i) : IsAffine H.X.left := by
  let : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffine (VectorGroup.groupScheme (CommRingCat.of k) n).X.left := by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) k)))
    infer_instance
  exact isAffine_of_isAffineHom i.hom.hom.left

section Capture

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
    (A Z : Over S') (z : Z ⟶ A)
    {H V G L : GroupScheme S}

/-- Every pointed map from the specified test object factors through the
changed group homomorphism. -/
def CapturesPointedMaps (l : L ⟶ H) : Prop :=
  ∀ a : A ⟶ ((GroupScheme.baseChange b).obj H).X,
    z ≫ a = 1 → a ∈
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map l)).carrier A

/-- Pointed curve capture passes through a scheme-theoretic intersection. -/
theorem capture_via_intersection
    (i : H ⟶ G) (s : V ⟶ G) (t : G ⟶ V) (hst : s ≫ t = 𝟙 V)
    (l : L ⟶ subgroupIntersection i s)
    (hambient : ∀ a : A ⟶ ((GroupScheme.baseChange b).obj H).X,
      z ≫ a = 1 → a ≫ ((GroupScheme.baseChange b).map i).hom.hom ∈
        (SubgroupFunctor.range ((GroupScheme.baseChange b).map s)).carrier A)
    (hintersection : ∀ a : A ⟶
      ((GroupScheme.baseChange b).obj (subgroupIntersection i s)).X,
      z ≫ a = 1 → a ∈
        (SubgroupFunctor.range ((GroupScheme.baseChange b).map l)).carrier A) :
    ∀ a : A ⟶ ((GroupScheme.baseChange b).obj H).X,
      z ≫ a = 1 → a ∈ (SubgroupFunctor.range
        ((GroupScheme.baseChange b).map (l ≫ subgroupIntersectionFst i s))).carrier A := by
  intro a ha
  let F := GroupScheme.baseChange b
  have hr := hambient a ha
  change ∃ v : A ⟶ (F.obj V).X,
    v ≫ (F.map s).hom.hom = a ≫ (F.map i).hom.hom at hr
  obtain ⟨v, hv⟩ := hr
  have hp : IsPullback (F.map (subgroupIntersectionFst i s)).hom.hom
      (F.map (subgroupIntersectionSnd i s)).hom.hom
      (F.map i).hom.hom (F.map s).hom.hom :=
    (subgroupIntersection_isPullback i s).map (Over.pullback b)
  have hst' : (F.map s).hom.hom ≫ (F.map t).hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, ← F.map_comp, hst, F.map_id, Grp.id_hom_hom]
  have hv0 : z ≫ v = 1 := by
    calc
      z ≫ v = z ≫ v ≫ (F.map s).hom.hom ≫ (F.map t).hom.hom := by
        rw [hst', Category.comp_id]
      _ = 1 := by rw [← Category.assoc v, hv, ← Category.assoc z,
        ← Category.assoc z, ha, MonObj.one_comp, MonObj.one_comp]
  let c : A ⟶ (F.obj (subgroupIntersection i s)).X := hp.lift a v hv.symm
  have hc0 : z ≫ c = 1 := by
    apply hp.hom_ext
    · rw [Category.assoc, hp.lift_fst, ha, MonObj.one_comp]
    · rw [Category.assoc, hp.lift_snd, hv0, MonObj.one_comp]
  have hr := hintersection c hc0
  change ∃ w : A ⟶ (F.obj L).X, w ≫ (F.map l).hom.hom = c at hr
  obtain ⟨w, hw⟩ := hr
  change ∃ w : A ⟶ (F.obj L).X,
    w ≫ (F.map (l ≫ subgroupIntersectionFst i s)).hom.hom = a
  refine ⟨w, ?_⟩
  rw [F.map_comp, Grp.comp_hom_hom, ← Category.assoc, hw]
  exact hp.lift_fst a v hv.symm

end Capture

section Induction

variable {S' : Scheme.{u}} (b : S' ⟶ Spec (CommRingCat.of k))
    (A Z : Over S') (z : Z ⟶ A)

/-- Strictly smaller ambient vector envelopes suffice to construct a capturing
vector subgroup with a retraction from the entire original ambient group. -/
theorem exists_capturing_ambientRetraction_of_lowering
    (step : ∀ (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k)))
      (i : H ⟶ VectorGroup.groupScheme (CommRingCat.of k) n),
      IsClosedSubgroup i → ¬ IsIso i →
        ∃ (r : ℕ) (s : VectorGroup.groupScheme (CommRingCat.of k) r ⟶
          VectorGroup.groupScheme (CommRingCat.of k) n)
          (t : VectorGroup.groupScheme (CommRingCat.of k) n ⟶
          VectorGroup.groupScheme (CommRingCat.of k) r),
          r < n ∧ s ≫ t = 𝟙 _ ∧
            ∀ a : A ⟶ ((GroupScheme.baseChange b).obj H).X,
              z ≫ a = 1 → a ≫ ((GroupScheme.baseChange b).map i).hom.hom ∈
                (SubgroupFunctor.range ((GroupScheme.baseChange b).map s)).carrier A)
    (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k)))
    (i : H ⟶ VectorGroup.groupScheme (CommRingCat.of k) n)
    (hi : IsClosedSubgroup i) :
    ∃ (r : ℕ) (l : VectorGroup.groupScheme (CommRingCat.of k) r ⟶ H)
      (t : VectorGroup.groupScheme (CommRingCat.of k) n ⟶
        VectorGroup.groupScheme (CommRingCat.of k) r),
      l ≫ i ≫ t = 𝟙 _ ∧
        CapturesPointedMaps b A Z z l := by
  induction n using Nat.strong_induction_on generalizing H with
  | h n ih =>
    by_cases hproper : IsIso i
    · let e := asIso i
      refine ⟨n, e.inv, 𝟙 _, ?_, ?_⟩
      · simp [e]
      · intro a _
        change ∃ w : A ⟶ ((GroupScheme.baseChange b).obj
            (VectorGroup.groupScheme (CommRingCat.of k) n)).X,
          w ≫ ((GroupScheme.baseChange b).map e.inv).hom.hom = a
        refine ⟨a ≫ ((GroupScheme.baseChange b).map e.hom).hom.hom, ?_⟩
        rw [Category.assoc, ← Grp.comp_hom_hom, ← Functor.map_comp,
          e.hom_inv_id, (GroupScheme.baseChange b).map_id, Grp.id_hom_hom,
          Category.comp_id]
    · obtain ⟨m, s, t, hmn, hst, hcapture⟩ := step n H i hi hproper
      let J := subgroupIntersection i s
      let j : J ⟶ VectorGroup.groupScheme (CommRingCat.of k) m :=
        subgroupIntersectionSnd i s
      have hj : IsClosedSubgroup j := by
        change IsClosedImmersion j.hom.hom.left
        exact MorphismProperty.of_isPullback
          (subgroupIntersection_isPullback_scheme i s) hi
      obtain ⟨r, l, t', hsplit, hcap⟩ := ih m hmn J j hj
      refine ⟨r, l ≫ subgroupIntersectionFst i s, t ≫ t', ?_, ?_⟩
      · calc
          (l ≫ subgroupIntersectionFst i s) ≫ i ≫ t ≫ t' =
              l ≫ j ≫ s ≫ t ≫ t' := by
            simpa only [Category.assoc, j] using
              congrArg (fun f => l ≫ f ≫ t ≫ t')
                (subgroupIntersection_condition i s)
          _ = 𝟙 _ := by
            rw [← Category.assoc s t t']
            rw [hst, Category.id_comp]
            exact hsplit
      · exact capture_via_intersection b A Z z i s t hst l hcapture hcap

end Induction

end Langlands.GroupScheme.ClosedVectorSubgroup
