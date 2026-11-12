import Langlands.Representation.Category.IdempotentDecomposition
import Langlands.Representation.CuspidalSupport.PointwiseProjectorSum
import Mathlib.Algebra.FiniteSupport.Basic

/-! # Actual coproducts from pointwise finite orthogonal projectors -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A pointwise finite sum of intertwiners, with independently sized index type. -/
def finiteSupportIntertwinerSum {A B : SmoothRep.{0, uG, uV} ℂ G} {ι : Type uI}
    (f : ι → A.representation.IntertwiningMap B.representation)
    (hf : ∀ x : A, Function.HasFiniteSupport (fun i => f i x)) :
    A.representation.IntertwiningMap B.representation where
  toLinearMap :=
    { toFun := fun x => ∑ᶠ i, f i x
      map_add' := fun x y => by
        simp only [map_add]
        exact finsum_add_distrib (hf x) (hf y)
      map_smul' := fun a x => by
        simp only [map_smul, RingHom.id_apply]
        exact (smul_finsum' a (hf x)).symm }
  isIntertwining' g := by
    ext x
    change (∑ᶠ i, f i (A.representation g x)) = B.representation g (∑ᶠ i, f i x)
    rw [map_finsum _ (hf x)]
    exact finsum_congr fun i => Representation.IntertwiningMap.isIntertwining _ _ (f i) g x

namespace SmoothRep

/-- The canonical map to the actual range of an intertwiner. -/
def projectorToRange {A : SmoothRep.{0, uG, uV} ℂ G}
    (p : A.representation.IntertwiningMap A.representation) :
    A ⟶ subrepresentation A p.range := ofHom
  { toLinearMap := p.toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext x
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ p g x) }

/-- The actual range objects and subtype maps form a coproduct whenever the
orthogonal idempotents are pointwise finite and sum to the identity. -/
def projectorRangeCofanIsColimit {ι : Type uI}
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (e : ι → A.representation.IntertwiningMap A.representation)
    (hf : ∀ x : A, Function.HasFiniteSupport (fun i => e i x))
    (hid : ∀ i x, e i (e i x) = e i x)
    (horth : ∀ i j, i ≠ j → ∀ x, e i (e j x) = 0)
    (hsum : ∀ x : A, (∑ᶠ i, e i x) = x) :
    IsColimit (Cofan.mk A (fun i => subtype A (e i).range)) := by
  classical
  let q (i : ι) := projectorToRange (e i)
  let f (s : Cofan (fun i => subrepresentation A (e i).range)) (i : ι) :=
    (hom (s.inj i)).comp (hom (q i))
  have hfinite (s : Cofan (fun i => subrepresentation A (e i).range)) (x : A) :
      Function.HasFiniteSupport (fun i => f s i x) := by
    apply (hf x).subset
    intro i hi
    by_contra he
    apply hi
    have he' : e i x = 0 := Classical.not_not.mp he
    change hom (s.inj i) (hom (q i) x) = 0
    have hq : hom (q i) x = 0 := Subtype.ext he'
    rw [hq, map_zero]
  let desc (s : Cofan (fun i => subrepresentation A (e i).range)) : A ⟶ s.pt :=
    ofHom (finiteSupportIntertwinerSum (f s) (hfinite s))
  refine Cofan.IsColimit.mk _ desc ?_ ?_
  · intro s i
    ext x
    change (∑ᶠ j, f s j x.val) = hom (s.inj i) x
    have hei : e i x.val = x.val := by
      obtain ⟨y, hy⟩ := x.property
      rw [← hy]
      exact hid i y
    rw [finsum_eq_single _ i]
    · change hom (s.inj i) (hom (q i) x.val) = hom (s.inj i) x
      congr 1
      exact Subtype.ext hei
    · intro j hji
      change hom (s.inj j) (hom (q j) x.val) = 0
      have he : e j x.val = 0 := by
        obtain ⟨y, hy⟩ := x.property
        rw [← hy]
        exact horth j i hji y
      have hq : hom (q j) x.val = 0 := Subtype.ext he
      rw [hq, map_zero]
  · intro s m hm
    ext x
    change hom m x = ∑ᶠ i, f s i x
    calc
      hom m x = hom m (∑ᶠ i, e i x) := congrArg (hom m) (hsum x).symm
      _ = ∑ᶠ i, hom m (e i x) := map_finsum _ (hf x)
      _ = ∑ᶠ i, f s i x := finsum_congr fun i =>
        congrArg (fun k => hom k (hom (q i) x)) (hm i)

/-- Orthogonality and exhaustion make the family finite on each vector. -/
theorem finiteSupport_projectors_of_iSup_range_eq_top {ι : Type uI}
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (e : ι → A.representation.IntertwiningMap A.representation)
    (horth : ∀ i j, i ≠ j → ∀ x, e i (e j x) = 0)
    (hspan : (⨆ i, (e i).range) = ⊤) (x : A) :
    Function.HasFiniteSupport (fun i => e i x) := by
  classical
  have hx : x ∈ ⨆ i, (e i).range.toSubmodule := by
    rw [← Subrepresentation.toSubmodule_iSup, hspan]
    trivial
  refine Submodule.iSup_induction _
    (motive := fun x => Function.HasFiniteSupport (fun i => e i x)) hx ?_ ?_ ?_
  · intro j y hy
    obtain ⟨z, rfl⟩ := hy
    apply (Set.finite_singleton j).subset
    intro i hi
    by_contra hij
    exact hi (horth i j hij z)
  · simp only [map_zero]
    exact Function.hasFiniteSupport_fun_zero
  · intro y z hy hz
    apply (hy.union hz).subset
    intro i hi
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    apply hi
    change e i (y + z) = 0
    exact (map_add (e i) y z).trans (by rw [h.1, h.2, add_zero])

/-- Pointwise finiteness and exhaustion imply that the total projector is identity. -/
theorem finsum_projectors_eq_self_of_iSup_range_eq_top {ι : Type uI}
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (e : ι → A.representation.IntertwiningMap A.representation)
    (hf : ∀ x : A, Function.HasFiniteSupport (fun i => e i x))
    (hid : ∀ i x, e i (e i x) = e i x)
    (horth : ∀ i j, i ≠ j → ∀ x, e i (e j x) = 0)
    (hspan : (⨆ i, (e i).range) = ⊤) (x : A) : (∑ᶠ i, e i x) = x := by
  have hx : x ∈ ⨆ i, (e i).range.toSubmodule := by
    rw [← Subrepresentation.toSubmodule_iSup, hspan]
    trivial
  change pointwiseFiniteSum e hf x = x
  refine Submodule.iSup_induction _
    (motive := fun x => pointwiseFiniteSum e hf x = x) hx ?_ (map_zero _) ?_
  · intro i y hy
    obtain ⟨z, rfl⟩ := hy
    exact pointwiseFiniteSum_component e hf hid horth i z
  · intro y z hy hz
    rw [map_add, hy, hz]

end SmoothRep
end Langlands
