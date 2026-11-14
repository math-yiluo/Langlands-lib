import Langlands.GroupScheme.SubgroupFunctor.FpqcMembership
import Langlands.GroupScheme.InnerAutomorphism

/-! # Conjugating subgroup functors by a point on a test scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}
  {F F' F'' : SubgroupFunctor G} {T U : Over S} {g h : U ⟶ G.X}

/-- A point conjugates `F` to `F'` when it identifies membership after every
refinement of its test scheme. -/
def IsConjugatingPoint (F F' : SubgroupFunctor G) (g : U ⟶ G.X) : Prop :=
  ∀ (V : Over S) (a : V ⟶ U) (x : V ⟶ G.X),
    x ∈ F.carrier V ↔ (a ≫ g) * x * (a ≫ g)⁻¹ ∈ F'.carrier V

/-- The same point continues to conjugate after restriction. -/
theorem IsConjugatingPoint.restrict (hg : IsConjugatingPoint F F' g) (a : T ⟶ U) :
    IsConjugatingPoint F F' (a ≫ g) := by
  intro V b x
  simpa only [Category.assoc] using hg V (b ≫ a) x

/-- Inverting a point reverses its subgroup conjugacy. -/
theorem IsConjugatingPoint.inv (hg : IsConjugatingPoint F F' g) :
    IsConjugatingPoint F' F g⁻¹ := by
  intro V a x
  rw [GrpObj.comp_inv, inv_inv]
  have he : (a ≫ g) * ((a ≫ g)⁻¹ * x * (a ≫ g)) * (a ≫ g)⁻¹ = x := by group
  have hp := hg V a ((a ≫ g)⁻¹ * x * (a ≫ g))
  rw [he] at hp
  exact hp.symm

/-- Successive conjugacies compose in the order of actual conjugation. -/
theorem IsConjugatingPoint.trans {h : U ⟶ G.X}
    (hg : IsConjugatingPoint F F' g) (hh : IsConjugatingPoint F' F'' h) :
    IsConjugatingPoint F F'' (h * g) := by
  intro V a x
  rw [MonObj.comp_mul, mul_inv_rev]
  simpa only [mul_assoc] using (hg V a x).trans (hh V a ((a ≫ g) * x * (a ≫ g)⁻¹))

/-- A point conjugates a subgroup functor to itself precisely when it normalizes
that functor on all refinements. -/
theorem isConjugatingPoint_self_iff :
    IsConjugatingPoint F F g ↔ g ∈ F.normalizer.carrier U := by
  constructor
  · intro hg V a x hx
    refine ⟨(hg V a x).mp hx, ?_⟩
    simpa only [GrpObj.comp_inv, inv_inv] using (hg.inv V a x).mp hx
  · intro hg V a x
    constructor
    · exact fun hx => (hg V a x hx).1
    · intro hx
      have hp := (hg V a ((a ≫ g) * x * (a ≫ g)⁻¹) hx).2
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hp

/-- Two conjugators for the same subgroup functors differ on the right by a
point of the full normalizer of the source subgroup. -/
theorem IsConjugatingPoint.inv_mul_mem_normalizer
    (hg : IsConjugatingPoint F F' g) (hh : IsConjugatingPoint F F' h) :
    g⁻¹ * h ∈ F.normalizer.carrier U :=
  isConjugatingPoint_self_iff.mp (hh.trans hg.inv)

/-- Right correction by a normalizer point preserves subgroup conjugacy. -/
theorem IsConjugatingPoint.mul_of_mem_normalizer
    (hg : IsConjugatingPoint F F' g) (hh : h ∈ F.normalizer.carrier U) :
    IsConjugatingPoint F F' (g * h) :=
  (isConjugatingPoint_self_iff.mpr hh).trans hg

/-- Conjugacy of subgroup functors descends along an fpqc cover of the test
scheme when membership in both subgroup functors descends. -/
theorem IsConjugatingPoint.of_cover
    (hF : HasFpqcMembershipDescent F) (hF' : HasFpqcMembershipDescent F')
    (q : T ⟶ U) [QuasiCompact q.left] [Flat q.left] [Surjective q.left]
    (hg : IsConjugatingPoint F F' (q ≫ g)) :
    IsConjugatingPoint F F' g := by
  intro V a x
  let Z : Over S := Over.mk (pullback.fst a.left q.left ≫ V.hom)
  let r : Z ⟶ V := Over.homMk (pullback.fst a.left q.left) rfl
  let b : Z ⟶ T := Over.homMk (pullback.snd a.left q.left) (by
    rw [← Over.w q, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w a]
    rfl)
  have hr : r ≫ a = b ≫ q := Over.OverMorphism.ext pullback.condition
  have : QuasiCompact r.left := by
    change QuasiCompact (pullback.fst a.left q.left)
    infer_instance
  have : Flat r.left := by
    change Flat (pullback.fst a.left q.left)
    infer_instance
  have : Surjective r.left := by
    change Surjective (pullback.fst a.left q.left)
    infer_instance
  have he : r ≫ ((a ≫ g) * x * (a ≫ g)⁻¹) =
      (b ≫ q ≫ g) * (r ≫ x) * (b ≫ q ≫ g)⁻¹ := by
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hr]
  constructor
  · intro hx
    apply hF' r
    rw [he]
    exact (hg Z b (r ≫ x)).mp (F.comp_mem r hx)
  · intro hx
    apply hF r
    apply (hg Z b (r ≫ x)).mpr
    rw [← he]
    exact F'.comp_mem r hx

section BaseChange

variable {S' : Scheme.{u}} (b : S' ⟶ S)

/-- A conjugating point remains conjugating after arbitrary base change, with
the new point specified through the actual pullback-point equivalence. -/
theorem IsConjugatingPoint.baseChange (hg : IsConjugatingPoint F F' g)
    {V : Over S'} (a : (Over.map b).obj V ⟶ U)
    (g' : V ⟶ ((GroupScheme.baseChange b).obj G).X)
    (he : baseChangePointsEquiv b G V g' = a ≫ g) :
    IsConjugatingPoint (F.baseChange b) (F'.baseChange b) g' := by
  intro W c x
  change baseChangePointsEquiv b G W x ∈ F.carrier _ ↔
    baseChangePointsEquiv b G W ((c ≫ g') * x * (c ≫ g')⁻¹) ∈ F'.carrier _
  rw [map_mul, map_mul, map_inv, baseChangePointsEquiv_naturality, he]
  simpa only [Category.assoc] using
    hg ((Over.map b).obj W) ((Over.map b).map c ≫ a) (baseChangePointsEquiv b G W x)

end BaseChange

end Langlands.GroupScheme.SubgroupFunctor
