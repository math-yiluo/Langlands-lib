import Langlands.GroupScheme.Absolute.CentralizerProductTransporter
import Langlands.GroupScheme.Dynamic.FlagQuotientAction
import Langlands.GroupScheme.HomogeneousQuotientComparison
import Langlands.GroupScheme.SubgroupIntersection
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The actual intersection quotient inside an ambient homogeneous quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralizerProduct

variable {S : Scheme.{u}} {M B G : GroupScheme S}
variable (j : M ⟶ G) (b : B ⟶ G) {Q : Over S} (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier T)

include hfib

/-- Restriction of an exact ambient quotient has precisely the intersection cosets
as its fibers on every relative test scheme. -/
theorem intersection_quotient_fibers [Mono j.hom.hom]
    (T : Over S) (m n : T ⟶ M.X) :
    m ≫ j.hom.hom ≫ q = n ≫ j.hom.hom ≫ q ↔
      m⁻¹ * n ∈ (SubgroupFunctor.range (subgroupIntersectionFst j b)).carrier T := by
  rw [← Category.assoc m, ← Category.assoc n, hfib]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp h
    have he : (m⁻¹ * n) ≫ j.hom.hom = x ≫ b.hom.hom := by
      rw [MonObj.mul_comp, GrpObj.inv_comp]
      exact hx.symm
    exact SubgroupFunctor.mem_range.mpr
      ⟨(subgroupIntersection_isPullback j b).lift (m⁻¹ * n) x he,
        (subgroupIntersection_isPullback j b).lift_fst _ _ _⟩
  · intro h
    obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp h
    refine SubgroupFunctor.mem_range.mpr
      ⟨x ≫ (subgroupIntersectionSnd j b).hom.hom, ?_⟩
    rw [Category.assoc, ← (subgroupIntersection_isPullback j b).w,
      ← Category.assoc, hx, MonObj.mul_comp, GrpObj.inv_comp]

/-- Exact ambient coset fibers identify the product with the actual pullback of
the ambient quotient along its restriction to the subgroup. -/
theorem product_quotient_isPullback [Mono b.hom.hom] :
    IsPullback (fst M.X B.X) (productHom j b) (j.hom.hom ≫ q) q := by
  have hw : fst M.X B.X ≫ j.hom.hom ≫ q = productHom j b ≫ q := by
    have ht : (fst M.X B.X ≫ j.hom.hom) ≫ q = productHom j b ≫ q := by
      apply (hfib _ _ _).mpr
      change (fst M.X B.X ≫ j.hom.hom)⁻¹ *
        ((fst M.X B.X ≫ j.hom.hom) * (snd M.X B.X ≫ b.hom.hom)) ∈ _
      rw [inv_mul_cancel_left]
      exact SubgroupFunctor.mem_range.mpr ⟨snd M.X B.X, rfl⟩
    simpa only [Category.assoc] using ht
  have hex (c : PullbackCone (j.hom.hom ≫ q) q) :
      ∃ x : c.pt ⟶ B.X,
        x ≫ b.hom.hom = (c.fst ≫ j.hom.hom)⁻¹ * c.snd :=
    SubgroupFunctor.mem_range.mp
      ((hfib _ (c.fst ≫ j.hom.hom) c.snd).mp
        (by simpa only [Category.assoc] using c.condition))
  let k (c : PullbackCone (j.hom.hom ≫ q) q) : c.pt ⟶ B.X :=
    (hex c).choose
  have hk (c : PullbackCone (j.hom.hom ≫ q) q) :
      k c ≫ b.hom.hom = (c.fst ≫ j.hom.hom)⁻¹ * c.snd :=
    (hex c).choose_spec
  refine ⟨⟨by simpa only [Category.assoc] using hw⟩,
    ⟨PullbackCone.IsLimit.mk _
      (fun c => lift c.fst (k c)) ?_ ?_ ?_⟩⟩
  · intro c
    exact lift_fst _ _
  · intro c
    rw [lift_productHom, hk, mul_inv_cancel_left]
  · intro c a ha₁ ha₂
    apply hom_ext
    · simp only [lift_fst]
      exact ha₁
    · apply (cancel_mono b.hom.hom).mp
      simp only [lift_snd]
      have he : a ≫ productHom j b =
          (a ≫ fst M.X B.X ≫ j.hom.hom) *
            (a ≫ snd M.X B.X ≫ b.hom.hom) := by
        simp only [productHom, SubgroupFunctor.cellMultiplication, MonObj.comp_mul]
      rw [he, ← Category.assoc a (fst M.X B.X), ha₁] at ha₂
      rw [hk, ← ha₂, inv_mul_cancel_left]
      exact Category.assoc _ _ _

omit hfib in
/-- A scheme pullback carries the exact inverse-image identity for its projection range. -/
theorem range_eq_preimage_of_isPullback
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {c : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a c f g) :
    Set.range c = g ⁻¹' Set.range f := by
  calc
    Set.range c = g ⁻¹' (f '' Set.univ) := by
      simpa only [Set.preimage_univ, Set.image_univ] using
        (Scheme.image_preimage_eq_of_isPullback h Set.univ)
    _ = g ⁻¹' Set.range f := by rw [Set.image_univ]

/-- The actual product image is the inverse image of the restricted quotient image. -/
theorem product_range_eq_preimage [Mono b.hom.hom] :
    Set.range (productHom j b).left =
      q.left ⁻¹' Set.range (j.hom.hom ≫ q).left :=
  range_eq_preimage_of_isPullback
    ((product_quotient_isPullback j b q hfib).map (Over.forget S))

/-- Closedness of the product descends to closedness of the restricted quotient image
along a surjective smooth ambient quotient. -/
theorem restricted_quotient_range_isClosed [Mono b.hom.hom]
    [Smooth q.left] [Surjective q.left]
    (hclosed : IsClosed (Set.range (productHom j b).left)) :
    IsClosed (Set.range (j.hom.hom ≫ q).left) := by
  rw [product_range_eq_preimage j b q hfib] at hclosed
  exact ((q.left.isOpenMap.isQuotientMap q.left.continuous
    q.left.surjective).isClosed_preimage).mp hclosed

variable {R : Over S} (r : M.X ⟶ R)
variable (hrfib : ∀ (T : Over S) (m n : T ⟶ M.X),
  m ≫ r = n ≫ r ↔
    m⁻¹ * n ∈ (SubgroupFunctor.range (subgroupIntersectionFst j b)).carrier T)
variable [Mono j.hom.hom] [Flat r.left] [Surjective r.left] [QuasiCompact r.left]

include hrfib

/-- The actual morphism from the intersection quotient to the ambient quotient. -/
def intersectionQuotientMap : R ⟶ Q :=
  HomogeneousQuotientComparison.desc r (j.hom.hom ≫ q)
    (fun T m n h => (intersection_quotient_fibers j b q hfib T m n).mpr
      ((hrfib T m n).mp h))

@[reassoc]
theorem comp_intersectionQuotientMap :
    r ≫ intersectionQuotientMap j b q hfib r hrfib = j.hom.hom ≫ q :=
  HomogeneousQuotientComparison.fac_desc _ _ _

/-- Equality of quotient points can be tested after two fpqc local lifts. The exact
restricted fibers then make the quotient comparison a monomorphism. -/
theorem intersectionQuotientMap_mono :
    Mono (intersectionQuotientMap j b q hfib r hrfib) := by
  constructor
  intro T x y hxy
  apply Dynamic.flagQuotient_hom_ext_of_local_lift M r x
  intro V a m ham
  apply Dynamic.flagQuotient_hom_ext_of_local_lift M r (a ≫ y)
  intro W d n hdn
  have he : (d ≫ m) ≫ j.hom.hom ≫ q = n ≫ j.hom.hom ≫ q := by
    have he' :
        ((d ≫ m) ≫ r) ≫ intersectionQuotientMap j b q hfib r hrfib =
          (n ≫ r) ≫ intersectionQuotientMap j b q hfib r hrfib := by
      calc
        _ = (d ≫ (a ≫ x)) ≫ intersectionQuotientMap j b q hfib r hrfib := by
          rw [Category.assoc d m r, ← ham]
        _ = (d ≫ a ≫ y) ≫ intersectionQuotientMap j b q hfib r hrfib := by
          simpa only [Category.assoc] using congrArg (fun z => d ≫ a ≫ z) hxy
        _ = _ := by rw [hdn]
    simpa only [Category.assoc, comp_intersectionQuotientMap] using he'
  have hr : (d ≫ m) ≫ r = n ≫ r :=
    (hrfib _ _ _).mpr ((intersection_quotient_fibers j b q hfib _ _ _).mp he)
  simpa only [Category.assoc, ham, hdn] using hr

/-- Surjectivity of the intersection quotient identifies its comparison image with
the image of the restricted ambient quotient. -/
theorem range_intersectionQuotientMap :
    Set.range (intersectionQuotientMap j b q hfib r hrfib).left =
      Set.range (j.hom.hom ≫ q).left := by
  rw [← comp_intersectionQuotientMap j b q hfib r hrfib, Over.comp_left]
  change Set.range (intersectionQuotientMap j b q hfib r hrfib).left =
    Set.range ((intersectionQuotientMap j b q hfib r hrfib).left ∘ r.left)
  rw [Set.range_comp, r.left.surjective.range_eq, Set.image_univ]

/-- Product closedness gives a closed image for the actual quotient comparison. -/
theorem intersectionQuotientMap_range_isClosed [Mono b.hom.hom]
    [Smooth q.left] [Surjective q.left]
    (hclosed : IsClosed (Set.range (productHom j b).left)) :
    IsClosed (Set.range (intersectionQuotientMap j b q hfib r hrfib).left) := by
  rw [range_intersectionQuotientMap j b q hfib r hrfib]
  exact restricted_quotient_range_isClosed j b q hfib hclosed

/-- Once the remaining immersion property is supplied, product closedness makes
the quotient comparison an actual closed immersion. -/
theorem intersectionQuotientMap_isClosedImmersion [Mono b.hom.hom]
    [Smooth q.left] [Surjective q.left]
    [IsImmersion (intersectionQuotientMap j b q hfib r hrfib).left]
    (hclosed : IsClosed (Set.range (productHom j b).left)) :
    IsClosedImmersion (intersectionQuotientMap j b q hfib r hrfib).left :=
  IsClosedImmersion.of_isPreimmersion _
    (intersectionQuotientMap_range_isClosed j b q hfib r hrfib hclosed)

/-- An ambient proper quotient makes the intersection quotient proper, conditional
on the immersion input and closedness of the actual product. -/
theorem intersection_quotient_isProper [Mono b.hom.hom]
    [Smooth q.left] [Surjective q.left] [IsProper Q.hom]
    [IsImmersion (intersectionQuotientMap j b q hfib r hrfib).left]
    (hclosed : IsClosed (Set.range (productHom j b).left)) :
    IsProper R.hom := by
  let : IsClosedImmersion (intersectionQuotientMap j b q hfib r hrfib).left :=
    intersectionQuotientMap_isClosedImmersion j b q hfib r hrfib hclosed
  rw [← Over.w (intersectionQuotientMap j b q hfib r hrfib)]
  infer_instance

end Langlands.GroupScheme.CentralizerProduct
