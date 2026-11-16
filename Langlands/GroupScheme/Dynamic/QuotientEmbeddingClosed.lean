import Langlands.GroupScheme.Dynamic.QuotientEmbedding
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.HomogeneousClosedImmersion
import Langlands.GroupScheme.Absolute.CentralizerProductQuotient
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Closed images of supplied dynamic quotient comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Equivariance

variable {S : Scheme.{u}} {G H : GroupScheme S} (f : G ⟶ H)
  (χ : (Gm S).toGrp ⟶ G)
  {Q R : Over S} (q : G.X ⟶ Q) (r : H.X ⟶ R)
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  [Flat r.left] [Surjective r.left] [QuasiCompact r.left]
  (hq : ∀ (T : Over S) (a b : T ⟶ G.X),
    a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (parabolic χ).carrier T)
  (hr : ∀ (T : Over S) (a b : T ⟶ H.X),
    a ≫ r = b ≫ r ↔ a⁻¹ * b ∈ (parabolic (χ ≫ f)).carrier T)

/-- The actual comparison respects the left actions on both supplied quotients. -/
theorem suppliedQuotientMap_equivariant (T : Over S) (g : T ⟶ G.X) (x : T ⟶ Q) :
    (flagQuotientSchemeAction G (parabolic χ) q hq).act g x ≫
        suppliedQuotientMap f χ q r hq hr =
      ((flagQuotientSchemeAction H (parabolic (χ ≫ f)) r hr).restrict f).act
        g (x ≫ suppliedQuotientMap f χ q r hq hr) := by
  rw [SchemeAction.restrict_act]
  apply HomogeneousQuotientComparison.hom_ext_of_local_lift q x
  intro V a m ham
  rw [← Category.assoc, SchemeAction.naturality, ham]
  rw [flagQuotientSchemeAction_act_lift, Category.assoc, fac_suppliedQuotientMap]
  rw [SchemeAction.naturality, ← Category.assoc a x, ham, Category.assoc,
    fac_suppliedQuotientMap, ← Category.assoc m f.hom.hom r,
    flagQuotientSchemeAction_act_lift]
  rw [← Category.assoc, MonObj.mul_comp, Category.assoc]

omit [Flat r.left] [Surjective r.left] [QuasiCompact r.left] in
/-- The projection identifies the comparison image with the restricted ambient image. -/
theorem range_suppliedQuotientMap :
    Set.range (suppliedQuotientMap f χ q r hq hr).left =
      Set.range (f.hom.hom ≫ r).left := by
  rw [← fac_suppliedQuotientMap f χ q r hq hr, Over.comp_left]
  change Set.range (suppliedQuotientMap f χ q r hq hr).left =
    Set.range ((suppliedQuotientMap f χ q r hq hr).left ∘ q.left)
  rw [Set.range_comp, q.left.surjective.range_eq, Set.image_univ]

end Equivariance

section ClosedImage

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H)
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  {Q R : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q) (r : H.X ⟶ R)
  [Smooth G.X.hom] [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
  [Flat r.left] [Surjective r.left] [QuasiCompact r.left]
  [QuasiCompact Q.hom] [LocallyOfFiniteType R.hom]
  (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
    a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (parabolic χ).carrier T)
  (hr : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ H.X),
    a ≫ r = b ≫ r ↔ a⁻¹ * b ∈ (parabolic (χ ≫ f)).carrier T)

/-- For the actual supplied comparison, a closed topological image suffices
for a closed immersion; no separate immersion hypothesis is required. -/
theorem suppliedQuotientMap_isClosedImmersion_of_closed_range
    (hf : IsClosedSubgroup f)
    (hclosed : IsClosed (Set.range (f.hom.hom ≫ r).left)) :
    IsClosedImmersion (suppliedQuotientMap f χ q r hq hr).left := by
  have hscomp : Smooth (q.left ≫ Q.hom) := by rw [Over.w]; infer_instance
  let : Smooth Q.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp q.left Q.hom
  let : IsReduced Q.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k Q.left Q.hom
  let : Mono (suppliedQuotientMap f χ q r hq hr).left :=
    mono_suppliedQuotientMap f χ q r hq hr hf
  apply HomogeneousClosedImmersion.isClosedImmersion_of_closed_range
    (flagQuotientSchemeAction G (parabolic χ) q hq)
    ((flagQuotientSchemeAction H (parabolic (χ ≫ f)) r hr).restrict f)
    (suppliedQuotientMap f χ q r hq hr)
    (suppliedQuotientMap_equivariant f χ q r hq hr) (1 ≫ q)
  · intro y
    obtain ⟨g, hg⟩ := HomogeneousClosedImmersion.exists_rational_lift q y
      (q.left.surjective (y.left (IsLocalRing.closedPoint k)))
    refine ⟨g, ?_⟩
    rw [flagQuotientSchemeAction_act_lift, mul_one, hg]
  · rwa [range_suppliedQuotientMap]

/-- A closed multiplication image with an ambient represented dynamic
parabolic gives a closed immersion of the supplied quotient comparison. -/
theorem suppliedQuotientMap_isClosedImmersion_of_product_closed
    [Smooth r.left] {P : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ H)
    (hi : (parabolic (χ ≫ f)).IsRepresentedBy i)
    (hf : IsClosedSubgroup f)
    (hclosed : IsClosed (Set.range (CentralizerProduct.productHom f i).left)) :
    IsClosedImmersion (suppliedQuotientMap f χ q r hq hr).left := by
  let : Mono i.hom.hom := hi.1
  apply suppliedQuotientMap_isClosedImmersion_of_closed_range f χ q r hq hr hf
  apply CentralizerProduct.restricted_quotient_range_isClosed f i r _ hclosed
  intro T a b
  rw [hr, hi.2]

/-- The actual closed comparison, with its closed immersion and projection
compatibility, constructed from closedness of the ambient product image. -/
def suppliedClosedQuotientComparison_of_product_closed
    [Smooth r.left] {P : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ H)
    (hi : (parabolic (χ ≫ f)).IsRepresentedBy i)
    (hf : IsClosedSubgroup f)
    (hclosed : IsClosed (Set.range (CentralizerProduct.productHom f i).left)) :
    {m : Q ⟶ R // IsClosedImmersion m.left ∧ q ≫ m = f.hom.hom ≫ r} :=
  ⟨suppliedQuotientMap f χ q r hq hr,
    suppliedQuotientMap_isClosedImmersion_of_product_closed f χ q r hq hr i hi hf hclosed,
    fac_suppliedQuotientMap f χ q r hq hr⟩

include hq hr in
omit [LocallyOfFiniteType R.hom] in
/-- Properness of the ambient quotient and closedness of the actual product
imply properness of the original supplied dynamic quotient. -/
theorem suppliedQuotient_isProper_of_product_closed
    [Smooth r.left] [IsProper R.hom]
    {P : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ H)
    (hi : (parabolic (χ ≫ f)).IsRepresentedBy i)
    (hf : IsClosedSubgroup f)
    (hclosed : IsClosed (Set.range (CentralizerProduct.productHom f i).left)) :
    IsProper Q.hom := by
  let : IsClosedImmersion (suppliedQuotientMap f χ q r hq hr).left :=
    suppliedQuotientMap_isClosedImmersion_of_product_closed f χ q r hq hr i hi hf hclosed
  exact suppliedQuotient_isProper_of_closed_comparison f χ q r hq hr

end ClosedImage

end Langlands.GroupScheme.Dynamic
