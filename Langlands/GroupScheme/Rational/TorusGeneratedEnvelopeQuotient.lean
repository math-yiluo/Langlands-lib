import Langlands.GroupScheme.Derived.CentralIntersectionPullback
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeCocharacter
import Langlands.GroupScheme.Dynamic.NormalSubgroupProduct
import Langlands.GroupScheme.HomogeneousQuotientRestriction
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.PseudoParabolic

/-! # Restricting supplied quotients to the fixed torus envelope -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorusGeneratedEnvelope

variable {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    (D : TorusGeneratedEnvelope G)

/-- Normality of the fixed envelope makes multiplication by a smooth-quotient
stabilizer containing a dynamic parabolic smooth and scheme-surjective. -/
theorem product_smooth_surjective
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth D.group.X.hom]
    (hn : (SubgroupFunctor.range D.inclusion).IsNormal)
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (hP : ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.parabolic χ ≤ SubgroupFunctor.range i)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q) [Smooth q.left]
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
      a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (SubgroupFunctor.range i).carrier T) :
    Smooth (HomogeneousQuotientRestriction.productMap D.inclusion i).left ∧
      Surjective (HomogeneousQuotientRestriction.productMap D.inclusion i).left := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom P.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : Smooth P.X.hom :=
    HomogeneousQuotient.smooth_subgroup_of_smooth_quotient G P i q hfib
  let : IsAffineHom D.group.X.hom := D.isAffineHom
  obtain ⟨χ, hχP⟩ := hP
  have hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range D.inclusion := by
    intro T x hx
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr
      ⟨z ≫ (D.cocharacterFactor χ).hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, D.cocharacterFactor_comp]
  exact Dynamic.normal_subgroup_product_smooth_surjective
    D.inclusion i χ D.closed hn hχ hχP

/-- Restrict a supplied exact quotient to the fixed envelope, using its actual
intersection with the stabilizer. The target and projection are unchanged and
precomposed with the envelope inclusion, respectively. -/
def restrictQuotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth D.group.X.hom]
    (hn : (SubgroupFunctor.range D.inclusion).IsNormal)
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (hP : ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.parabolic χ ≤ SubgroupFunctor.range i)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
      a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (SubgroupFunctor.range i).carrier T) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient
      (subgroupIntersectionFst D.inclusion i) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have h := D.product_smooth_surjective hn i hi hP q hfib
  let : Smooth (HomogeneousQuotientRestriction.productMap D.inclusion i).left := h.1
  let : Surjective (HomogeneousQuotientRestriction.productMap D.inclusion i).left := h.2
  exact HomogeneousQuotientRestriction.restrict D.inclusion i q hfib D.closed
    (subgroupIntersectionFst D.inclusion i) (range_subgroupIntersectionFst _ _)

/-- For an arbitrary pseudo-parabolic stabilizer, only envelope smoothness and
normality remain structural inputs to restriction of the supplied quotient. -/
def restrictPseudoQuotient
    [Smooth D.group.X.hom]
    (hn : (SubgroupFunctor.range D.inclusion).IsNormal)
    (i : P ⟶ G) (hi : IsPseudoParabolicSubgroup i)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
      a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (SubgroupFunctor.range i).carrier T) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient
      (subgroupIntersectionFst D.inclusion i) := by
  let : Smooth G.X.hom := hi.smooth
  let : IsAffineHom G.X.hom := hi.isAffineHom
  let : ConnectedSpace G.X.left := hi.connectedSpace
  exact D.restrictQuotient hn i hi.isClosedSubgroup hi.exists_cocharacter_le q hfib

theorem restrictPseudoQuotient_scheme
    [Smooth D.group.X.hom]
    (hn : (SubgroupFunctor.range D.inclusion).IsNormal)
    (i : P ⟶ G) (hi : IsPseudoParabolicSubgroup i)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
      a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (SubgroupFunctor.range i).carrier T) :
    (D.restrictPseudoQuotient hn i hi q hfib).scheme = Q := rfl

theorem restrictPseudoQuotient_projection
    [Smooth D.group.X.hom]
    (hn : (SubgroupFunctor.range D.inclusion).IsNormal)
    (i : P ⟶ G) (hi : IsPseudoParabolicSubgroup i)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
      a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (SubgroupFunctor.range i).carrier T) :
    (D.restrictPseudoQuotient hn i hi q hfib).projection = D.inclusion.hom.hom ≫ q :=
  rfl

/-- If the original stabilizer is dynamic, every supplied representative of
the restricted dynamic parabolic gives the same original quotient target. -/
def restrictDynamicQuotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth D.group.X.hom]
    (hn : (SubgroupFunctor.range D.inclusion).IsNormal)
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range i = Dynamic.parabolic χ)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
      a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (SubgroupFunctor.range i).carrier T)
    {K : GroupScheme (Spec (CommRingCat.of k))} (j : K ⟶ D.group)
    (hj : (Dynamic.parabolic (D.cocharacterFactor χ)).IsRepresentedBy j) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient j := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have h := D.product_smooth_surjective hn i hi
    ⟨χ, by rw [hχ]⟩ q hfib
  let : Smooth (HomogeneousQuotientRestriction.productMap D.inclusion i).left := h.1
  let : Surjective (HomogeneousQuotientRestriction.productMap D.inclusion i).left := h.2
  apply HomogeneousQuotientRestriction.restrict D.inclusion i q hfib D.closed j
  rw [hj.2, hχ, D.parabolic_cocharacterFactor χ]

end TorusGeneratedEnvelope

end Langlands.GroupScheme
