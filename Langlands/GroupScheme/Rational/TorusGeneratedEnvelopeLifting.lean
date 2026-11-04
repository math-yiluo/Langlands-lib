import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeQuotient
import Langlands.GroupScheme.Dynamic.FlagQuotientCell
import Langlands.GroupScheme.Dynamic.FlagQuotientDensity
import Langlands.AlgebraicGeometry.PointTopology.RationalDensityStatement

/-! # Dynamic quotient lifting through the fixed torus envelope -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable (k : Type u) [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : P ⟶ G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : (parabolic χ).IsRepresentedBy i)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
      a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (SubgroupFunctor.range i).carrier T)

/-- An actual section of the supplied quotient on an open containing its
identity coset, constructed from the opposite dynamic cell. -/
def parabolicIdentitySection :
    Σ U : Q.left.Opens, {s : openOver k Q U ⟶ G.X //
      Set.range ((1 : RationalPoint k G.X) ≫ q).left ⊆ U ∧
        s ≫ q = openOverι k Q U} := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Mono i.hom.hom := hP.1
  let χopp := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  let iU := Affine.unipotentHom χopp
  have hU := Affine.isRepresentedBy_unipotentHom χopp
  let : IsOpenImmersion (QuotientCell.multiplication i iU.hom.hom).left :=
    oppositeCellStatement k G χ _ _ iU i hU hP
  refine ⟨(flagQuotientCell k i iU q hfib).1,
    (flagQuotientCell k i iU q hfib).2, ?_, flagQuotientCell_comp k i iU q hfib⟩
  have h := range_identity_subset_flagQuotientCell k i iU q hfib
  rw [rationalPointEquiv_left] at h
  exact h

include hP hfib in
/-- Dense rational group points lift every rational point under the supplied
dynamic-parabolic quotient, with its identity section proved by the open cell. -/
theorem rational_lifts_of_dense_parabolic
    (hdense : HasDenseRationalPoints k G.X) :
    ∀ p : RationalPoint k Q, ∃ g : RationalPoint k G.X, g ≫ q = p := by
  let C := parabolicIdentitySection k i χ hP q hfib
  intro p
  obtain ⟨g, hg⟩ := rational_lifts_of_dense_identity_section k G
    (SubgroupFunctor.range i) q hfib hdense C.1 C.2.val C.2.property.1
    C.2.property.2 (rationalPointEquiv k Q p)
  refine ⟨(rationalPointEquiv k G.X).symm g, ?_⟩
  apply (rationalPointEquiv k Q).injective
  rw [rationalPointEquiv_natural, Equiv.apply_symm_apply]
  exact hg

/-- A chosen actual lift for a dynamic-parabolic quotient of a group with
dense rational points. -/
def rationalLiftOfDenseParabolic
    (hdense : HasDenseRationalPoints k G.X) (p : RationalPoint k Q) :
    RationalPoint k G.X :=
  Classical.choose (rational_lifts_of_dense_parabolic k i χ hP q hfib hdense p)

theorem rationalLiftOfDenseParabolic_comp
    (hdense : HasDenseRationalPoints k G.X) (p : RationalPoint k Q) :
    rationalLiftOfDenseParabolic k i χ hP q hfib hdense p ≫ q = p :=
  Classical.choose_spec (rational_lifts_of_dense_parabolic k i χ hP q hfib hdense p)

end Dynamic

namespace TorusGeneratedEnvelope

variable {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (D : TorusGeneratedEnvelope G) [Smooth D.group.X.hom]
    (hn : (SubgroupFunctor.range D.inclusion).IsNormal)
    (hdense : HasDenseRationalPoints k D.group.X)
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range i = Dynamic.parabolic χ)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsSeparated Q.hom] [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
      a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (SubgroupFunctor.range i).carrier T)

include hn hdense hi hχ hfib in
/-- Smoothness, normality and rational density of the fixed torus envelope
give actual lifts under the original dynamic-parabolic quotient. -/
theorem rational_lifts_dynamic :
    ∀ p : RationalPoint k Q, ∃ g : RationalPoint k G.X, g ≫ q = p := by
  let : IsAffineHom D.group.X.hom := D.isAffineHom
  let : IsAffine D.group.X.left := isAffine_of_isAffineHom D.group.X.hom
  let ψ := D.cocharacterFactor χ
  let j := Dynamic.Affine.parabolicHom ψ
  have hj := Dynamic.Affine.isRepresentedBy_parabolicHom ψ
  let E := D.restrictDynamicQuotient hn i hi χ hχ q hfib j hj
  let : Smooth E.projection.left := E.smooth_projection
  let : Surjective E.projection.left := E.surjective_projection
  let : QuasiCompact E.projection.left := E.quasiCompact_projection
  intro p
  obtain ⟨d, hd⟩ := Dynamic.rational_lifts_of_dense_parabolic
    k j ψ hj E.projection E.fibers hdense p
  refine ⟨d ≫ D.inclusion.hom.hom, ?_⟩
  exact (Category.assoc _ _ _).trans hd

/-- A chosen actual lift in the ambient group, under the supplied original
projection, obtained through the fixed torus envelope. -/
def rationalLiftDynamic (p : RationalPoint k Q) : RationalPoint k G.X :=
  Classical.choose (D.rational_lifts_dynamic hn hdense i hi χ hχ q hfib p)

theorem rationalLiftDynamic_comp (p : RationalPoint k Q) :
    D.rationalLiftDynamic hn hdense i hi χ hχ q hfib p ≫ q = p :=
  Classical.choose_spec (D.rational_lifts_dynamic hn hdense i hi χ hχ q hfib p)

end TorusGeneratedEnvelope

end Langlands.GroupScheme
