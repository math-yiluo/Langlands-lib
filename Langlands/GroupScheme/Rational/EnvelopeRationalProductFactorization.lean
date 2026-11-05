import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeNormalityReduction
import Langlands.GroupScheme.Rational.TorusUnipotentLiftConjugacy
import Langlands.GroupScheme.Rational.TorusVectorLinearizationProof
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof

/-! # Rational product factorization from torus maps in the envelope -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorusGeneratedEnvelope

variable {k : Type u} [Field k]
    {G N V : GroupScheme (Spec (CommRingCat.of k))}
    {Q : CommGroupScheme (Spec (CommRingCat.of k))}
    (D : TorusGeneratedEnvelope G)

/-- The original torus-map lift conjugated by the induced envelope
isomorphism of a rational ambient inner automorphism. -/
def rationalConjugateLift (sH : Q.toGrp ⟶ D.group)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) : Q.toGrp ⟶ D.group :=
  sH ≫ (D.isoOver D (G.innerIso g)).hom

/-- The lift recovers the actual rational conjugation in the ambient group. -/
theorem rationalConjugateLift_comp (sH : Q.toGrp ⟶ D.group)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    D.rationalConjugateLift sH g ≫ D.inclusion =
      (sH ≫ D.inclusion) ≫ (G.innerIso g).hom := by
  rw [rationalConjugateLift, Category.assoc, isoOver_hom_comp, Category.assoc]

/-- Conjugation by a rational kernel point does not change the quotient map
of the envelope lift. -/
theorem rationalConjugateLift_comp_quotient
    (n : N ⟶ G) (q : G ⟶ Q.toGrp) (hnq : n ≫ q = 0)
    (sH : Q.toGrp ⟶ D.group)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X) :
    D.rationalConjugateLift sH (u ≫ n.hom.hom) ≫ (D.inclusion ≫ q) =
      sH ≫ (D.inclusion ≫ q) := by
  have huq : (u ≫ n.hom.hom) ≫ q.hom.hom = 1 := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hnq]
    exact MonObj.comp_one u
  rw [← Category.assoc, rationalConjugateLift_comp, Category.assoc,
    innerIso_hom_comp, huq, innerIso_one_hom, Category.comp_id, Category.assoc]

section KernelCorrection

variable
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    [Smooth V.X.hom] [IsAffineHom V.X.hom] [ConnectedSpace V.X.left]
    (v : V ⟶ D.group) [Mono v.hom.hom]
    (hV : IsUnipotent V) (hVsplit : RelativeRoot.IsSplitUnipotent V)
    (n : N ⟶ G) (q : G ⟶ Q.toGrp) (hnq : n ≫ q = 0)
    (hqV : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range v) (D.inclusion ≫ q))
    (sH : Q.toGrp ⟶ D.group) (hQ : IsTorus Q.toGrp)

/-- A rational point of the supplied envelope kernel that corrects
conjugation of the torus map by a rational ambient kernel point. -/
def rationalTorusKernelCorrection
    (u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X :=
  QuotientHomCocycle.splitUnipotentTorusConjugator hstable
    RelativeRoot.torusVectorActionLinearization splitUnipotentAffineTorsorStatement
    v (D.inclusion ≫ q) hqV.2.2.2.symm hV hVsplit
    sH (D.rationalConjugateLift sH (u ≫ n.hom.hom))
    (D.rationalConjugateLift_comp_quotient n q hnq sH u).symm hQ

/-- The correction conjugates the original homomorphisms themselves,
without changing their source parametrization. -/
theorem rationalTorusKernelCorrection_conjugates
    (u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X) :
    sH ≫ (D.group.innerIso
      (D.rationalTorusKernelCorrection hstable v hV hVsplit n q hnq hqV sH hQ u ≫
        v.hom.hom)).hom = D.rationalConjugateLift sH (u ≫ n.hom.hom) := by
  exact QuotientHomCocycle.splitUnipotentTorusConjugator_conjugates hstable
    RelativeRoot.torusVectorActionLinearization splitUnipotentAffineTorsorStatement
    v (D.inclusion ≫ q) hqV.2.2.2.symm hV hVsplit
    sH (D.rationalConjugateLift sH (u ≫ n.hom.hom))
    (D.rationalConjugateLift_comp_quotient n q hnq sH u).symm hQ

include hstable hV hVsplit hnq hqV hQ in
/-- If the envelope kernel embeds into the ambient kernel and the latter's
torus centralizer is represented, every rational ambient kernel point is a
product of a rational envelope-kernel point and a rational centralizer point. -/
theorem rationalPoints_mul_surjective
    {C : GroupScheme (Spec (CommRingCat.of k))}
    [Mono n.hom.hom]
    (m : V ⟶ N) (hm : m ≫ n = v ≫ D.inclusion)
    (c : C ⟶ N)
    (hc : ((torusCentralizer (sH ≫ D.inclusion)).comap n).IsRepresentedBy c)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X) :
    ∃ w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X,
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X,
      (w ≫ m.hom.hom) * (z ≫ c.hom.hom) = u := by
  let w := D.rationalTorusKernelCorrection hstable v hV hVsplit n q hnq hqV sH hQ u
  let a := w ≫ m.hom.hom
  let b := a⁻¹ * u
  have ha : a ≫ n.hom.hom = (w ≫ v.hom.hom) ≫ D.inclusion.hom.hom := by
    change (w ≫ m.hom.hom) ≫ n.hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, hm, Grp.comp_hom_hom, Category.assoc]
  have hconj : (sH ≫ D.inclusion) ≫ (G.innerIso (a ≫ n.hom.hom)).hom =
      (sH ≫ D.inclusion) ≫ (G.innerIso (u ≫ n.hom.hom)).hom := by
    have h := congrArg (fun f : Q.toGrp ⟶ D.group => f ≫ D.inclusion)
      (D.rationalTorusKernelCorrection_conjugates
        hstable v hV hVsplit n q hnq hqV sH hQ u)
    rw [Category.assoc, innerIso_hom_comp, ← Category.assoc,
      rationalConjugateLift_comp] at h
    simpa only [w, ha] using h
  have hb : b ∈ ((torusCentralizer (sH ≫ D.inclusion)).comap n).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [SubgroupFunctor.mem_comap, mem_torusCentralizer_base_iff]
    change (sH ≫ D.inclusion) ≫ (G.innerIso ((a⁻¹ * u) ≫ n.hom.hom)).hom = _
    rw [MonObj.mul_comp, GrpObj.inv_comp, innerIso_mul_hom,
      ← Category.assoc, ← hconj, Category.assoc, innerIso_inv_hom,
      Iso.hom_inv_id, Category.comp_id]
  rw [← hc.2] at hb
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hb
  refine ⟨w, z, ?_⟩
  rw [hz]
  exact mul_inv_cancel_left a u

end KernelCorrection

end TorusGeneratedEnvelope

end Langlands.GroupScheme
