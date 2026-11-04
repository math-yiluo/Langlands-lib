import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Rational.TorusVectorLiftConjugacy
import Langlands.GroupScheme.Rational.TorusVectorLinearizationStatement
import Langlands.GroupScheme.Rational.VectorGroupDimension
import Langlands.GroupScheme.Rational.VectorGroupUnipotent

/-! # Full maximality through quotients with supplied torus lifts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section General

variable {k : Type u} [Field k]
  {G Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom Q.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i) (q : G ⟶ Q)
  (hclosed : IsClosedSubgroup (i ≫ q))
  (hlift : ∀ (T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (i' : T'.toGrp ⟶ Q), IsTorus T'.toGrp → IsClosedSubgroup i' →
      ∃ j : T'.toGrp ⟶ G, j ≫ q = i')
  (hcompare : ∀ j : T.toGrp ⟶ G, i ≫ q = j ≫ q → SubgroupConjugate i j)

include hi hclosed hlift hcompare in
/-- Full maximality descends if the image is closed, every closed target torus
has a homomorphic lift, and equal-quotient maps from the source are conjugate. -/
theorem IsMaximalTorus.comp_of_torus_lifts : IsMaximalTorus (i ≫ q) := by
  refine ⟨hi.1, hclosed, ?_⟩
  intro T' i' f hT' hi' hf
  obtain ⟨j, hjq⟩ := hlift T' i' hT' hi'
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom :=
    mono_of_mono_fac (congrArg (fun a => a.hom.hom) hjq)
  have : IsAffineHom T'.toGrp.X.hom := by
    rw [← Over.w i'.hom.hom]
    infer_instance
  have hj : IsClosedSubgroup j := hT'.isClosedSubgroup_of_mono j
  have heq : i ≫ q = (f ≫ j) ≫ q := by
    rw [Category.assoc, hjq, hf]
  have hfj : IsMaximalTorus (f ≫ j) :=
    (hcompare (f ≫ j) heq).isMaximalTorus_iff.mp hi
  exact hfj.2.2 T' j f hT' hj rfl

/-- The actual isomorphism to any proposed larger quotient torus, under the
same explicit torus-lifting and equal-map comparison premises. -/
def IsMaximalTorus.quotientFactorIsoOfTorusLifts
    (T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (i' : T'.toGrp ⟶ Q) (f : T.toGrp ⟶ T'.toGrp)
    (hT' : IsTorus T'.toGrp) (hi' : IsClosedSubgroup i')
    (hf : f ≫ i' = i ≫ q) : T.toGrp ≅ T'.toGrp :=
  haveI := (hi.comp_of_torus_lifts q hclosed hlift hcompare).2.2 T' i' f hT' hi' hf
  asIso f

@[simp]
theorem IsMaximalTorus.quotientFactorIsoOfTorusLifts_hom
    (T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (i' : T'.toGrp ⟶ Q) (f : T.toGrp ⟶ T'.toGrp)
    (hT' : IsTorus T'.toGrp) (hi' : IsClosedSubgroup i')
    (hf : f ≫ i' = i ≫ q) :
    (hi.quotientFactorIsoOfTorusLifts q hclosed hlift hcompare T' i' f hT' hi' hf).hom = f :=
  rfl

end General

section VectorKernel

variable {k : Type u} [Field k]
  {N G Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
  (n : N ⟶ G) [Mono n.hom.hom] (q : G ⟶ Q)
  (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))

include hi n hn in
/-- A vector-kernel specialization: intrinsic vector geometry and the supplied
linearization statement discharge closedness and equal-map comparison. Only
closed-subgroup unipotence, linearization and torus lift existence remain explicit. -/
theorem IsMaximalTorus.comp_of_vector_kernel_torus_lifts
    (hsub : UnipotentClosedSubgroupStatement.{u})
    (hlin : RelativeRoot.TorusVectorActionLinearizationStatement.{u})
    {d : ℕ} (hN : RelativeRoot.IsVectorGroupOfDimension N d)
    (hlift : ∀ (T' : CommGroupScheme (Spec (CommRingCat.of k)))
      (i' : T'.toGrp ⟶ Q), IsTorus T'.toGrp → IsClosedSubgroup i' →
        ∃ j : T'.toGrp ⟶ G, j ≫ q = i') :
    IsMaximalTorus (i ≫ q) := by
  have : IsAffineHom N.X.hom := hN.isAffineHom
  have : SmoothOfRelativeDimension d N.X.hom := hN.smoothOfRelativeDimension
  have : Smooth N.X.hom := SmoothOfRelativeDimension.smooth d _
  have hc : IsClosedSubgroup (i ≫ q) :=
    hN.isUnipotent.closed_torus_quotient hsub hi.1 n i hi.2.1 q hn.symm.le
  obtain ⟨e, he⟩ := hlin k T.toGrp N d hi.1 hN (QuotientHomCocycle.action n q hn i)
  apply hi.comp_of_torus_lifts q hc hlift
  intro j hj
  exact QuotientHomCocycle.subgroupConjugate_of_isTorus n q hn i j hj hi.1 e he

end VectorKernel

end Langlands.GroupScheme
