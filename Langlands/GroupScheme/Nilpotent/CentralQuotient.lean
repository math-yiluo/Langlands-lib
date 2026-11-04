import Langlands.GroupScheme.Nilpotent.TorusDescent
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.CentralMaximalQuotientProof
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Absolute.QuotientNormalizer

/-! # Actual quotients by central maximal tori in nilpotent groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- Geometric nilpotence passes through a surjective homomorphism locally
of finite type, by lifting points over the algebraic closure. -/
theorem IsNilpotentGroupScheme.map_of_surjective
    (hG : IsNilpotentGroupScheme G) (q : G ⟶ Q)
    [LocallyOfFiniteType q.hom.hom.left] [Surjective q.hom.hom.left] :
    IsNilpotentGroupScheme Q := by
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  have : LocallyOfFiniteType (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) b q.hom.hom inferInstance
  have : Surjective (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  let : Group.IsNilpotent
      ↑((yonedaGrp.obj (B.obj G)).obj
        (op (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))))) := hG
  exact Group.nilpotent_of_surjective
    (((yonedaGrp.map (B.map q)).app
      (op (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))))).hom)
    (rationalPoints_surjective (B.map q))

/-- An actual central maximal torus and its smooth connected affine quotient.
The quotient is geometrically nilpotent and receives only trivial torus
homomorphisms. Unipotence of the quotient is not a field of these data. -/
structure NilpotentCentralTorusQuotientData
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ G
  quotient : GroupScheme (Spec (CommRingCat.of k))
  projection : G ⟶ quotient
  maximal_torus : IsMaximalTorus inclusion
  central : IsCentral inclusion
  smooth_quotient : Smooth quotient.X.hom
  affine_quotient : IsAffineHom quotient.X.hom
  connected_quotient : ConnectedSpace quotient.X.left
  smooth_projection : Smooth projection.hom.hom.left
  fppf_quotient : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range inclusion) projection
  nilpotent_quotient : IsNilpotentGroupScheme quotient
  no_tori : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
    ∀ g : T.toGrp ⟶ quotient, SubgroupFunctor.range g = ⊥

/-- Choose a maximal torus over the original field and its actual affine
quotient. No assertion about maximal tori after field extension is used. -/
def IsNilpotentGroupScheme.centralTorusQuotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsNilpotentGroupScheme G) : NilpotentCentralTorusQuotientData G :=
  Classical.choice (by
    obtain ⟨T, i, hi⟩ := maximalTorusExistence k G
    have hc := hG.isCentral_of_isTorus T hi.1 i
    obtain ⟨Q, q, hs, ha, hq⟩ :=
      normalSubgroupQuotient k G T.toGrp i hi.2.1 hc.range_isNormal
    let : Smooth Q.X.hom := hs
    let : IsAffineHom Q.X.hom := ha
    let : IsClosedImmersion i.hom.hom.left := hi.2.1
    have hr : (SubgroupFunctor.range i).IsRepresentedBy i :=
      ⟨Over.mono_of_mono_left _, rfl⟩
    have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
    let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
    let : Surjective q.hom.hom.left := hq.2.1
    let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
    exact ⟨{
      torus := T
      inclusion := i
      quotient := Q
      projection := q
      maximal_torus := hi
      central := hc
      smooth_quotient := hs
      affine_quotient := ha
      connected_quotient := hq.connectedSpace
      smooth_projection := hq.smooth_of_smooth_kernel hr hi.1.smooth
      fppf_quotient := hq
      nilpotent_quotient := hG.map_of_surjective q
      no_tori := centralMaximalTorusQuotientStatement k G T i hc hi Q q hq }⟩)

end Langlands.GroupScheme
