import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Lie.SubgroupEqualityProof
import Langlands.GroupScheme.Lie.SubgroupTangent

/-! # Parabolic containment over a field with a specified common maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace RelativeLevi

variable {k : Type u} [Field k]
    {G P Q : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A parabolic containing a specified maximal torus has a dynamic presentation
by a cocharacter of that same torus, over its original field. -/
theorem exists_fixedTorusDynamicPresentation_of_isParabolicSubgroup
    (hG : IsConnectedReductive G) (i : P ⟶ G) (hi : IsParabolicSubgroup i)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) :
    ∃ ν : cocharacterLattice T,
      SubgroupFunctor.range i = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion t.hom.hom.left := ht.2.1
  have : IsAffineHom T.X.hom := by
    rw [← Over.w t.hom.hom]
    infer_instance
  let hrep : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let f := hrep.liftOfLE t hTP
  have hf : f ≫ i = t := hrep.liftOfLE_comp t hTP
  obtain ⟨K, _, _, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k T.toGrp ht.1
  let : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  let b := algebraBaseMap k K
  let F := GroupScheme.baseChange b
  let TK := (CommGroupScheme.baseChange b).obj T
  have hTK : IsSplitTorus TK.toGrp := hsplit
  have hGK : IsConnectedReductive (F.obj G) :=
    connectedReductiveFieldExtensionStatement k K G hG
  have htK : IsMaximalTorus (T := TK) (F.map t) :=
    (maximalTorusBaseChange k K G T t ht.1 ht.2.1).mp ht
  have hiK : IsParabolicSubgroup (F.map i) :=
    parabolicFieldExtensionStatement k K G hG P i hi
  have hfK : F.map f ≫ F.map i = F.map t :=
    (F.map_comp f i).symm.trans (congrArg F.map hf)
  have hclass : SplitParabolicCocharacterStatement.{u} :=
    splitParabolicCocharacterStatement_of_absoluteBorelOvergroup
      borelConjugacy absoluteBorelOvergroupCocharacter maximalTorusBaseChange
  exact (exists_range_eq_parabolic_iff_finiteGaloisBaseChange k K T t i hTK).mpr
    (hclass K (F.obj G) hGK TK (F.map t) hTK htK (F.obj P) (F.map i)
      (F.map f) hiK hfK)

/-- An actual fixed-torus dynamic presentation of a parabolic, chosen from the
published field classification and integral finite-Galois descent. -/
def fixedTorusDynamicPresentationOfParabolic
    (hG : IsConnectedReductive G) (i : P ⟶ G) (hi : IsParabolicSubgroup i)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) :
    FixedTorusDynamicPresentations T t i :=
  ⟨(exists_fixedTorusDynamicPresentation_of_isParabolicSubgroup hG i hi t ht hTP).choose,
    (exists_fixedTorusDynamicPresentation_of_isParabolicSubgroup hG i hi t ht hTP).choose_spec⟩

/-- For field parabolics containing a common specified maximal torus, inclusion
of the actual tangent submodules implies inclusion on every test scheme. -/
theorem parabolic_range_le_of_lie_le [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    (i : P ⟶ G) (j : Q ⟶ G) (hi : IsParabolicSubgroup i) (hj : IsParabolicSubgroup j)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hTQ : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (hlie : (SubgroupFunctor.range j).lie k ≤ (SubgroupFunctor.range i).lie k) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range i := by
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  let νP := fixedTorusDynamicPresentationOfParabolic hG i hi t ht hTP
  let νQ := fixedTorusDynamicPresentationOfParabolic hG j hj t ht hTQ
  have hP := νP.property
  have hQ := νQ.property
  rw [hP, hQ] at hlie ⊢
  refine parabolic_le_parabolic_of_lieKernel dynamicSmooth dynamicConnected
    lieSubgroupEquality _ _ ?_ ?_
  · exact (SubgroupFunctor.range_comp_le _ t).trans (hTQ.trans hQ.le)
  · intro X hX
    exact hlie (show Additive.ofMul X ∈
      (Dynamic.parabolic (CommGroupScheme.groupHom νQ.val ≫ t)).lie k from hX)

/-- The actual inclusion homomorphism obtained from containment of tangent
submodules of parabolics with a common maximal torus. -/
def parabolicContainmentHomOfLieLE [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    (i : P ⟶ G) (j : Q ⟶ G) (hi : IsParabolicSubgroup i) (hj : IsParabolicSubgroup j)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hTQ : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (hlie : (SubgroupFunctor.range j).lie k ≤ (SubgroupFunctor.range i).lie k) : Q ⟶ P := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let hrep : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  exact hrep.liftOfLE j (parabolic_range_le_of_lie_le hG i j hi hj t ht hTP hTQ hlie)

/-- The constructed field containment homomorphism commutes with the ambient
inclusions. -/
theorem parabolicContainmentHomOfLieLE_comp [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    (i : P ⟶ G) (j : Q ⟶ G) (hi : IsParabolicSubgroup i) (hj : IsParabolicSubgroup j)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hTQ : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (hlie : (SubgroupFunctor.range j).lie k ≤ (SubgroupFunctor.range i).lie k) :
    parabolicContainmentHomOfLieLE hG i j hi hj t ht hTP hTQ hlie ≫ i = j :=
  SubgroupFunctor.IsRepresentedBy.liftOfLE_comp _ _
    (parabolic_range_le_of_lie_le hG i j hi hj t ht hTP hTQ hlie)

end RelativeLevi

end Langlands.GroupScheme
