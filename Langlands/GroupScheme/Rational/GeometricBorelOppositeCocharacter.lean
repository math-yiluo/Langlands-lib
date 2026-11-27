import Langlands.GroupScheme.Absolute.FixedTorusGaloisDescent
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Absolute.GeometricBorelBaseChange
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Opposite dynamic Borels over the original field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

variable {k : Type u} [Field k] {G B : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ G}

private theorem regular_of_eq_dynamicParabolic
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t)
    {eta ν : cocharacterLattice T} (hν : IsRegularCocharacter t ν)
    (heq : Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ t) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t)) :
    IsRegularCocharacter t eta := by
  intro α hα hz
  have hn := neg_mem_roots_of_split_maximalTorus hG hT t ht hα
  have hle := RelativeRoot.nonnegative_rootSupport_of_parabolic_le hT t eta ν heq.le
  have hp := hle α ((relativeRoots_eq_roots t).symm ▸ hα) hz.ge
  have hnz : latticePairing T (-α) eta = 0 := by
    rw [map_neg, LinearMap.neg_apply, hz, neg_zero]
  have hq := hle (-α) ((relativeRoots_eq_roots t).symm ▸ hn) hnz.ge
  rw [map_neg, LinearMap.neg_apply] at hq
  exact hν α hα (le_antisymm (neg_nonneg.mp hq) hp)

private theorem isGeometricBorel_of_regular_of_isSplitTorus
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t)
    (ν : cocharacterLattice T) (hν : IsRegularCocharacter t ν) {j : B ⟶ G}
    (hj : IsClosedSubgroup j)
    (hrep : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t)).IsRepresentedBy j) :
    IsGeometricBorelSubgroup j := by
  let : Smooth G.X.hom := hG.smooth
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let C := GroupScheme.baseChange b
  let TK := (CommGroupScheme.baseChange b).obj T
  let νK := cocharacterLattice.baseChange b T ν
  have hGK : IsConnectedReductive (C.obj G) := connectedReductiveFieldExtensionStatement k K G hG
  let : IsAffineHom (C.obj G).X.hom := hGK.isAffineHom
  have htK : IsMaximalTorus (T := TK) (C.map t) :=
    (maximalTorusBaseChange k K G T t ht.1 ht.2.1).mp ht
  have hνK : IsRegularCocharacter (T := TK) (C.map t) νK := by
    intro α hα
    obtain ⟨β, rfl⟩ := (characterLattice.baseChangeEquiv b T hT).surjective α
    have hβ := (mem_roots_baseChange_iff (K := K) G T hT t β).mp hα
    rw [characterLattice.baseChangeEquiv_apply, latticePairing_baseChange]
    exact hν β hβ
  have hc : Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ t) =
      CommGroupScheme.groupHom νK ≫ C.map t := by
    rw [Dynamic.baseChangeCocharacter_comp, ← cocharacterLattice.groupHom_baseChange_dynamic]
  have hK := hrep.baseChange b
  rw [← Dynamic.parabolic_baseChange, hc] at hK
  exact isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure
    ((regularCocharacterBorel K (C.obj G) hGK TK (C.map t) (hT.baseChange b) htK).1
      νK hνK (C.obj B) (C.map j) (hj.baseChange b) hK) hj

variable [IsAffine G.X.left]

/-- A geometric Borel through a maximal torus has a cocharacter in that
torus whose opposite parabolic is again a geometric Borel. Its full
dynamic centralizer is the original torus. -/
theorem IsGeometricBorelSubgroup.exists_oppositeDynamicBorel
    (hG : IsConnectedReductive G) (ht : IsMaximalTorus t)
    {j : B ⟶ G} (hj : IsGeometricBorelSubgroup j) (f : T.toGrp ⟶ B) (hf : f ≫ j = t) :
    ∃ ν : cocharacterLattice T,
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t)).IsRepresentedBy j ∧
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t) = SubgroupFunctor.range t ∧
      IsGeometricBorelSubgroup (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom (-ν) ≫ t)) := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsClosedImmersion t.hom.hom.left := ht.2.1
  let : IsAffineHom T.X.hom := by
    rw [← Over.w t.hom.hom]
    infer_instance
  let : IsClosedImmersion j.hom.hom.left := hj.1.isClosedSubgroup
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  obtain ⟨K, _, _, _, _, hTK⟩ := torusFiniteGaloisSplitting k T.toGrp ht.1
  let : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  let b := algebraBaseMap k K
  let C := GroupScheme.baseChange b
  let TK := (CommGroupScheme.baseChange b).obj T
  have hGK : IsConnectedReductive (C.obj G) := connectedReductiveFieldExtensionStatement k K G hG
  let : Smooth (C.obj G).X.hom := hGK.smooth
  let : IsAffineHom (C.obj G).X.hom := hGK.isAffineHom
  have htK : IsMaximalTorus (T := TK) (C.map t) :=
    (maximalTorusBaseChange k K G T t ht.1 ht.2.1).mp ht
  have hfK : C.map f ≫ C.map j = C.map t := (C.map_comp f j).symm.trans (congrArg C.map hf)
  obtain ⟨eta, heta, hrep⟩ := (regularCocharacterBorel K (C.obj G) hGK TK (C.map t) hTK htK).2.2
    (C.obj B) (C.map j) (C.map f) (hj.baseChange hG b).1 hfK
  obtain ⟨ν, hν⟩ := (exists_range_eq_parabolic_iff_finiteGaloisBaseChange k K T t j hTK).mpr
    ⟨eta, hrep.2⟩
  let νK := cocharacterLattice.baseChange b T ν
  have hνK : IsRegularCocharacter (T := TK) (C.map t) νK :=
    regular_of_eq_dynamicParabolic hGK hTK htK heta
      (((range_eq_parabolic_iff_baseChange (K := K) T t j ν).mp hν).symm.trans hrep.2)
  refine ⟨ν, ⟨inferInstance, hν⟩, ?_, ?_⟩
  · let χ := CommGroupScheme.groupHom ν ≫ t
    let c := Dynamic.Affine.centralizerHom χ
    have hc := Dynamic.Affine.isRepresentedBy_centralizerHom χ
    let : Mono c.hom.hom := hc.1
    let : Mono t.hom.hom := Over.mono_of_mono_left _
    obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc k K
    let : Surjective b := hs
    let : Flat b := hf
    let : QuasiCompact b := hq
    rw [← hc.2]
    apply SubgroupFunctor.range_eq_of_baseChange_eq b c t
    change (SubgroupFunctor.range (Dynamic.Affine.centralizerHom χ)).baseChange b = _
    rw [hc.2, ← Dynamic.centralizer_baseChange,
      Dynamic.baseChangeCocharacter_comp, ← cocharacterLattice.groupHom_baseChange_dynamic,
      ← SubgroupFunctor.range_baseChangeHom]
    exact centralizer_comp_eq_range_of_isRegular (T := TK) hGK hTK (C.map t) htK νK hνK
  · let χ := CommGroupScheme.groupHom (-ν) ≫ t
    let j' := Dynamic.Affine.parabolicHom χ
    have hj' := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
    have hp := (Dynamic.Affine.isRepresentedBy_parabolicHom χ).baseChange b
    have hc : Dynamic.baseChangeCocharacter b χ =
        CommGroupScheme.groupHom (-νK) ≫ C.map t := by
      dsimp only [χ, νK]
      rw [Dynamic.baseChangeCocharacter_comp, ← cocharacterLattice.groupHom_baseChange_dynamic, map_neg]
    rw [← Dynamic.parabolic_baseChange, hc] at hp
    exact IsGeometricBorelSubgroup.of_baseChange (K := K)
      (isGeometricBorel_of_regular_of_isSplitTorus hGK hTK htK (-νK)
        (fun α hα => by simpa only [map_neg, neg_ne_zero] using hνK α hα)
        (hj'.baseChange b) hp) hj'

end Langlands.GroupScheme
