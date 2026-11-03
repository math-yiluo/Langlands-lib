import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Torus.FiniteHomRigidity
import Langlands.GroupScheme.Torus.ImageStatement
import Langlands.GroupScheme.ImageGenerationDominant
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Finite-hom maximality from closed torus images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- Closed-torus image factorizations imply reflection of maximal tori along finite maps. -/
def FiniteHomMaximalTorusReflectionReductionStatement : Prop :=
  TorusImageClosedTorusStatement.{u} →
    ∀ (k : Type u) [Field k]
      (G H : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G → IsConnectedReductive H →
      ∀ (π : G ⟶ H), IsFinite π.hom.hom.left →
      ∀ (T S : CommGroupScheme (Spec (CommRingCat.of k)))
        (j : T.toGrp ⟶ G) (i : S.toGrp ⟶ H) (f : T ⟶ S),
        IsTorus T.toGrp → IsClosedSubgroup j → IsMaximalTorus i →
        Surjective (CommGroupScheme.groupHom f).hom.hom.left →
        j ≫ π = CommGroupScheme.groupHom f ≫ i →
        IsMaximalTorus j

/-- The only structural input is the existence of closed torus images. The finite-map
step uses integral incomparability, so no rank comparison or separability is needed. -/
theorem finiteHomMaximalTorusReflection_of_torusImage :
    FiniteHomMaximalTorusReflectionReductionStatement.{u} := by
  intro hImage k _ G H hG hH π hπ T S j i f hT hj hi hsurj hcomm
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : Smooth H.X.hom := hH.smooth
  let : IsFinite π.hom.hom.left := hπ
  let g := CommGroupScheme.groupHom f
  let : Surjective g.hom.hom.left := hsurj
  let : IsIntegral S.toGrp.X.left := hi.1.isIntegral
  let : IsSchemeTheoreticallyDominant g.hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  refine ⟨hT, hj, ?_⟩
  intro M m a hM hm ha
  obtain ⟨Z, z, p, hZ, hz, hp⟩ := hImage k H M.toGrp hM (m ≫ π)
  let : IsClosedImmersion z.hom.hom.left := hz
  let : Mono z.hom.hom := Over.mono_of_mono_left _
  have he : g.hom.hom ≫ i.hom.hom = (a ≫ p).hom.hom ≫ z.hom.hom := by
    change (g ≫ i).hom.hom = ((a ≫ p) ≫ z).hom.hom
    rw [Category.assoc, hp, ← Category.assoc, ha, hcomm]
  obtain ⟨s, hs⟩ := exists_over_factor_of_schematic_precomp
    z.hom.hom g.hom.hom i.hom.hom (a ≫ p).hom.hom he
  let hzrep : (SubgroupFunctor.range z).IsRepresentedBy z := ⟨inferInstance, rfl⟩
  have hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range z := by
    intro U x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply SubgroupFunctor.mem_range.mpr
    exact ⟨t ≫ s, by rw [Category.assoc, hs]⟩
  let b := hzrep.factorHom i hle
  have hb : b ≫ z = i := hzrep.factorHom_comp i hle
  let : IsIso b := hi.2.2 Z z b hZ hz hb
  let q : M.toGrp ⟶ S.toGrp := p ≫ inv b
  have hq : q ≫ i = m ≫ π := by
    dsimp [q]
    rw [← hb, Category.assoc, IsIso.inv_hom_id_assoc, hp]
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have haq : a ≫ q = g := by
    apply Grp.hom_ext
    apply (cancel_mono i.hom.hom).mp
    change ((a ≫ q) ≫ i).hom.hom = (g ≫ i).hom.hom
    rw [Category.assoc, hq, ← Category.assoc, ha, hcomm]
  let : IsClosedImmersion m.hom.hom.left := hm
  have hqf : IsFinite q.hom.hom.left := by
    have heq : q.hom.hom.left ≫ i.hom.hom.left = m.hom.hom.left ≫ π.hom.hom.left :=
      congrArg (fun t => t.hom.hom.left) hq
    have : IsFinite (q.hom.hom.left ≫ i.hom.hom.left) := by
      rw [heq]
      infer_instance
    exact IsFinite.of_comp _ i.hom.hom.left
  let : IsFinite q.hom.hom.left := hqf
  have hac : IsClosedSubgroup a := IsClosedSubgroup.of_comp hm (by rw [ha]; exact hj)
  let : IsClosedImmersion a.hom.hom.left := hac
  let : IsAffineHom M.toGrp.X.hom := hm.isAffineHom
  let : IsAffineHom S.toGrp.X.hom := hi.2.1.isAffineHom
  let : IsAffine M.toGrp.X.left := isAffine_of_isAffineHom M.toGrp.X.hom
  let : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
  let : IsIntegral M.toGrp.X.left := hM.isIntegral
  have hschem : IsSchemeTheoreticallyDominant
      (a.hom.hom.left ≫ q.hom.hom.left) := by
    change IsSchemeTheoreticallyDominant (a ≫ q).hom.hom.left
    rw [haq]
    infer_instance
  let : IsSchemeTheoreticallyDominant
      (a.hom.hom.left ≫ q.hom.hom.left) := hschem
  let : IsIso a.hom.hom.left :=
    isIso_of_closedImmersion_finite_comp_schematic a.hom.hom.left q.hom.hom.left
  let : IsIso a.hom.hom :=
    (isIso_iff_of_reflects_iso _ (Over.forget _)).mp
      (show IsIso a.hom.hom.left from inferInstance)
  let : IsIso a.hom :=
    (isIso_iff_of_reflects_iso _ (Mon.forget _)).mp
      (show IsIso a.hom.hom from inferInstance)
  exact (isIso_iff_of_reflects_iso _ (Grp.forget₂Mon _)).mp
    (show IsIso a.hom from inferInstance)

end Langlands.GroupScheme
