import Langlands.GroupScheme.Dynamic.RingSmoothConnectedStatement
import Langlands.GroupScheme.Dynamic.SmoothOverRing
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Smoothness and geometric connectedness of dynamic subgroups over a ring -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Dynamic subgroups of a smooth affine group scheme over an arbitrary ring are smooth.
The unipotent subgroup has geometrically connected fibres; the parabolic and centralizer
subgroups do as well when the ambient group has geometrically connected fibres. -/
theorem dynamicRingSmoothConnected : DynamicRingSmoothConnectedStatement.{u} := by
  intro R _ G _ _ χ H j
  obtain ⟨hP, hZ, hU⟩ := dynamicSmooth_ring R G χ H j
  refine ⟨fun hj => ⟨hU hj, ?_⟩, fun hj => ⟨hP hj, ?_⟩,
    fun hj => ⟨hZ hj, ?_⟩⟩
  · refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
    let Gk := (GroupScheme.baseChange y).obj G
    let Hk := (GroupScheme.baseChange y).obj H
    let jk := (GroupScheme.baseChange y).map j
    let χk := Dynamic.baseChangeCocharacter y χ
    have : Smooth Gk.X.hom := by
      change Smooth (pullback.snd G.X.hom y)
      infer_instance
    have : IsAffineHom Gk.X.hom := by
      change IsAffineHom (pullback.snd G.X.hom y)
      infer_instance
    have hjk : (Dynamic.unipotent χk).IsRepresentedBy jk := by
      rw [Dynamic.unipotent_baseChange]
      exact hj.baseChange y
    exact (dynamicConnected K Gk χk Hk jk).1 hjk
  · intro hG
    refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
    let Gk := (GroupScheme.baseChange y).obj G
    let Hk := (GroupScheme.baseChange y).obj H
    let jk := (GroupScheme.baseChange y).map j
    let χk := Dynamic.baseChangeCocharacter y χ
    have : Smooth Gk.X.hom := by
      change Smooth (pullback.snd G.X.hom y)
      infer_instance
    have : IsAffineHom Gk.X.hom := by
      change IsAffineHom (pullback.snd G.X.hom y)
      infer_instance
    have hGk : ConnectedSpace Gk.X.left :=
      pullback_of_geometrically hG.geometrically_connectedSpace K y
    have hjk : (Dynamic.parabolic χk).IsRepresentedBy jk := by
      rw [Dynamic.parabolic_baseChange]
      exact hj.baseChange y
    exact ((dynamicConnected K Gk χk Hk jk).2 hGk).1 hjk
  · intro hG
    refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
    let Gk := (GroupScheme.baseChange y).obj G
    let Hk := (GroupScheme.baseChange y).obj H
    let jk := (GroupScheme.baseChange y).map j
    let χk := Dynamic.baseChangeCocharacter y χ
    have : Smooth Gk.X.hom := by
      change Smooth (pullback.snd G.X.hom y)
      infer_instance
    have : IsAffineHom Gk.X.hom := by
      change IsAffineHom (pullback.snd G.X.hom y)
      infer_instance
    have hGk : ConnectedSpace Gk.X.left :=
      pullback_of_geometrically hG.geometrically_connectedSpace K y
    have hjk : (Dynamic.centralizer χk).IsRepresentedBy jk := by
      rw [Dynamic.centralizer_baseChange]
      exact hj.baseChange y
    exact ((dynamicConnected K Gk χk Hk jk).2 hGk).2 hjk

end Langlands.GroupScheme
