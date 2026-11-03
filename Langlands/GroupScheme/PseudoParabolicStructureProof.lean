import Langlands.GroupScheme.PseudoParabolicGeometry
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # Assembly of the pseudo-parabolic structure theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace IsPseudoParabolicSubgroup

variable {k : Type u} [Field k]
variable {G P : GroupScheme (Spec (CommRingCat.of k))} {i : P ⟶ G}

/-- Connectedness of the supplied pseudo-parabolic source, using dynamic
parabolic connectedness. -/
theorem source_connectedSpace (hi : IsPseudoParabolicSubgroup i) :
    ConnectedSpace P.X.left := by
  let : Smooth G.X.hom := hi.smooth
  let : IsAffineHom G.X.hom := hi.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨U, j, χ, hj, hprod⟩ := hi.presentation
  let H := Dynamic.Affine.parabolicScheme χ
  let h := Dynamic.Affine.parabolicHom χ
  have hH : (Dynamic.parabolic χ).IsRepresentedBy h :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ
  let : IsClosedImmersion h.hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have hU : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let : IsAffineHom H.X.hom := by
    rw [← h.hom.hom.w]
    infer_instance
  let : IsAffineHom U.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  let : Smooth H.X.hom := (dynamicSmooth k G χ H h).1 hH
  let : Smooth U.X.hom := hj.smooth
  let : ConnectedSpace H.X.left := (dynamicConnected k G χ H h).2 hi.connectedSpace |>.1 hH
  let : ConnectedSpace U.X.left := hj.connectedSpace
  exact hprod.connectedSpace hH hU

end IsPseudoParabolicSubgroup

/-- Over every field, the source of a pseudo-parabolic inclusion into a smooth
connected affine group scheme is smooth, connected and affine. -/
theorem pseudoParabolicSubgroupStructure : PseudoParabolicSubgroupStructureStatement.{u} := by
  intro k _ G P _ _ _ i hi
  exact ⟨hi.source_smooth, hi.source_connectedSpace, hi.source_isAffineHom⟩

end Langlands.GroupScheme
