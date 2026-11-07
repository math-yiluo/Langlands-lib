import Langlands.GroupScheme.Rational.KernelCentralizerComponentReductiveStatement
import Langlands.GroupScheme.Rational.KernelCentralizerBaseChange
import Langlands.GroupScheme.Rational.KernelCentralizerClassical
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Reductive.ToPseudoReductive

/-! # Reductivity of full character-kernel centralizer identity components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeRoot

/-- The identity component of any smooth closed representative of the centralizer
of a full nonzero split-torus character kernel is connected reductive. -/
theorem kernelCentralizerComponentReductive :
    KernelCentralizerComponentReductiveStatement.{u} := by
  intro k _ G hG S hS i a ha C j hj hclosed hC
  let : Smooth C.X.hom := hC
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsClosedImmersion j.hom.hom.left := hclosed
  let : IsAffineHom C.X.hom := hclosed.isAffineHom
  change IsConnectedReductive (identityComponent C)
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  let : Smooth (F.obj C).X.hom :=
    IdentityComponent.smooth_baseChange C (algebraMap k (AlgebraicClosure k))
  let : IsAffineHom (F.obj C).X.hom :=
    IdentityComponent.isAffineHom_baseChange C (algebraMap k (AlgebraicClosure k))
  have haK : characterLattice.baseChange b S a ≠ 0 := by
    intro h
    apply ha
    apply (hS.characterLattice_baseChange_bijective b S).injective
    simpa only [map_zero] using h
  have hCK : IsConnectedReductive (identityComponent (F.obj C)) :=
    isConnectedReductive_kernelCentralizer_identityComponent_isAlgClosed
      (F.obj G) hG.baseChange_toAlgebraicClosure
      ((CommGroupScheme.baseChange b).obj S) (IsSplitTorus.baseChange b hS)
      (F.map i) (characterLattice.baseChange b S a) haK
      (F.obj C) (F.map j)
      (kernelCentralizer_isRepresentedBy_baseChange b i a hj) (hclosed.baseChange b)
  exact ⟨inferInstance, inferInstance, inferInstance,
    HasTrivialUnipotentRadical.of_iso
      (IdentityComponent.baseChangeIso C (algebraMap k (AlgebraicClosure k)))
      hCK.hasTrivialUnipotentRadical⟩

end Langlands.GroupScheme.RelativeRoot
