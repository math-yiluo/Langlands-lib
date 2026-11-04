import Langlands.GroupScheme.Cartan.LieGeneration
import Langlands.GroupScheme.Lie.ElementCentralizerRepresentability
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSmoothStatement
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSpanningStatement

/-! # The semisimple-centralizer step of Cartan generation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

namespace Lie

/-- Semisimplicity together with proper actual tangent centralizer. -/
def IsNoncentralSemisimpleElement (X : lieKernel G k) : Prop :=
  IsSemisimpleElement G X ∧ elementCentralizerLie G X ≠ ⊤

end Lie

set_option maxHeartbeats 1000000 in
/-- The centralizers of noncentral semisimple elements supply the induction
step once their smoothness, tangent spanning and maximal-torus preservation
have been established. -/
theorem isGeneratedByCartanSubgroups_of_semisimpleCentralizers
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hsmooth : Lie.SemisimpleCentralizerSmoothStatement.{u})
    (hspan : (⨆ (X : lieKernel G k) (_ : Lie.IsSemisimpleElement G X)
      (_ : Lie.elementCentralizerLie G X ≠ ⊤), Lie.elementCentralizerLie G X) = ⊤)
    (hind : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → IsGeneratedByCartanSubgroups H)
    (htori : ∀ (X : lieKernel G k), Lie.IsSemisimpleElement G X →
      ∀ (C : GroupScheme (Spec (CommRingCat.of k)))
        [Smooth C.X.hom] [IsAffineHom C.X.hom] (j : C ⟶ G),
      (Lie.elementCentralizer G X).IsRepresentedBy j → IsClosedSubgroup j →
        PreservesMaximalTori (identityComponentι C ≫ j)) :
    IsGeneratedByCartanSubgroups G := by
  classical
  let J := {X : lieKernel G k // Lie.IsNoncentralSemisimpleElement X}
  have hex : ∀ t : J, ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (j : C ⟶ G),
      (Lie.elementCentralizer G t.val).IsRepresentedBy j ∧ IsClosedSubgroup j :=
    fun t => Lie.elementCentralizer_isClosedRepresentable G t.val
  choose C j hrep hclosed using hex
  have hsmC : ∀ t : J, Smooth (C t).X.hom :=
    fun t => hsmooth k G t.val t.property.1 (C t) (j t) (hrep t) (hclosed t)
  let : ∀ t : J, Smooth (C t).X.hom := hsmC
  have haffC : ∀ t : J, IsAffineHom (C t).X.hom := by
    intro t
    let : IsClosedImmersion (j t).hom.hom.left := hclosed t
    rw [← Over.w (j t).hom.hom]
    infer_instance
  let : ∀ t : J, IsAffineHom (C t).X.hom := haffC
  let A : J → GroupScheme (Spec (CommRingCat.of k)) := fun t => identityComponent (C t)
  let : ∀ t : J, IsAffineHom (A t).X.hom :=
    fun t => IdentityComponent.isAffineHom_identityComponent (C t)
  let : ∀ t : J, Smooth (A t).X.hom :=
    fun t => IdentityComponent.smooth_identityComponent (C t)
  let : ∀ t : J, ConnectedSpace (A t).X.left :=
    fun t => IdentityComponent.connectedSpace_identityComponent (C t)
  let : ∀ t : J, CommGroup (lieKernel (A t) k) :=
    fun t => lieKernelCommGroup (A t)
  let : ∀ t : J, Module k (Additive (lieKernel (A t) k)) :=
    fun t => lieKernelModule (A t)
  let a : ∀ t, A t ⟶ G := fun t => identityComponentι (C t) ≫ j t
  have hrange : ∀ t : J, LinearMap.range (Lie.targetMapLinear (a t) k) =
      Lie.elementCentralizerLie G t.val := by
    intro t
    exact ((hrep t).lie_eq_range_identityComponent k).symm
  apply isGeneratedByCartanSubgroups_of_lieSpanningFamily A a
  · intro t
    exact IdentityComponent.smooth_identityComponent (C t)
  · intro t
    exact IdentityComponent.connectedSpace_identityComponent (C t)
  · intro t
    exact (IdentityComponent.isClosedSubgroup_identityComponentι (C t)).comp (hclosed t)
  · unfold LieSpanningFamily
    apply top_unique
    refine le_trans (le_of_eq hspan.symm) ?_
    refine iSup_le fun (X : lieKernel G k) => ?_
    refine iSup_le fun (hX : Lie.IsSemisimpleElement G X) => ?_
    refine iSup_le fun (hproper : Lie.elementCentralizerLie G X ≠ ⊤) => ?_
    exact le_iSup_of_le (⟨X, hX, hproper⟩ : J) (by rw [hrange])
  · intro t
    apply hind (A t)
    exact Lie.dimension_identityComponent_lt_of_lie_ne_top
      (hrep t) (hclosed t) t.property.2
  · intro t
    exact htori t.val t.property.1 (C t) (j t) (hrep t) (hclosed t)

/-- The published spanning target supplies the preceding step from the
existence of a geometric noncentral semisimple element. -/
theorem isGeneratedByCartanSubgroups_of_geometricSemisimpleElement
    [Infinite k] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hsmooth : Lie.SemisimpleCentralizerSmoothStatement.{u})
    (hspanning : Lie.SemisimpleCentralizerSpanningStatement.{u})
    (hgeo : ∃ X : lieKernel ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)
        (AlgebraicClosure k),
      Lie.IsSemisimpleElement ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G) X ∧
      Lie.elementCentralizerLie ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G) X ≠ ⊤)
    (hind : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → IsGeneratedByCartanSubgroups H)
    (htori : ∀ (X : lieKernel G k), Lie.IsSemisimpleElement G X →
      ∀ (C : GroupScheme (Spec (CommRingCat.of k)))
        [Smooth C.X.hom] [IsAffineHom C.X.hom] (j : C ⟶ G),
      (Lie.elementCentralizer G X).IsRepresentedBy j → IsClosedSubgroup j →
        PreservesMaximalTori (identityComponentι C ≫ j)) :
    IsGeneratedByCartanSubgroups G :=
  isGeneratedByCartanSubgroups_of_semisimpleCentralizers hsmooth
    (hspanning k G hgeo).2 hind htori

end Langlands.GroupScheme
