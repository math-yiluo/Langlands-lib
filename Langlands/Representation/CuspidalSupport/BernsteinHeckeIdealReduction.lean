import Langlands.Representation.Hecke.CentralIdealDirectSum
import Langlands.Representation.Hecke.DecompositionIdealEquivalence
import Langlands.Representation.CuspidalSupport.BernsteinCentralProjectorReduction

/-! # Renard VI.7.4 reduced to the actual Bernstein decomposition -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open Langlands.Aubert.General.RationalPointFamily
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- The Hecke ideal and block-module assertions of VI.7.4 follow from actual decomposition. -/
theorem bernsteinHeckeIdealDecomposition_of_decomposition
    (h : BernsteinDecompositionStatement.{uF,max uF uV}) :
    BernsteinHeckeIdealDecompositionStatement.{uF,uV} := by
  intro F _ _ _ _ G _ _ T i ν
  let : TopologicalSpace (rationalPoints G) := pointTopology
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space F := by
    let := IsTopologicalAddGroup.rightUniformSpace F
    have := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  intro _ _ family _ _ haar _ hl e hid hzero
  classical
  let hd := h F G T i ν family
  have heq : e = SmoothRep.centralProjector hd := by
    funext s
    exact SmoothRep.centralProjector_unique hd s (e s) (hid s)
      (fun t ht V hV => hzero s t ht.symm V hV)
  subst e
  have hiso : ∀ s {V W : SmoothRep.{0,uF,max uF uV} ℂ (rationalPoints G)},
      bernsteinBlockProperty i ν family s V → (V ≅ W) →
        bernsteinBlockProperty i ν family s W := by
    intro s V W hV E
    exact bernsteinBlockProperty_of_iso hV E.symm
  refine ⟨fun s => Hecke.centralIdeal.{uF,uV} haar hl (SmoothRep.centralProjector hd s),
    ?_, ?_, ?_, ?_⟩
  · intro s a
    exact Hecke.mem_centralIdeal_iff_regular haar hl (SmoothRep.centralProjector hd s)
      (SmoothRep.centralProjector_idempotent hd s) a
  · intro s a b hb
    exact Hecke.centralIdeal_twoSided haar hl (SmoothRep.centralProjector hd s) a b hb
  · exact Hecke.decomposition_centralIdeals_isInternal haar hl hd
  · intro s
    exact ⟨Hecke.decompositionIdealEquivalence haar hl hd hiso s,
      ⟨Hecke.decompositionIdealEquivalence_comparison haar hl hd hiso s⟩⟩

/-- Both VI.7.4 assertions follow from the decomposition in the two carrier universes used. -/
theorem bernsteinCentralIdempotentStatements_of_decomposition
    (hsmall : BernsteinDecompositionStatement.{uF,uV})
    (hlarge : BernsteinDecompositionStatement.{uF,max uF uV}) :
    BernsteinCentralIdempotentStatements.{uF,uV} :=
  ⟨bernsteinCentralIdempotent_of_decomposition hsmall,
    bernsteinHeckeIdealDecomposition_of_decomposition hlarge⟩

end Langlands.CuspidalSupport
