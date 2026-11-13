import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocyclePinning
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleRestriction
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleFinBridge
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleDiagonal

/-! # Diagonal weights for the original Tits data at a finite stage -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

local instance stageWeightsBaseChangeAffine (k L : Type u) [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (d' : GaloisPinningData k L G)
  (t : d'.torus ≅ d.pinning.torus)
  {n : ℕ} {eG : d'.toSplitPinning.base.support ≃ Fin n}
  (c : CoordinatePinnedIso d'.toSplitPinning eG)

/-- The original split torus mapped to last-pivot diagonal coordinates over the stage field. -/
def stageDiagonalMap :
    (CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.splitTorus ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of L))
        (ULift.{u} (SpecialLinear.OffPivot (Fin.last n))) :=
  (CommGroupScheme.baseChange (algebraBaseMap k L)).map (stageTorusMap d d' t) ≫
    c.pinningIso.torusIso.inv ≫ (lastPivotTorusIso n (Spec (CommRingCat.of L))).hom

/-- The individual diagonal characters, descended to the original maximal split torus. -/
def stageDiagonalWeight (i : Fin (n + 1)) : characterLattice d.splitTorus :=
  descendedDiagonalWeight (algebraBaseMap k L) d.splitTorus d.maximalSplit.1.1
    (Fin.last n) (stageDiagonalMap d d' t c) i

section Roots

variable [Algebra L (SeparableClosure k)]
  (hc : algebraBaseMap L (SeparableClosure k) ≫ algebraBaseMap k L =
    algebraBaseMap k (SeparableClosure k))
  (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.pinning.toSplitPinning.rootDatum)
  (he : ∀ χ, e.weightMap χ =
    StarActionFiniteStage.stageCharacter (algebraBaseMap k L)
      (algebraBaseMap L (SeparableClosure k)) t (algebraBaseMap k (SeparableClosure k)) hc χ)

include hc he

/-- The corresponding original simple-root restriction is a difference of descended weights. -/
theorem rootRestriction_stageDiagonalWeight_sub (i : Fin n) :
    d.rootRestriction (e.indexEquiv (eG.symm i).val) =
      stageDiagonalWeight d d' t c i.castSucc - stageDiagonalWeight d d' t c i.succ := by
  apply eq_descendedDiagonalWeight_sub (algebraBaseMap k L) d.splitTorus
    d.maximalSplit.1.1 (Fin.last n) (stageDiagonalMap d d' t c)
  rw [baseChange_rootRestriction_stage d d' t hc e he]
  have hr : c.pinningIso.torusIso.hom ≫ d'.rootDatum.root (eG.symm i).val =
      (lastPivotTorusIso n (Spec (CommRingCat.of L))).hom ≫
        (SpecialLinear.diagonalWeight (Fin.last n) (Spec (CommRingCat.of L)) i.castSucc -
          SpecialLinear.diagonalWeight (Fin.last n) (Spec (CommRingCat.of L)) i.succ) :=
    (c.simpleRoot_pullback i).trans
      (fin_rootChar_eq_lastPivot n L i.castSucc i.succ)
  calc
    _ = ((CommGroupScheme.baseChange (algebraBaseMap k L)).map (stageTorusMap d d' t) ≫
          c.pinningIso.torusIso.inv) ≫
        (c.pinningIso.torusIso.hom ≫ d'.rootDatum.root (eG.symm i).val) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = _ := by
      rw [hr]
      rfl

/-- Matching the finite-stage numbering recovers the exact simple-root clause for `d`. -/
theorem numbered_rootRestriction_stageDiagonalWeight_sub (e₀ : d.Vertex ≃ Fin n)
    (hindex : ∀ i : Fin n, e.indexEquiv (eG.symm i).val = (e₀.symm i).val)
    (i : Fin n) :
    d.rootRestriction (e₀.symm i).val =
      stageDiagonalWeight d d' t c i.castSucc - stageDiagonalWeight d d' t c i.succ := by
  rw [← hindex i]
  exact rootRestriction_stageDiagonalWeight_sub d d' t c hc e he i

end Roots

section Diagonal

variable
  (hi : CommGroupScheme.groupHom t.hom ≫ d.pinning.inclusion = d'.inclusion)

include hi

/-- The pinning square factors the original split inclusion through the diagonal torus. -/
theorem stageDiagonalMap_factorization :
    (GroupScheme.baseChange (algebraBaseMap k L)).map d.splitInclusion ≫
        c.pinningIso.groupIso.inv =
      CommGroupScheme.groupHom (stageDiagonalMap d d' t c) ≫
        SpecialLinear.diagonalTorus (Fin.last n) (CommRingCat.of L) := by
  have hs := stageTorusMap_square d d' t hi
  have hbase := congrArg ((GroupScheme.baseChange (algebraBaseMap k L)).map) hs
  have hinv :
      (GroupScheme.baseChange (algebraBaseMap k L)).map d'.inclusion ≫
          c.pinningIso.groupIso.inv =
        CommGroupScheme.groupHom c.pinningIso.torusIso.inv ≫
          SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of L) :=
    torusTransport_inverse_square c.pinningIso.torusIso c.pinningIso.groupIso
      c.pinningIso.square
  rw [Functor.map_comp] at hbase
  rw [← hbase, Category.assoc, hinv]
  change
    CommGroupScheme.groupHom
        ((CommGroupScheme.baseChange (algebraBaseMap k L)).map (stageTorusMap d d' t) ≫
          c.pinningIso.torusIso.inv) ≫
        SpecialLinear.FinSucc.diagonalTorus n (CommRingCat.of L) = _
  rw [fin_diagonalTorus_eq_lastPivot]
  rfl

/-- A local presentation with the coordinate pinned group isomorphism has the required
diagonal formula on every original relative test. -/
theorem diagonal_stageDiagonalWeight
    (E : LocalGroupIso
      (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k)) G
      (Over.mk (algebraBaseMap k L)))
    (hE : E.toBaseChangeIso.hom =
      (SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap k L)).hom ≫
        c.pinningIso.groupIso.hom)
    (Z : Over (Spec (CommRingCat.of k))) (a : Z ⟶ Over.mk (algebraBaseMap k L))
    (s : Z ⟶ d.splitTorus.X) :
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of k) Z
        ((E.toFun a).symm (s ≫ d.splitInclusion.hom.hom)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      Matrix.diagonal fun i =>
        ((Gm.pointsEquiv _ Z
          (s ≫ (CommGroupScheme.groupHom (stageDiagonalWeight d d' t c i)).hom.hom) :
          Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
  apply diagonal_of_baseChangeFactorization (algebraBaseMap k L) d.splitTorus
    d.maximalSplit.1.1 (Fin.last n) (stageDiagonalMap d d' t c) E d.splitInclusion
  have hE' : E.toBaseChangeIso.inv ≫
      (SpecialLinear.baseChangeModelIso (Fin (n + 1)) (algebraBaseMap k L)).hom =
        c.pinningIso.groupIso.inv := by
    apply (cancel_mono c.pinningIso.groupIso.hom).1
    rw [Category.assoc, ← hE, Iso.inv_hom_id, Iso.inv_hom_id]
  rw [hE']
  exact stageDiagonalMap_factorization d d' t c hi

end Diagonal

end Langlands.GroupScheme.SpecialLinearTitsCocycle
