import Langlands.GroupScheme.Reductive.StarActionFiniteStageTorus
import Langlands.GroupScheme.Reductive.TitsIndex

/-! # Finite-stage restrictions of the original Tits roots -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace StarActionFiniteStage

section Tower

variable {B SL SK : Scheme.{u}} (bL : SL ⟶ B) (j : SK ⟶ SL)

/-- The tower character map commutes with pullback along an original torus morphism. -/
theorem towerCharacter_precomp {T U : CommGroupScheme B} (f : T ⟶ U)
    (χ : characterLattice ((CommGroupScheme.baseChange bL).obj U)) :
    towerCharacter bL j T ((CommGroupScheme.baseChange bL).map f ≫ χ) =
      (CommGroupScheme.baseChange (j ≫ bL)).map f ≫ towerCharacter bL j U χ := by
  unfold towerCharacter
  rw [characterLattice.baseChange_precomp]
  have h :
      (CommGroupScheme.baseChange (j ≫ bL)).map f ≫ (towerIso bL j U).hom =
        (towerIso bL j T).hom ≫
          (CommGroupScheme.baseChange j).map ((CommGroupScheme.baseChange bL).map f) :=
    congrArg Additive.ofMul
      (baseChangeCompIso_hom_naturality bL j (CommGroupScheme.groupHom f))
  rw [← Category.assoc, ← h, Category.assoc]

/-- Successive character base changes agree with direct base change through the tower. -/
theorem towerCharacter_baseChange (T : CommGroupScheme B) (χ : characterLattice T) :
    towerCharacter bL j T (characterLattice.baseChange bL T χ) =
      characterLattice.baseChange (j ≫ bL) T χ := by
  apply characterLattice.ext_points
  intro V y
  change Gm.pointsEquiv SK V
      (y ≫ (CommGroupScheme.groupHom
        ((towerIso bL j T).hom ≫
          characterLattice.baseChange j _ (characterLattice.baseChange bL T χ))).hom.hom) = _
  rw [comp_groupHom_comp, characterLattice_baseChange_points,
    characterLattice_baseChange_points, characterLattice_baseChange_points]
  change Gm.pointsEquiv B ((Over.map bL).obj ((Over.map j).obj V))
      (baseChangePointsEquiv bL T.toGrp ((Over.map j).obj V)
        (baseChangePointsEquiv j ((Over.pullback bL).mapGrp.obj T.toGrp) V
          (y ≫ (baseChangeCompIso bL j T.toGrp).hom.hom.hom)) ≫
        (CommGroupScheme.groupHom χ).hom.hom) = _
  rw [baseChangePointsEquiv_base_comp]
  have hy :
      (y ≫ (baseChangeCompIso bL j T.toGrp).hom.hom.hom) ≫
        (baseChangeCompIso bL j T.toGrp).inv.hom.hom = y := by
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id]
    exact Category.comp_id y
  rw [hy, Category.assoc, Gm.pointsEquiv_naturality]
  change Units.map (𝟙 V.left : V.left ⟶ V.left).appTop.hom.toMonoidHom _ = _
  simp

variable (bK : SK ⟶ B) (hc : j ≫ bL = bK)

/-- Precomposition coherence also holds along an equality of the structure maps. -/
theorem towerCharacterOf_precomp {T U : CommGroupScheme B} (f : T ⟶ U)
    (χ : characterLattice ((CommGroupScheme.baseChange bL).obj U)) :
    towerCharacterOf bL j T bK hc ((CommGroupScheme.baseChange bL).map f ≫ χ) =
      (CommGroupScheme.baseChange bK).map f ≫ towerCharacterOf bL j U bK hc χ := by
  subst hc
  simpa only [towerCharacterOf, towerCharacter, towerIsoOf, eqToIso_refl, Iso.refl_trans]
    using towerCharacter_precomp bL j f χ

/-- A ground-field character has its direct base change as its tower image. -/
theorem towerCharacterOf_baseChange (T : CommGroupScheme B) (χ : characterLattice T) :
    towerCharacterOf bL j T bK hc (characterLattice.baseChange bL T χ) =
      characterLattice.baseChange bK T χ := by
  subst hc
  simpa only [towerCharacterOf, towerCharacter, towerIsoOf, eqToIso_refl, Iso.refl_trans]
    using towerCharacter_baseChange bL j T χ

end Tower

end StarActionFiniteStage

namespace SpecialLinearTitsCocycle

section Restriction

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (d' : GaloisPinningData k L G)
  (t : d'.torus ≅ d.pinning.torus)

/-- The original maximal split torus mapped into the identified finite-stage torus. -/
def stageTorusMap : d.splitTorus ⟶ d'.torus :=
  d.torusMap ≫ t.inv

/-- The finite-stage torus map retains the original split inclusion. -/
theorem stageTorusMap_square
    (hi : CommGroupScheme.groupHom t.hom ≫ d.pinning.inclusion = d'.inclusion) :
    CommGroupScheme.groupHom (stageTorusMap d d' t) ≫ d'.inclusion = d.splitInclusion := by
  have h : stageTorusMap d d' t ≫ t.hom = d.torusMap := by
    simp [stageTorusMap]
  calc
    CommGroupScheme.groupHom (stageTorusMap d d' t) ≫ d'.inclusion =
        (CommGroupScheme.groupHom (stageTorusMap d d' t) ≫
          CommGroupScheme.groupHom t.hom) ≫ d.pinning.inclusion := by
      rw [Category.assoc, hi]
    _ = CommGroupScheme.groupHom d.torusMap ≫ d.pinning.inclusion :=
      congrArg (fun f => CommGroupScheme.groupHom f ≫ d.pinning.inclusion) h
    _ = d.splitInclusion := d.square

variable [Algebra L (SeparableClosure k)]
  (hc : algebraBaseMap L (SeparableClosure k) ≫ algebraBaseMap k L =
    algebraBaseMap k (SeparableClosure k))
  (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.pinning.toSplitPinning.rootDatum)
  (he : ∀ χ, e.weightMap χ =
    StarActionFiniteStage.stageCharacter (algebraBaseMap k L)
      (algebraBaseMap L (SeparableClosure k)) t (algebraBaseMap k (SeparableClosure k)) hc χ)

include hc he

/-- Restricting the corresponding finite-stage root gives the scalar extension of the
original Tits root restriction. -/
theorem baseChange_rootRestriction_stage (a : d'.rootIndex) :
    characterLattice.baseChange (algebraBaseMap k L) d.splitTorus
        (d.rootRestriction (e.indexEquiv a)) =
      (CommGroupScheme.baseChange (algebraBaseMap k L)).map (stageTorusMap d d' t) ≫
        d'.rootDatum.root a := by
  have hr : d.pinning.rootDatum.root (e.indexEquiv a) =
      StarActionFiniteStage.stageCharacter (algebraBaseMap k L)
        (algebraBaseMap L (SeparableClosure k)) t
        (algebraBaseMap k (SeparableClosure k)) hc (d'.rootDatum.root a) :=
    (e.root_weightMap_apply d'.rootDatum d.pinning.rootDatum a).symm.trans (he _)
  have ht :
      StarActionFiniteStage.towerCharacterOf (algebraBaseMap k L)
          (algebraBaseMap L (SeparableClosure k)) d.splitTorus
          (algebraBaseMap k (SeparableClosure k)) hc
          (characterLattice.baseChange (algebraBaseMap k L) d.splitTorus
            (d.rootRestriction (e.indexEquiv a))) =
        StarActionFiniteStage.towerCharacterOf (algebraBaseMap k L)
          (algebraBaseMap L (SeparableClosure k)) d.splitTorus
          (algebraBaseMap k (SeparableClosure k)) hc
          ((CommGroupScheme.baseChange (algebraBaseMap k L)).map (stageTorusMap d d' t) ≫
            d'.rootDatum.root a) := by
    rw [StarActionFiniteStage.towerCharacterOf_baseChange]
    calc
      characterLattice.baseChange (algebraBaseMap k (SeparableClosure k)) d.splitTorus
          (d.rootRestriction (e.indexEquiv a)) =
          (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map
            d.torusMap ≫ d.pinning.rootDatum.root (e.indexEquiv a) :=
        (characterLattice.baseChangeEquiv (algebraBaseMap k (SeparableClosure k))
          d.splitTorus d.maximalSplit.1.1).apply_symm_apply _
      _ = (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map
            d.torusMap ≫ StarActionFiniteStage.stageCharacter (algebraBaseMap k L)
              (algebraBaseMap L (SeparableClosure k)) t
              (algebraBaseMap k (SeparableClosure k)) hc (d'.rootDatum.root a) := by rw [hr]
      _ = _ := by
        simpa only [StarActionFiniteStage.stageCharacter, stageTorusMap, Functor.map_comp,
          Category.assoc] using
          (StarActionFiniteStage.towerCharacterOf_precomp (algebraBaseMap k L)
            (algebraBaseMap L (SeparableClosure k))
            (algebraBaseMap k (SeparableClosure k)) hc d.torusMap
            ((CommGroupScheme.baseChange (algebraBaseMap k L)).map t.inv ≫
              d'.rootDatum.root a)).symm
  apply (characterLattice.baseChangeEquiv (algebraBaseMap L (SeparableClosure k))
    ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.splitTorus)
    (d.maximalSplit.1.1.baseChange (algebraBaseMap k L))).injective
  exact (cancel_epi (StarActionFiniteStage.towerIsoOf (algebraBaseMap k L)
    (algebraBaseMap L (SeparableClosure k)) d.splitTorus
    (algebraBaseMap k (SeparableClosure k)) hc).hom).1 ht

end Restriction

end SpecialLinearTitsCocycle

end Langlands.GroupScheme
