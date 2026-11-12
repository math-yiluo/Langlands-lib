import Langlands.GroupScheme.Reductive.StarActionQuasiSplitStatement
import Langlands.GroupScheme.Reductive.StarActionQuasiSplitRoots
import Langlands.GroupScheme.Reductive.StarActionQuasiSplitBorel
import Langlands.GroupScheme.Reductive.AbsoluteStarAction
import Langlands.GroupScheme.Reductive.RegularCocharacterPinning
import Langlands.GroupScheme.Reductive.RootDatumGaloisSimpleRoots
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Absolute.BorelMaximalTorusProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusReduction

/-! # The star action of a quasi-split group is the natural action: proof -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

namespace StarActionQuasiSplit

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A geometric Borel subgroup of a connected reductive group contains a maximal torus of the
ambient group defined over the ground field. -/
theorem exists_isMaximalTorus_comp_of_isGeometricBorel (hG : IsConnectedReductive G)
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G} (hb : IsGeometricBorelSubgroup b) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ B),
      IsMaximalTorus (t ≫ b) := by
  have := hG.smooth
  have := hG.isAffineHom
  have : IsAffineHom B.X.hom := BorelFieldExtension.isAffineHom_source hb.1.isClosedSubgroup
  have : Smooth B.X.hom := hb.1.smooth
  let bc := GroupScheme.baseChange (toAlgebraicClosure k)
  have : Smooth (bc.obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have : IsAffineHom (bc.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have : ConnectedSpace (bc.obj G).X.left := hG.connectedSpace_toAlgebraicClosure
  obtain ⟨Tbar, jbar, hpair⟩ :=
    borelMaximalTorus (AlgebraicClosure k) (bc.obj G) (bc.obj B) (bc.map b) hb.2
  obtain ⟨f, hf⟩ := hpair.2.2
  exact exists_isMaximalTorus_comp_of_geometric maximalTorusExistence maximalTorusBaseChange
    maximalTorusConjugacy k B G b hb.1.isClosedSubgroup hb.2.connectedSpace
    ⟨Tbar, f, by rw [hf]; exact hpair.2.1⟩

end StarActionQuasiSplit

open StarActionQuasiSplit in
/-- Milne 2022, Proposition 25.28(a), direction "quasi-split implies natural action". -/
theorem starActionQuasiSplit : StarActionQuasiSplitStatement.{u} := by
  intro k _ G _ _ hqs
  have hG := hqs.isConnectedReductive
  have := hG.smooth
  obtain ⟨B, b, hb⟩ := hqs.exists_isGeometricBorelSubgroup
  obtain ⟨T, t, hj⟩ := exists_isMaximalTorus_comp_of_isGeometricBorel hG hb
  have : IsAffineHom B.X.hom := BorelFieldExtension.isAffineHom_source hb.1.isClosedSubgroup
  let E := SeparableClosure k
  let s := algebraBaseMap k E
  let bcG := GroupScheme.baseChange s
  have hsplit := GaloisPinningData.isSplitTorus_separableClosure T hj.1
  have hGE := connectedReductiveFieldExtensionStatement k E G hG
  have hjE := (maximalTorusBaseChange k E G T (t ≫ b) hj.1 hj.2.1).mp hj
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence E _ hGE _ hsplit _ hjE
  have : IsAffineHom (bcG.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom s)
    infer_instance
  have : LocallyOfFiniteType (bcG.obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom s)
    infer_instance
  have : IsAffineHom (bcG.obj B).X.hom := by
    change IsAffineHom (pullback.snd B.X.hom s)
    infer_instance
  have hcomp : bcG.map t ≫ bcG.map b = bcG.map (t ≫ b) := (bcG.map_comp t b).symm
  obtain ⟨ν, hνreg, hrep⟩ :=
    (regularCocharacterBorel E (bcG.obj G) hGE _ (bcG.map (t ≫ b)) hsplit hjE).2.2
      (bcG.obj B) (bcG.map b) (bcG.map t) (isBorelSubgroup_separableClosure hb) hcomp
  have hν : ∀ a, P.root' a ν ≠ 0 := by
    intro a
    change P.toLinearMap (P.root a) ν ≠ 0
    rw [hP.1]
    exact hνreg _ (by rw [← hP.2.1]; exact Set.mem_range_self a)
  have := hred
  let base := IsRootDatumOf.regularCocharacterBase k E (P := P) ν hν
  have hpos : ∀ a, base.IsPos a ↔ P.root a ∈ roots (bcG.map t) := by
    intro a
    rw [IsRootDatumOf.regularCocharacterBase_isPos k E (t ≫ b) hP ν hν a,
      mem_roots_iff_of_isRepresentedBy_parabolic_of_comp hsplit (bcG.map b) (bcG.map t)
        (bcG.map (t ≫ b)) hcomp ν hrep hνreg]
    have hroot : P.root a ∈ roots (bcG.map (t ≫ b)) := by
      rw [← hP.2.1]
      exact Set.mem_range_self a
    exact ⟨fun h => ⟨hroot, h⟩, fun h => h.2⟩
  let d : GaloisPinningData k E G :=
    { torus := T
      inclusion := t ≫ b
      isConnectedReductive := hGE
      isSplitTorus := hsplit
      isMaximalTorus := hjE
      rootIndex := J
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := base
      pinning := RootPinning.ofSplitMaximalTorus hGE hsplit _ hjE P hP base }
  refine ⟨d, fun σ => d.starAction_eq_galoisAction σ ?_⟩
  intro a
  change a ∈ base.support ↔
    (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k E (t ≫ b) hsplit hjE.2.1 hP
      σ).indexEquiv a ∈ base.support
  rw [IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus_indexEquiv]
  exact (IsRootDatumOf.galoisRootIndexEquiv_mem_support_iff k E (t ≫ b) hP base t hpos σ a).symm

end Langlands.GroupScheme
