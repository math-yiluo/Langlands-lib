import Langlands.GroupScheme.Reductive.StandardLeviDerivedPinning
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.LinearAlgebra.RootDatumFaceHeight

/-! # Cocharacters of the derived torus of a dynamic Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000

section Field

variable {k : Type u} [Field k] {G M D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
  {p : SplitPinning G} {ν : cocharacterLattice p.torus}
  {j : M ⟶ G} {i : D ⟶ M}

/-- The postcomposition map on the actual torus of a derived Levi has
image the simple zero coroot span when the derived group is simply connected. -/
theorem StandardLeviDerivedPinning.range_cocharacterMapInt_eq_span_simple
    (R : StandardLeviDerivedPinning p ν j i) (hsc : IsSimplyConnected D)
    (hν : ∀ a : p.base.support, 0 ≤ p.rootDatum.root' a.val ν)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ p.inclusion)).IsRepresentedBy j)
    (hi : IsDerivedSubgroup i) :
    LinearMap.range (RealTorusSpace.cocharacterMapInt R.torusMap) =
      Submodule.span ℤ (p.rootDatum.coroot ''
        {r | r ∈ p.base.support ∧ p.rootDatum.root' r ν = 0}) := by
  let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
  let pD := R.pinning
  let P := p.rootDatum
  let Q := pD.rootDatum
  have hjT : (torusCentralizer χ).IsRepresentedBy j :=
    (torusCentralizer_gm_eq_dynamicCentralizer χ).symm ▸ hj
  have hjc := isSplitTorus_gm.isClosedSubgroup_torusCentralizer χ hjT
  have hM := splitTorusCentralizerReductive k G p.isConnectedReductive (Gm _) χ
    isSplitTorus_gm M j hjT
  have ht : SubgroupFunctor.range p.inclusion ≤ torusCentralizer χ := by
    rw [torusCentralizer_gm_eq_dynamicCentralizer]
    exact (range_le_torusCentralizer p.inclusion).trans
      (torusCentralizer_le_dynamicCentralizer p.inclusion _)
  let t := hjT.liftOfLE p.inclusion ht
  have htcomp : t ≫ j = p.inclusion := hjT.liftOfLE_comp _ _
  have htmax : IsMaximalTorus t := IsMaximalTorus.of_comp hjc (htcomp.symm ▸ p.isMaximalTorus)
  have hsq : pD.inclusion ≫ i = CommGroupScheme.groupHom R.torusMap ≫ t := by
    apply hjT.hom_ext
    simp only [Category.assoc, htcomp]
    exact R.square.symm
  obtain ⟨e, he⟩ := exists_derivedCentralizerRootEquiv χ isSplitTorus_gm j hjT hM
    p.inclusion p.isSplitTorus p.isRootDatum t htcomp htmax ν rfl
    i hi pD.inclusion pD.isSplitTorus pD.isMaximalTorus R.torusMap hsq pD.isRootDatum
  have hzero (r : p.rootIndex) : ν ≫ P.root r = 0 ↔ P.root' r ν = 0 := by
    change _ ↔ P.toLinearMap (P.root r) ν = _
    rw [p.isRootDatum.1, latticePairing_apply]
    exact (gmEndEquiv k).map_eq_zero_iff.symm
  let f := RealTorusSpace.cocharacterMapInt R.torusMap
  have hset : f '' Set.range Q.coroot = P.coroot '' {r | P.root' r ν = 0} := by
    ext y
    constructor
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      exact ⟨(e q).val, (hzero _).mp (e q).property, (he q).2.symm⟩
    · rintro ⟨r, hr, rfl⟩
      let z : {r : p.rootIndex // ν ≫ P.root r = 0} := ⟨r, (hzero r).mpr hr⟩
      refine ⟨Q.coroot (e.symm z), Set.mem_range_self _, ?_⟩
      change Q.coroot (e.symm z) ≫ R.torusMap = P.coroot r
      rw [(he (e.symm z)).2, e.apply_symm_apply]
  have hspan := splitSimplyConnectedCorootSpan k D hsc pD.torus pD.isSplitTorus
    pD.inclusion pD.isMaximalTorus pD.rootIndex Q pD.isRootDatum pD.isReduced
  let : Fintype p.rootIndex := Fintype.ofFinite _
  calc
    LinearMap.range f = (Q.corootSpan ℤ).map f := by rw [hspan, Submodule.map_top]
    _ = Submodule.span ℤ (P.coroot '' {r | P.root' r ν = 0}) := by
      rw [RootPairing.corootSpan, Submodule.map_span, hset]
    _ = _ := RootDatumFaceHeight.coroot_span_zero_eq_of_dominant (B := p.base) (ν := ν)
      fun r hr => hν ⟨r, hr⟩

end Field

/-- For a standard derived Levi pinning, the actual integral cocharacter map
has image the simple zero coroot span. -/
def DerivedLeviCocharacterSpanStatement : Prop :=
  ∀ (k : Type u) [Field k] (G M D : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    (p : SplitPinning G) (ν : cocharacterLattice p.torus) (j : M ⟶ G) (i : D ⟶ M)
    (R : StandardLeviDerivedPinning p ν j i),
    IsSimplyConnected D →
    (∀ a : p.base.support, 0 ≤ p.rootDatum.root' a.val ν) →
    (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ p.inclusion)).IsRepresentedBy j →
    IsDerivedSubgroup i →
    LinearMap.range (RealTorusSpace.cocharacterMapInt R.torusMap) =
      Submodule.span ℤ (p.rootDatum.coroot ''
        {r | r ∈ p.base.support ∧ p.rootDatum.root' r ν = 0})

theorem derivedLeviCocharacterSpan : DerivedLeviCocharacterSpanStatement.{u} := by
  intro k _ G M D _ _ _ _ p ν j i R hsc hν hj hi
  exact R.range_cocharacterMapInt_eq_span_simple hsc hν hj hi

end Langlands.GroupScheme
