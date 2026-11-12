import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricAtlasCoverIncidence
import Langlands.AlgebraicGeometry.GeometricallyConnectedClosedCoverProof
import Langlands.AlgebraicGeometry.SplitGenericComponentSpreading
import Langlands.AlgebraicGeometry.GeometricIrreducibilityProof

/-! # Geometric atlas covers from split generic components -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open SchemeFiberGeometry GenericImagePattern ComponentIncidence

variable {S : Scheme.{u}} {U : Over S} {ι : Type v}

/-- The residue fibre followed by algebraic closure is the geometric atlas fibre. -/
def geometricAtlasResidueFiberIso (U : Over S) (p : S) :
    Limits.pullback (U.hom.fiberToSpecResidueField p)
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p)
          (AlgebraicClosure (S.residueField p))))) ≅
      (U ⨯ Over.mk (componentCountGeometricPoint p)).left :=
  (pullbackLeftPullbackSndIso U.hom (S.fromSpecResidueField p) _).trans
    (Over.prodLeftIsoPullback U (Over.mk (componentCountGeometricPoint p))).symm

@[reassoc (attr := simp)]
theorem geometricAtlasResidueFiberIso_hom_fst (U : Over S) (p : S) :
    (geometricAtlasResidueFiberIso U p).hom ≫
        (prod.fst (X := U) (Y := Over.mk (componentCountGeometricPoint p))).left =
      Limits.pullback.fst _ _ ≫ U.hom.fiberι p := by
  dsimp only [geometricAtlasResidueFiberIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Over.prodLeftIsoPullback_inv_fst]
  exact pullbackLeftPullbackSndIso_hom_fst U.hom (S.fromSpecResidueField p) _

/-- The transported geometric cover is precisely base change of its residue-fibre range. -/
theorem preimage_geometricAtlasCoverSets (p : S)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ U.left) (i : ι) :
    (geometricAtlasResidueFiberIso U p).hom ⁻¹'
        geometricAtlasCoverSets (fun k => Set.range (g k)) p i =
      baseChangeSubschemeRanges
        (Limits.pullback.fst (U.hom.fiberToSpecResidueField p)
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p)
            (AlgebraicClosure (S.residueField p))))))
        (fun k => Limits.pullback.snd (g k) (U.hom.fiberι p)) i := by
  rw [baseChangeSubschemeRanges_eq_preimage,
    range_baseChange_eq_fiberSubschemeSets]
  ext x
  change (prod.fst (X := U) (Y := Over.mk (componentCountGeometricPoint p))).left
      ((geometricAtlasResidueFiberIso U p).hom x) ∈ Set.range (g i) ↔
    U.hom.fiberι p (Limits.pullback.fst (U.hom.fiberToSpecResidueField p)
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p)
        (AlgebraicClosure (S.residueField p))))) x) ∈ Set.range (g i)
  rw [← Scheme.Hom.comp_apply, geometricAtlasResidueFiberIso_hom_fst,
    Scheme.Hom.comp_apply]

/-- A geometrically connected residue-fibre piece gives a connected geometric atlas member. -/
theorem isConnected_geometricAtlasCoverSets_of_residueFiber
    (p : S) {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ U.left) (i : ι)
    [GeometricallyConnected
      (Limits.pullback.snd (g i) (U.hom.fiberι p) ≫ U.hom.fiberToSpecResidueField p)] :
    _root_.IsConnected (geometricAtlasCoverSets (fun k => Set.range (g k)) p i) := by
  apply (geometricAtlasResidueFiberIso U p).hom.homeomorph.isConnected_preimage.mp
  change _root_.IsConnected ((geometricAtlasResidueFiberIso U p).hom ⁻¹' _)
  rw [preimage_geometricAtlasCoverSets]
  exact isConnected_fieldBaseChangeSubschemeRanges
    (U.hom.fiberToSpecResidueField p) _
    (fun k => Limits.pullback.snd (g k) (U.hom.fiberι p)) i

/-- A residue-fibre cover covers the geometric atlas fibre. -/
theorem geometricAtlasCoverSets_cover_of_residueFiber
    (p : S) {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ U.left)
    (hcover : closedSubschemeFiberCover U.hom g p) :
    (⋃ i, geometricAtlasCoverSets (fun k => Set.range (g k)) p i) = Set.univ := by
  have hc : (⋃ i, Set.range (Limits.pullback.snd (g i) (U.hom.fiberι p))) =
      Set.univ := by
    simpa only [range_baseChange_eq_fiberSubschemeSets] using
      (show (⋃ i, fiberSubschemeSets U.hom g p i) = Set.univ from hcover)
  have hbc := baseChangeSubschemeRanges_cover
    (Limits.pullback.fst (U.hom.fiberToSpecResidueField p)
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p)
        (AlgebraicClosure (S.residueField p))))))
    (fun k => Limits.pullback.snd (g k) (U.hom.fiberι p)) hc
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨t, rfl⟩ := (geometricAtlasResidueFiberIso U p).hom.homeomorph.surjective x
  have ht : t ∈ ⋃ i, baseChangeSubschemeRanges
      (Limits.pullback.fst (U.hom.fiberToSpecResidueField p)
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p)
          (AlgebraicClosure (S.residueField p))))))
      (fun k => Limits.pullback.snd (g k) (U.hom.fiberι p)) i := by
    rw [hbc]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
  exact Set.mem_iUnion.mpr ⟨i, by
    rwa [← preimage_geometricAtlasCoverSets p g i] at hi⟩

/-- Geometric components of an atlas with split generic irreducible pieces are
constant on an open neighbourhood of the generic point. -/
theorem exists_open_geometricComponentsEquiv_of_split_generic
    [IsNoetherian S] (X : AlgebraicSpace S) (hX : IsQuasiSeparated X)
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    {η : S} (hη : IsGenericPoint η (Set.univ : Set S))
    (hgeom : FiberComponentsGeometricallyIrreducible U.hom η) :
    ∃ V : Set S, IsOpen V ∧ η ∈ V ∧ ∀ p ∈ V,
      Nonempty
        (@_root_.ConnectedComponents
            (Points (X.presheaf ⨯ (schemeYoneda S).obj
              (Over.mk (componentCountGeometricPoint p)))) (pointTopology _) ≃
          @_root_.ConnectedComponents
            (Points (X.presheaf ⨯ (schemeYoneda S).obj
              (Over.mk (componentCountGeometricPoint η)))) (pointTopology _)) := by
  let : LocallyOfFiniteType (U.hom.fiberToSpecResidueField η) := by
    change LocallyOfFiniteType (Limits.pullback.snd U.hom (S.fromSpecResidueField η))
    infer_instance
  let : IsNoetherian (U.hom.fiber η) :=
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian (U.hom.fiberToSpecResidueField η)
      toCompactSpace := inferInstance }
  let := (NoetherianSpace.finite_irreducibleComponents (α := U.hom.fiber η)).to_subtype
  let g := fiberComponentClosureι U.hom η
  let s := fun C => Set.range (g C)
  have hclosed : ∀ C, IsClosed (s C) :=
    fun C => (g C).isClosedEmbedding.isClosed_range
  obtain ⟨W, hW, hηW, hpieces⟩ :=
    exists_open_genericComponentClosures_geometricallyIrreducible_and_incidence
      finiteTypeGeometricallyIrreducibleGenericSpreading U.hom hη hgeom
  obtain ⟨V, hV, hηV, hpattern⟩ :=
    exists_open_atlasCoverIncidenceLoci X hX a ha s hclosed hη
  have hconn : ∀ p ∈ W, ∀ C, _root_.IsConnected (geometricAtlasCoverSets s p C) := by
    intro p hp C
    let : GeometricallyIrreducible
        (Limits.pullback.snd (g C) (U.hom.fiberι p) ≫
          U.hom.fiberToSpecResidueField p) := (hpieces p hp).2.1 C
    let : GeometricallyConnected
        (Limits.pullback.snd (g C) (U.hom.fiberι p) ≫
          U.hom.fiberToSpecResidueField p) :=
      geometricallyConnected_of_geometricallyIrreducible _
    exact isConnected_geometricAtlasCoverSets_of_residueFiber p g C
  have hcover : ∀ p ∈ W, (⋃ C, geometricAtlasCoverSets s p C) = Set.univ := by
    intro p hp
    exact geometricAtlasCoverSets_cover_of_residueFiber p g (hpieces p hp).1
  refine ⟨W ∩ V, hW.inter hV, ⟨hηW, hηV⟩, ?_⟩
  intro p hp
  exact ⟨(geometricAtlasClosedCoverComponentsEquiv a ha hs s hclosed p
    (hconn p hp.1) (hcover p hp.1)).symm.trans
      ((Quot.congr (Equiv.refl _) (hpattern p hp.2)).trans
        (geometricAtlasClosedCoverComponentsEquiv a ha hs s hclosed η
          (hconn η hηW) (hcover η hηW)))⟩

/-- For every split generic atlas, the exact host component count is constant nearby. -/
theorem exists_open_geometricFibreComponentCount_of_split_generic
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    (X : AlgebraicSpace (Spec (CommRingCat.of B))) (hX : IsQuasiSeparated X)
    {U : Over (Spec (CommRingCat.of B))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    {η : Spec (CommRingCat.of B)}
    (hη : IsGenericPoint η (Set.univ : Set (Spec (CommRingCat.of B))))
    (hgeom : FiberComponentsGeometricallyIrreducible U.hom η) :
    ∃ V : Set (Spec (CommRingCat.of B)), IsOpen V ∧ η ∈ V ∧ ∀ p ∈ V,
      geometricFibreComponentCount B X p = geometricFibreComponentCount B X η := by
  obtain ⟨V, hV, hηV, hcomp⟩ :=
    exists_open_geometricComponentsEquiv_of_split_generic X hX a ha hs hη hgeom
  exact ⟨V, hV, hηV, fun p hp => ENat.card_congr (hcomp p hp).some⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
