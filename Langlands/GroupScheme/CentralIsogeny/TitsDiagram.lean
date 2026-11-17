import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Reductive.StarActionHom
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumProof
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.CentralIsogeny.MaximalTorusImageProof
import Langlands.GroupScheme.Torus.GaloisCharacterFunctor

/-! # Actual Cartan and full star diagrams under central isogenies -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

private instance titsDiagram_affineBaseChange {k E : Type u} [Field k] [Field E] [Algebra k E]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

private instance titsDiagram_finiteTypeBaseChange {k E : Type u}
    [Field k] [Field E] [Algebra k E]
    {G : GroupScheme (Spec (CommRingCat.of k))} [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

namespace GaloisPinningData

variable {k : Type u} [Field k]
  {C G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom C.X.hom] [LocallyOfFiniteType C.X.hom]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A central-isogeny-compatible pair of actual pinnings, retaining the source
torus and root datum, with a based morphism on the full lattices. -/
structure CentralImage (p : GaloisPinningData k (SeparableClosure k) C) where
  target : GaloisPinningData k (SeparableClosure k) G
  sourceBase : p.rootDatum.Base
  sourcePinning : RootPinning p.toSplitPinning.inclusion p.rootDatum sourceBase
  rootHom : RootPairing.Hom target.rootDatum p.rootDatum
  weight_injective : Function.Injective rootHom.weightMap
  coweight_injective : Function.Injective rootHom.coweightMap
  base_iff : ∀ i, i ∈ target.base.support ↔ rootHom.indexEquiv i ∈ sourceBase.support
  character_intertwining : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) χ,
    rootHom.weightMap (characterLattice.galoisRepresentation k (SeparableClosure k)
      target.torus σ χ) =
      characterLattice.galoisRepresentation k (SeparableClosure k) p.torus σ
        (rootHom.weightMap χ)

/-- The source pinning with the compatible transported base. -/
def CentralImage.source {p : GaloisPinningData k (SeparableClosure k) C}
    (F : CentralImage (G := G) p) : GaloisPinningData k (SeparableClosure k) C :=
  { p with base := F.sourceBase, pinning := F.sourcePinning }

/-- The actual central-isogeny root morphism, with both bases retained. -/
def CentralImage.basedHom {p : GaloisPinningData k (SeparableClosure k) C}
    (F : CentralImage (G := G) p) :
    SplitPinning.BasedRootHom F.target.toSplitPinning F.source.toSplitPinning :=
  ⟨F.rootHom, F.base_iff⟩

/-- Full star naturality on every actual root in the compatible pinnings. -/
theorem CentralImage.star_eq {p : GaloisPinningData k (SeparableClosure k) C}
    (F : CentralImage (G := G) p)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (i : F.target.rootIndex) :
    F.rootHom.indexEquiv ((F.target.starAction σ).val.indexEquiv i) =
      (F.source.starAction σ).val.indexEquiv (F.rootHom.indexEquiv i) :=
  F.target.starAction_index_of_basedHom F.source F.basedHom σ σ
    (F.character_intertwining σ) i

omit [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The actual closed image of the source maximal torus provides compatible
pinnings and a full star-equivariant root morphism under a central isogeny. -/
theorem nonempty_centralImage (hC : IsConnectedReductive C) (hG : IsConnectedReductive G)
    (φ : C ⟶ G) (hφ : IsCentralIsogeny φ)
    (p : GaloisPinningData k (SeparableClosure k) C)
    (hp : IsMaximalTorus p.inclusion) : Nonempty (CentralImage (G := G) p) := by
  let := hG.smooth
  let e := p.inclusion ≫ φ
  have : IsFinite φ.hom.hom.left := hφ.isFinite
  have : IsClosedImmersion p.inclusion.hom.hom.left := hp.2.1
  have : IsFinite e.hom.hom.left := by
    change IsFinite (p.inclusion.hom.hom.left ≫ φ.hom.hom.left)
    infer_instance
  have hS : IsTorus (SchematicImage.image e) := hp.1.isTorus_schematicImage e
  let S : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { SchematicImage.image e with comm := hS.isCommMonObj }
  let i : S.toGrp ⟶ G := SchematicImage.inclusion e
  let t : p.torus ⟶ S := Additive.ofMul (SchematicImage.projection e)
  have ht : p.inclusion ≫ φ = CommGroupScheme.groupHom t ≫ i :=
    (SchematicImage.projection_inclusion e).symm
  have : IsFinite (CommGroupScheme.groupHom t).hom.hom.left := by
    have hfin : IsFinite ((CommGroupScheme.groupHom t).hom.hom.left ≫ i.hom.hom.left) := by
      change IsFinite (CommGroupScheme.groupHom t ≫ i).hom.hom.left
      rw [← ht]
      infer_instance
    exact IsFinite.of_comp _ i.hom.hom.left
  have : IsSchemeTheoreticallyDominant (CommGroupScheme.groupHom t).hom.hom.left :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (SchematicImage.projection e).hom.hom.left)
  have hsurj : Surjective (CommGroupScheme.groupHom t).hom.hom.left := inferInstance
  have hi : IsMaximalTorus i :=
    centralIsogenyMaximalTorusImage k C G hC hG φ hφ p.torus S p.inclusion i t hp hS
      (inferInstanceAs (IsClosedImmersion (SchematicImage.inclusion e).hom.hom.left)) hsurj ht
  let K := SeparableClosure k
  let b := algebraBaseMap k K
  let GE := (GroupScheme.baseChange b).obj G
  let SE := (CommGroupScheme.baseChange b).obj S
  let iE : SE.toGrp ⟶ GE := (GroupScheme.baseChange b).map i
  have hGE : IsConnectedReductive GE := connectedReductiveFieldExtensionStatement k K G hG
  have hSE : IsSplitTorus SE.toGrp := isSplitTorus_separableClosure S hS
  have hiE : IsMaximalTorus (T := SE) iE := (maximalTorusBaseChange k K G S i hi.1 hi.2.1).mp hi
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence K GE hGE SE hSE iE hiE
  let B := Langlands.LinearAlgebra.RootDatumBase.base P
  let q : GaloisPinningData k K G :=
    { torus := S
      inclusion := i
      isConnectedReductive := hGE
      isSplitTorus := hSE
      isMaximalTorus := hiE
      rootIndex := J
      finiteRootIndex := hJ
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := B
      pinning := RootPinning.ofSplitMaximalTorus hGE hSE iE hiE P hP B }
  let tE := (CommGroupScheme.baseChange b).map t
  have htE : p.toSplitPinning.inclusion ≫ (GroupScheme.baseChange b).map φ =
      CommGroupScheme.groupHom tE ≫ q.toSplitPinning.inclusion := by
    change (GroupScheme.baseChange b).map p.inclusion ≫ (GroupScheme.baseChange b).map φ = _
    rw [← Functor.map_comp, ht, Functor.map_comp]
    rfl
  obtain ⟨f, hf, _hfc, hfw, hfc, _hiso⟩ :=
    centralIsogenyRootDatumHom K ((GroupScheme.baseChange b).obj C) GE
      p.isConnectedReductive hGE p.toSplitPinning.torus q.toSplitPinning.torus
      p.isSplitTorus q.isSplitTorus p.toSplitPinning.inclusion q.toSplitPinning.inclusion
      p.isMaximalTorus q.isMaximalTorus ((GroupScheme.baseChange b).map φ) tE
      (hφ.baseChange b) htE p.rootIndex q.rootIndex p.rootDatum q.rootDatum p.isRootDatum q.isRootDatum
  let baseC := Langlands.RootDatumHomBase.mapBase f hfw hfc q.base
  have hbase : ∀ j, j ∈ q.base.support ↔ f.indexEquiv j ∈ baseC.support := by
    classical
    intro j
    rw [Langlands.RootDatumHomBase.support_mapBase, Finset.mem_image]
    constructor
    · exact fun hj => ⟨j, hj, rfl⟩
    · rintro ⟨j', hj', heq⟩
      exact f.indexEquiv.injective heq ▸ hj'
  refine ⟨{
    target := q
    sourceBase := baseC
    sourcePinning := RootPinning.ofSplitMaximalTorus p.isConnectedReductive p.isSplitTorus
      p.toSplitPinning.inclusion p.isMaximalTorus p.rootDatum p.isRootDatum baseC
    rootHom := f
    weight_injective := hfw
    coweight_injective := hfc
    base_iff := hbase
    character_intertwining := ?_ }⟩
  intro σ χ
  exact (hf _).trans ((characterLattice.galoisRepresentation_naturality k K t σ χ).symm.trans
    (congrArg (characterLattice.galoisRepresentation k K p.torus σ) (hf χ).symm))

/-- Choose the actual compatible pinning construction. -/
def centralImage (hC : IsConnectedReductive C) (hG : IsConnectedReductive G)
    (φ : C ⟶ G) (hφ : IsCentralIsogeny φ)
    (p : GaloisPinningData k (SeparableClosure k) C) (hp : IsMaximalTorus p.inclusion) :
    CentralImage (G := G) p :=
  Classical.choice (nonempty_centralImage hC hG φ hφ p hp)

end GaloisPinningData

namespace TitsIndexData

variable {k : Type u} [Field k]
  {C G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom C.X.hom] [LocallyOfFiniteType C.X.hom]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The entire absolute integral Cartan diagram and every full star permutation,
without a requirement on restriction to maximal split tori. -/
structure CartanStarEquiv (d : TitsIndexData C) (e : TitsIndexData G) where
  vertices : d.Vertex ≃ e.Vertex
  cartan_eq : ∀ i j, e.cartan (vertices i) (vertices j) = d.cartan i j
  star_eq : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) i,
    vertices (d.star σ i) = e.star σ (vertices i)

/-- A central isogeny identifies all actual simple vertices, every ordered
Cartan entry and the action of each absolute Galois element, for arbitrary
compatible Tits-index choices on source and target. -/
theorem nonempty_cartanStarEquiv_of_centralIsogeny
    (d : TitsIndexData C) (e : TitsIndexData G) (φ : C ⟶ G) (hφ : IsCentralIsogeny φ) :
    Nonempty (CartanStarEquiv d e) := by
  let F := d.pinning.centralImage d.isSemisimple.isConnectedReductive
    e.isSemisimple.isConnectedReductive φ hφ d.maximalTorus
  obtain ⟨_gC, _tC, εC, _hconjC, _hweightC, hbaseC, hstarC⟩ :=
    StarActionIndependence.starActionIndependence k (SeparableClosure k) C d.pinning F.source
  obtain ⟨_gG, _tG, εG, _hconjG, _hweightG, hbaseG, hstarG⟩ :=
    StarActionIndependence.starActionIndependence k (SeparableClosure k) G F.target e.pinning
  let vC : d.Vertex ≃ F.source.base.support := εC.indexEquiv.subtypeEquiv hbaseC
  let vG : F.target.base.support ≃ e.Vertex := εG.indexEquiv.subtypeEquiv hbaseG
  let vF : F.target.base.support ≃ F.source.base.support :=
    F.rootHom.indexEquiv.subtypeEquiv F.base_iff
  refine ⟨{
    vertices := (vC.trans vF.symm).trans vG
    cartan_eq := ?_
    star_eq := ?_ }⟩
  · intro i j
    change e.pinning.rootDatum.pairing
        (εG.indexEquiv (F.rootHom.indexEquiv.symm (εC.indexEquiv i.val)))
        (εG.indexEquiv (F.rootHom.indexEquiv.symm (εC.indexEquiv j.val))) =
      d.pinning.rootDatum.pairing i.val j.val
    calc
      _ = F.target.rootDatum.pairing
          (F.rootHom.indexEquiv.symm (εC.indexEquiv i.val))
          (F.rootHom.indexEquiv.symm (εC.indexEquiv j.val)) := εG.toHom.pairing
      _ = F.source.rootDatum.pairing (εC.indexEquiv i.val) (εC.indexEquiv j.val) := by
        simpa only [GaloisPinningData.CentralImage.source, Equiv.apply_symm_apply] using
          (F.rootHom.pairing
            (i := F.rootHom.indexEquiv.symm (εC.indexEquiv i.val))
            (j := F.rootHom.indexEquiv.symm (εC.indexEquiv j.val))).symm
      _ = d.pinning.rootDatum.pairing i.val j.val := εC.toHom.pairing
  · intro σ i
    apply Subtype.ext
    have hC := congrArg (fun r => r.indexEquiv i.val) (hstarC σ)
    change εC.indexEquiv ((d.pinning.starAction σ).val.indexEquiv i.val) =
      (F.source.starAction σ).val.indexEquiv (εC.indexEquiv i.val) at hC
    have hF := congrArg F.rootHom.indexEquiv.symm
      (F.star_eq σ (F.rootHom.indexEquiv.symm (εC.indexEquiv i.val)))
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at hF
    have hG := congrArg
      (fun r => r.indexEquiv (F.rootHom.indexEquiv.symm (εC.indexEquiv i.val))) (hstarG σ)
    change εG.indexEquiv
        ((F.target.starAction σ).val.indexEquiv
          (F.rootHom.indexEquiv.symm (εC.indexEquiv i.val))) =
      (e.pinning.starAction σ).val.indexEquiv
        (εG.indexEquiv (F.rootHom.indexEquiv.symm (εC.indexEquiv i.val))) at hG
    change εG.indexEquiv
        (F.rootHom.indexEquiv.symm
          (εC.indexEquiv ((d.pinning.starAction σ).val.indexEquiv i.val))) =
      (e.pinning.starAction σ).val.indexEquiv
        (εG.indexEquiv (F.rootHom.indexEquiv.symm (εC.indexEquiv i.val)))
    rw [hC, ← hF]
    exact hG

/-- Choose the complete actual Cartan/star comparison of a central isogeny. -/
def cartanStarEquivOfCentralIsogeny
    (d : TitsIndexData C) (e : TitsIndexData G) (φ : C ⟶ G) (hφ : IsCentralIsogeny φ) :
    CartanStarEquiv d e :=
  Classical.choice (nonempty_cartanStarEquiv_of_centralIsogeny d e φ hφ)

end TitsIndexData
end Langlands.GroupScheme
