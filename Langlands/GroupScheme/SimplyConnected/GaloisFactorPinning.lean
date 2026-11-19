import Langlands.GroupScheme.Reductive.PinningActualTitsDiagram
import Langlands.GroupScheme.Reductive.TitsClassFactorProjection
import Langlands.GroupScheme.SimplyConnected.GeometricFactorTorus
import Langlands.GroupScheme.SimplyConnected.FactorComponentEmbedding
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Torus.GaloisCharacterFunctor

/-! # Actual original-field Galois pinnings for recovered geometric factors -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

private theorem rootDatum_comp_ambientIso {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {A B : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom A.X.hom] [IsAffineHom B.X.hom]
    {J : Type u} {t : T.toGrp ⟶ A}
    {Q : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hQ : IsRootDatumOf t Q) (e : A ≅ B) : IsRootDatumOf (t ≫ e.hom) Q := by
  refine ⟨hQ.1, ?_, ?_⟩
  · have hs : t ≫ e.hom = CommGroupScheme.groupHom (Iso.refl T).hom ≫ (t ≫ e.hom) :=
      (Category.id_comp _).symm
    have hchar : ⇑(characterLattice.congr (Iso.refl T)) = id := by
      funext a
      exact Category.id_comp a
    rw [hQ.2.1, ← roots_image_of_transport (Iso.refl T) e hs, hchar, Set.image_id]
  · intro a
    obtain ⟨n, σ, hn, hσ⟩ := hQ.2.2 a
    refine ⟨n ≫ e.hom.hom.hom, σ, ?_, hσ⟩
    unfold IsNormalizingPoint at hn ⊢
    rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, hn, Category.assoc]

namespace GaloisPinningData

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- Full star action on a simple vertex of actual Galois pinning data. -/
def simpleStarVertex (p : GaloisPinningData k L G) (σ : L ≃ₐ[k] L) (b : p.base.support) :
    p.base.support :=
  p.simpleStar σ b

/-- An actual original-field pinning of a normal factor, with a comparison to
the full ambient simple-root fibre and every full Galois star element. -/
structure FactorPinningComparison (p : GaloisPinningData k L G)
    (D : SimplyConnectedAlmostSimpleProduct ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    (hG : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    (i : D.Index) (H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] where
  pinning : GaloisPinningData k L H
  vertices : pinning.base.support ≃ {a : p.base.support //
    D.rootDatumFactorIndex hG p.isSplitTorus _ p.isMaximalTorus p.isRootDatum a.val = i}
  cartan_eq : ∀ b c,
    p.rootDatum.pairing (vertices b).val.val (vertices c).val.val = pinning.rootDatum.pairing b.val c.val
  star_eq : ∀ (σ : L ≃ₐ[k] L) b,
    (vertices (pinning.simpleStarVertex σ b)).val.val =
      (p.starAction σ).val.indexEquiv (vertices b).val.val

/-- The actual factor comparison together with the projection defining its
simple-root inflation. -/
structure FactorPinningWithProjection (p : GaloisPinningData k L G)
    (D : SimplyConnectedAlmostSimpleProduct ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    (hG : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    (i : D.Index) (j : H ⟶ G) where
  comparison : p.FactorPinningComparison D hG i H
  projection : p.FactorProjection comparison.pinning
  inclusion_eq : projection.inclusion = j
  vertices_eq : ∀ b, projection.vertices b = (comparison.vertices b).val

end GaloisPinningData
namespace NormalFactorTorusProjection

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  (p : GaloisPinningData k L G) {j : H ⟶ G}
  (F : NormalFactorTorusProjection j p.inclusion)
  (D : SimplyConnectedAlmostSimpleProduct ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
  (hG : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)) (i : D.Index)
  (r : (GroupScheme.baseChange (algebraBaseMap k L)).obj H ≅ D.factor i)
  (hr : (GroupScheme.baseChange (algebraBaseMap k L)).map j = r.hom ≫ D.inclusion i)

local instance galoisFactorPinning_ambientAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance galoisFactorPinning_subgroupAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj H).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom _)
  infer_instance

local instance galoisFactorPinning_factorAffine : IsAffineHom (D.factor i).X.hom :=
  (D.isSimplyConnected i).isSemisimple.isConnectedReductive.isAffineHom

include F r hr

/-- Construct a genuine Galois pinning on the original normal-subgroup model.
Its torus projection is defined over the ground field, so the entire ambient
simple-root fibre comparison intertwines every full star element. -/
theorem nonempty_galoisFactorPinningWithProjection (hH : IsConnectedReductive H) :
    Nonempty (p.FactorPinningWithProjection D hG i j) := by
  let B := GroupScheme.baseChange (algebraBaseMap k L)
  let BC := CommGroupScheme.baseChange (algebraBaseMap k L)
  let FG : D.FactorMaximalTorus p.toSplitPinning.inclusion i :=
    F.geometricFactorTorus D i r hr hH p.isSplitTorus
  have hHL : IsConnectedReductive (B.obj H) :=
    (D.isSimplyConnected i).isSemisimple.isConnectedReductive.of_iso r
  have hsplit : IsSplitTorus (BC.obj F.torus).toGrp := F.isSplitTorus_baseChange L p.isSplitTorus
  have hmax : IsMaximalTorus (T := BC.obj F.torus) (B.map F.subgroupHom) :=
    isMaximalTorus_baseChange_of_torusCentralizer_eq L F.isMaximalTorus.1 F.isMaximalTorus.2.1
      (maximalTorusCentralizer k H hH F.torus F.subgroupHom F.isMaximalTorus)
  obtain ⟨J, hJ, Q, hQ, hred⟩ := rootDatumExistence L (B.obj H) hHL
    (BC.obj F.torus) hsplit (B.map F.subgroupHom) hmax
  let : Finite J := hJ
  let : Q.IsReduced := hred
  have hQG : IsRootDatumOf FG.subgroupHom Q := rootDatum_comp_ambientIso hQ r
  let b := FG.inducedBase D hG p.toSplitPinning hQG
  let pH : GaloisPinningData k L H := {
    torus := F.torus
    inclusion := F.subgroupHom
    isConnectedReductive := hHL
    isSplitTorus := hsplit
    isMaximalTorus := hmax
    rootIndex := J
    finiteRootIndex := hJ
    rootDatum := Q
    isRootDatum := hQ
    isReduced := hred
    base := b
    pinning := RootPinning.ofSplitMaximalTorus hHL hsplit _ hmax Q hQ b }
  let f : SplitPinning.BasedComponentEmbedding pH.toSplitPinning p.toSplitPinning := {
    rootEmbedding := FG.rootComponentEmbedding D hG p.toSplitPinning hQG
    base_iff := FG.mem_inducedBase_iff D hG p.toSplitPinning hQG }
  let v := FG.simpleRootIndexEquiv D hG p.toSplitPinning hQG
  let C : p.FactorPinningComparison D hG i H := {
    pinning := pH
    vertices := v
    cartan_eq := FG.pairing_simpleRootIndexEquiv D hG p.toSplitPinning hQG
    star_eq := by
      intro σ a
      have hnat (χ : characterLattice (BC.obj F.torus)) :
          f.rootEmbedding.weightMap (characterLattice.galoisRepresentation k L F.torus σ χ) =
            characterLattice.galoisRepresentation k L p.torus σ (f.rootEmbedding.weightMap χ) := by
        exact (characterLattice.galoisRepresentation_naturality k L
          (Additive.ofMul F.projection) σ χ).symm
      exact pH.starAction_index_of_componentWeightIntertwining p f σ σ hnat a.val }
  let P : p.FactorProjection C.pinning := {
    inclusion := j
    projection := F.retraction
    section_comp := F.inclusion_retraction
    torusInclusion := F.torusHom
    torusProjection := Additive.ofMul F.projection
    torus_section_comp := congrArg Additive.ofMul F.projection_section
    torusProjection_comp := F.projection_comp.symm
    vertices := ⟨fun b => (v b).val, fun _ _ h => v.injective (Subtype.ext h)⟩
    root_eq := fun b =>
      (FG.rootIndex_root D hG p.isSplitTorus p.toSplitPinning.inclusion
        p.isMaximalTorus p.isRootDatum hQG b.val).symm }
  exact ⟨⟨C, P, rfl, fun _ => rfl⟩⟩

/-- The actual pinning comparison obtained by keeping the diagram of the
compatible projection construction. -/
theorem nonempty_galoisFactorPinning (hH : IsConnectedReductive H) :
    Nonempty (p.FactorPinningComparison D hG i H) := by
  obtain ⟨C⟩ := F.nonempty_galoisFactorPinningWithProjection p D hG i r hr hH
  exact ⟨C.comparison⟩

end NormalFactorTorusProjection
end Langlands.GroupScheme
