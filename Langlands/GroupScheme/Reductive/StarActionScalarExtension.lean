import Langlands.GroupScheme.Torus.LatticeGaloisScalarExtension
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.PinningConstruction
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.GaloisPointTowerBaseChange

/-! # Full star-action comparison under extension of the ground field -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace GaloisPinningData

section Comparison

variable {k L k' L' : Type u} [Field k] [Field L] [Field k'] [Field L']
  [Algebra k L] [Algebra k' L']
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of k'))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- A base-preserving equivalence intertwining ordinary character Galois
actions intertwines their Weyl-corrected star actions, over different fields. -/
theorem starAction_comp_of_character_intertwining
    (p : GaloisPinningData k L G) (q : GaloisPinningData k' L' H)
    (e : RootPairing.Equiv p.toSplitPinning.rootDatum q.toSplitPinning.rootDatum)
    (hb : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)
    (σ : L ≃ₐ[k] L) (τ : L' ≃ₐ[k'] L')
    (hx : ∀ χ, e.weightMap (characterLattice.galoisRepresentation k L p.torus σ χ) =
      characterLattice.galoisRepresentation k' L' q.torus τ (e.weightMap χ)) :
    e.comp (p.starAction σ).val = (q.starAction τ).val.comp e := by
  open StarActionIndependence in
  have hconj : StarActionIndependence.conjAut e (p.galoisAction σ) = q.galoisAction τ := by
    apply equiv_ext_of_weightMap
    intro y
    rw [conjAut_weightMap]
    obtain ⟨χ, rfl⟩ := e.weightEquiv.surjective y
    rw [LinearEquiv.symm_apply_apply]
    change e.weightMap ((p.galoisAction σ).weightMap χ) =
      (q.galoisAction τ).weightMap (e.weightMap χ)
    rw [galoisAction_weightMap_apply, galoisAction_weightMap_apply]
    exact hx χ
  have hw : q.galoisAction τ *
      (StarActionIndependence.conjAut e (p.galoisAction σ))⁻¹ ∈
        q.toSplitPinning.rootDatum.weylGroup := by
    rw [hconj, mul_inv_cancel]
    exact one_mem _
  exact StarActionFiniteStage.comp_basedRootDatumProjection
    p.toSplitPinning q.toSplitPinning e hb (p.galoisAction σ) (q.galoisAction τ) hw

end Comparison

section ScalarExtension

variable {k E L : Type u} [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance scalarExtension_affine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance scalarExtension_finiteType :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

/-- Actual Galois pinning data after extending the ground field, with a full
based root-datum comparison intertwining every relative Galois element. -/
structure ScalarExtension (p : GaloisPinningData k L G) where
  pinning : GaloisPinningData E L ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)
  rootEquiv : RootPairing.Equiv p.toSplitPinning.rootDatum pinning.toSplitPinning.rootDatum
  base_eq : ∀ a, a ∈ p.base.support ↔ rootEquiv.indexEquiv a ∈ pinning.base.support
  star_eq : ∀ σ : L ≃ₐ[E] L,
    rootEquiv.comp (p.starAction (σ.restrictScalars k)).val =
      (pinning.starAction σ).val.comp rootEquiv
  groupIso : (GroupScheme.baseChange (algebraBaseMap E L)).obj
      ((GroupScheme.baseChange (algebraBaseMap k E)).obj G) ≅
    (GroupScheme.baseChange (algebraBaseMap k L)).obj G
  groupIso_eq : groupIso = GaloisPointComparison.towerBaseChangeIso k E L G
  torusIso : (CommGroupScheme.baseChange (algebraBaseMap E L)).obj pinning.torus ≅
    (CommGroupScheme.baseChange (algebraBaseMap k L)).obj p.torus
  inclusion_comp : (GroupScheme.baseChange (algebraBaseMap E L)).map pinning.inclusion ≫ groupIso.hom =
    CommGroupScheme.groupHom torusIso.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k L)).map p.inclusion
  weight_eq : ∀ χ, rootEquiv.weightMap χ = torusIso.hom ≫ χ

/-- A common splitting field supplies an actual scalar-extension comparison,
with no finite-dimensional or separability restriction on the field tower. -/
theorem nonempty_scalarExtension (p : GaloisPinningData k L G) :
    Nonempty (ScalarExtension (E := E) p) := by
  let b := algebraBaseMap k E
  let j := algebraBaseMap E L
  let c := algebraBaseMap k L
  have hc : j ≫ b = c := by
    simp only [j, b, c, algebraBaseMap, ← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq k E L).symm
  let g := StarActionFiniteStage.groupTowerIsoOf b j c hc G
  let t := StarActionFiniteStage.towerIsoOf b j p.torus c hc
  let GE := (GroupScheme.baseChange b).obj G
  let TE := (CommGroupScheme.baseChange b).obj p.torus
  let iE := (GroupScheme.baseChange b).map p.inclusion
  have hGE : IsConnectedReductive ((GroupScheme.baseChange j).obj GE) :=
    IsConnectedReductive.of_iso g.symm p.isConnectedReductive
  have hTE : IsSplitTorus ((CommGroupScheme.baseChange j).obj TE).toGrp :=
    IsSplitTorus.of_iso
      (StarActionFiniteStage.groupTowerIsoOf b j c hc p.torus.toGrp).symm p.isSplitTorus
  have heq := StarActionFiniteStage.baseChange_map_eq_groupTowerIsoOf b j c hc p.inclusion
  have hiE : IsMaximalTorus (T := (CommGroupScheme.baseChange j).obj TE)
      ((GroupScheme.baseChange j).map iE) :=
    IsMaximalTorus.of_eq_iso_comp_comp_iso
      (T := (CommGroupScheme.baseChange c).obj p.torus)
      (T' := (CommGroupScheme.baseChange j).obj TE) p.isMaximalTorus
      (StarActionFiniteStage.groupTowerIsoOf b j c hc p.torus.toGrp).symm g heq
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence L _ hGE _ hTE _ hiE
  have hsq : (GroupScheme.baseChange j).map iE ≫ g.inv =
      CommGroupScheme.groupHom t.inv ≫ (GroupScheme.baseChange c).map p.inclusion := by
    rw [heq, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  let e := rootDatumEquivOfTorusCompatibleIso hGE p.isConnectedReductive hTE p.isSplitTorus
    hiE p.isMaximalTorus g.symm t.symm hsq hP p.isRootDatum
  have he (χ) : e.weightMap χ = t.inv ≫ χ :=
    rootDatumEquivOfTorusCompatibleIso_weightMap hGE p.isConnectedReductive hTE p.isSplitTorus
      hiE p.isMaximalTorus g.symm t.symm hsq hP p.isRootDatum χ
  let base' : P.Base := p.base.map e
  let q : GaloisPinningData E L GE :=
    { torus := TE
      inclusion := iE
      isConnectedReductive := hGE
      isSplitTorus := hTE
      isMaximalTorus := hiE
      rootIndex := J
      finiteRootIndex := hJ
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := base'
      pinning := RootPinning.ofSplitMaximalTorus hGE hTE _ hiE P hP base' }
  have hb : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support := by
    classical
    intro a
    change a ∈ p.base.support ↔ e.indexEquiv a ∈ (p.base.map e).support
    rw [RootPairing.Base.support_map_eq, Finset.mem_image]
    constructor
    · exact fun ha => ⟨a, ha, rfl⟩
    · rintro ⟨x, hx, hxa⟩
      exact e.indexEquiv.injective hxa ▸ hx
  refine ⟨{
    pinning := q
    rootEquiv := e
    base_eq := hb
    star_eq := fun σ => ?_
    groupIso := g.symm
    groupIso_eq := rfl
    torusIso := t.symm
    inclusion_comp := hsq
    weight_eq := he }⟩
  apply starAction_comp_of_character_intertwining p q e hb (σ.restrictScalars k) σ
  intro χ
  exact (he _).trans ((characterLattice.galoisRepresentation_scalarExtension hc p.torus σ χ).trans
    (congrArg (characterLattice.galoisRepresentation E L TE σ) (he χ).symm))

/-- Choose actual scalar-extension pinning data and their full star comparison. -/
def scalarExtension (p : GaloisPinningData k L G) : ScalarExtension (E := E) p :=
  Classical.choice (nonempty_scalarExtension p)

/-- Actual Galois pinning data after extending the ground field, with a full
based root-datum comparison intertwining every relative Galois element. -/
structure RootDatumScalarExtension (p : GaloisPinningData k L G) where
  pinning : GaloisPinningData E L ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)
  rootEquiv : RootPairing.Equiv p.toSplitPinning.rootDatum pinning.toSplitPinning.rootDatum
  base_eq : ∀ a, a ∈ p.base.support ↔ rootEquiv.indexEquiv a ∈ pinning.base.support
  star_eq : ∀ σ : L ≃ₐ[E] L,
    rootEquiv.comp (p.starAction (σ.restrictScalars k)).val =
      (pinning.starAction σ).val.comp rootEquiv

/-- Existence of the based root-datum comparison after changing ground field. -/
theorem nonempty_rootDatumScalarExtension (p : GaloisPinningData k L G) :
    Nonempty (RootDatumScalarExtension (E := E) p) := by
  obtain ⟨c⟩ := nonempty_scalarExtension (E := E) p
  exact ⟨⟨c.pinning, c.rootEquiv, c.base_eq, c.star_eq⟩⟩

/-- Choose a pinning with its based root-datum and star-action comparison. -/
def rootDatumScalarExtension (p : GaloisPinningData k L G) :
    RootDatumScalarExtension (E := E) p :=
  Classical.choice (nonempty_rootDatumScalarExtension p)

end ScalarExtension

end GaloisPinningData
end Langlands.GroupScheme
