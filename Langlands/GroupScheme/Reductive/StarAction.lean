import Langlands.GroupScheme.Reductive.BasedRootDatumProjection
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots

/-! # The star action on a based root datum -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable (k E : Type u) [Field k] [Field E] [Algebra k E]

local instance starActionBaseChangeAffine {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-- Pinning data for the star action of `E ≃ₐ[k] E`: a torus `T` of `G` defined over `k`
whose base change to `E` is a split maximal torus of `G_E`, together with a reduced root
datum of `(G_E, T_E)`, a base of it and simple-root Lie vectors. -/
structure GaloisPinningData (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] where
  /-- The torus, defined over `k`. -/
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  /-- Its inclusion into `G`, defined over `k`. -/
  inclusion : torus.toGrp ⟶ G
  isConnectedReductive :
    IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)
  isSplitTorus :
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj torus).toGrp
  isMaximalTorus : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj torus)
    ((GroupScheme.baseChange (algebraBaseMap k E)).map inclusion)
  /-- The index type of the roots. -/
  rootIndex : Type u
  [finiteRootIndex : Finite rootIndex]
  /-- The root datum of `(G_E, T_E)`. -/
  rootDatum : RootDatum rootIndex
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj torus))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj torus))
  isRootDatum : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj torus)
    ((GroupScheme.baseChange (algebraBaseMap k E)).map inclusion) rootDatum
  isReduced : rootDatum.IsReduced
  /-- The chosen base. -/
  base : rootDatum.Base
  /-- The chosen simple-root Lie vectors. -/
  pinning : RootPinning (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj torus)
    ((GroupScheme.baseChange (algebraBaseMap k E)).map inclusion) rootDatum base

attribute [instance] GaloisPinningData.finiteRootIndex

namespace GaloisPinningData

variable {k E} {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (d : GaloisPinningData k E G)

/-- The split pinning of `G_E` carried by the data. -/
def toSplitPinning : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k E)).obj G) where
  isConnectedReductive := d.isConnectedReductive
  torus := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj d.torus
  inclusion := (GroupScheme.baseChange (algebraBaseMap k E)).map d.inclusion
  isSplitTorus := d.isSplitTorus
  isMaximalTorus := d.isMaximalTorus
  rootIndex := d.rootIndex
  rootDatum := d.rootDatum
  isRootDatum := d.isRootDatum
  isReduced := d.isReduced
  base := d.base
  pinning := d.pinning

variable [LocallyOfFiniteType G.X.hom]

/-- The ordinary Galois action of `E ≃ₐ[k] E` on the root datum of `(G_E, T_E)`, through its
action on the characters and cocharacters of the `k`-torus `T`. -/
def galoisAction : (E ≃ₐ[k] E) →* d.toSplitPinning.rootDatum.Aut :=
  IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k E d.inclusion d.isSplitTorus
    d.isMaximalTorus.2.1 d.isRootDatum

/-- The star action: the ordinary Galois action followed by the unique Weyl correction
restoring the chosen base. -/
def starAction : (E ≃ₐ[k] E) →* d.toSplitPinning.basedRootDatumAut :=
  d.toSplitPinning.basedRootDatumProjection.comp d.galoisAction

/-- The star action differs from the ordinary Galois action by an element of the Weyl
group of the root datum. -/
theorem starAction_mul_galoisAction_inv_mem (σ : E ≃ₐ[k] E) :
    (d.starAction σ).val * (d.galoisAction σ)⁻¹ ∈ d.toSplitPinning.rootDatum.weylGroup :=
  d.toSplitPinning.basedRootDatumProjection_correction (d.galoisAction σ)

/-- There is a Weyl element `w` with `w * galoisAction σ = starAction σ`. -/
theorem exists_weyl_mul_galoisAction_eq_starAction (σ : E ≃ₐ[k] E) :
    ∃ w : d.toSplitPinning.rootDatum.weylGroup,
      w.val * d.galoisAction σ = (d.starAction σ).val :=
  d.toSplitPinning.exists_weyl_mul_eq_basedRootDatumProjection (d.galoisAction σ)

/-- If the ordinary Galois action of `σ` preserves the chosen base, it is the star action. -/
theorem starAction_eq_galoisAction (σ : E ≃ₐ[k] E)
    (h : d.galoisAction σ ∈ d.toSplitPinning.basedRootDatumAut) :
    (d.starAction σ).val = d.galoisAction σ := by
  change (d.toSplitPinning.basedRootDatumProjection
    (⟨d.galoisAction σ, h⟩ : d.toSplitPinning.basedRootDatumAut).val).val = _
  rw [d.toSplitPinning.basedRootDatumProjection_of_based]

/-- The star action of `σ` is trivial exactly when the ordinary Galois action of `σ` lies
in the Weyl group. -/
theorem starAction_eq_one_iff (σ : E ≃ₐ[k] E) :
    d.starAction σ = 1 ↔ d.galoisAction σ ∈ d.toSplitPinning.rootDatum.weylGroup :=
  d.toSplitPinning.basedRootDatumProjection_eq_one_iff (d.galoisAction σ)

end GaloisPinningData

end Langlands.GroupScheme
