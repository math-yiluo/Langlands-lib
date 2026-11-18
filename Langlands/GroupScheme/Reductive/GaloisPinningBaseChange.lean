import Langlands.GroupScheme.Reductive.StarActionScalarExtension
import Langlands.GroupScheme.Reductive.StarActionFiniteStageProof
import Langlands.GroupScheme.Reductive.TorusTransportPinning
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescent
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus

/-! # Base change of Galois pinning data to an intermediate field -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace StarActionFiniteStage

section TowerTransport

variable {B SL SK : Scheme.{u}} (bL : SL ⟶ B) (j : SK ⟶ SL) (T : CommGroupScheme B)
  (bK : SK ⟶ B) (hc : j ≫ bL = bK)

/-- The inverse tower isomorphism intertwines the changes of test-scheme structure along an
endomorphism `a` of `SK` over `SL`. -/
theorem descentPoint_towerIsoOf_inv (a : SK ⟶ SK) (ha : a ≫ j = j) (haK : a ≫ bK = bK)
    (U : Over SK)
    (y : U ⟶ ((CommGroupScheme.baseChange j).obj ((CommGroupScheme.baseChange bL).obj T)).X) :
    descentPoint j a ha ((CommGroupScheme.baseChange bL).obj T).toGrp U y ≫
        (CommGroupScheme.groupHom (towerIsoOf bL j T bK hc).inv).hom.hom =
      descentPoint bK a haK T.toGrp U
        (y ≫ (CommGroupScheme.groupHom (towerIsoOf bL j T bK hc).inv).hom.hom) := by
  subst hc
  have hinv : CommGroupScheme.groupHom (towerIsoOf bL j T (j ≫ bL) rfl).inv =
      (baseChangeCompIso bL j T.toGrp).inv := by
    simp only [towerIsoOf, towerIso, eqToIso_refl, Iso.refl_trans]
    rfl
  rw [hinv]
  exact descentPoint_comp_of_fst (j ≫ bL) j a haK ha T.toGrp
    ((GroupScheme.baseChange bL).obj T.toGrp) (baseChangeCompIso bL j T.toGrp).inv
    (pullback.fst T.toGrp.X.hom bL) (baseChangeCompIso_inv_fst bL j T.toGrp) U y

/-- **Tower compatibility of transports.** Under the tower isomorphism, transport of
characters of `(T_L)_K` along an endomorphism `a` of `SK` over `SL` is transport of
characters of `T_K` along `a`, viewed over `B`. -/
theorem transport_congr_towerIsoOf (a : SK ⟶ SK) (ha : a ≫ j = j) (haK : a ≫ bK = bK)
    (ψ : characterLattice ((CommGroupScheme.baseChange bK).obj T)) :
    characterLattice.transport j a ha ((CommGroupScheme.baseChange bL).obj T)
        (characterLattice.congr (towerIsoOf bL j T bK hc) ψ) =
      characterLattice.congr (towerIsoOf bL j T bK hc)
        (characterLattice.transport bK a haK T ψ) := by
  apply characterLattice.ext_points
  intro U y
  have h1 : Gm.pointsEquiv SK U (y ≫ (CommGroupScheme.groupHom
        (characterLattice.transport j a ha ((CommGroupScheme.baseChange bL).obj T)
          (characterLattice.congr (towerIsoOf bL j T bK hc) ψ))).hom.hom) =
      Gm.pointsEquiv SK ((Over.map a).obj U)
        ((descentPoint j a ha ((CommGroupScheme.baseChange bL).obj T).toGrp U y ≫
          (CommGroupScheme.groupHom (towerIsoOf bL j T bK hc).inv).hom.hom) ≫
            (CommGroupScheme.groupHom ψ).hom.hom) :=
    (characterLattice.transport_points j a ha ((CommGroupScheme.baseChange bL).obj T)
      (characterLattice.congr (towerIsoOf bL j T bK hc) ψ) U y).trans
      (congrArg (Gm.pointsEquiv SK ((Over.map a).obj U))
        (comp_groupHom_comp _ (towerIsoOf bL j T bK hc).inv ψ))
  have h2 : Gm.pointsEquiv SK U (y ≫ (CommGroupScheme.groupHom
        (characterLattice.congr (towerIsoOf bL j T bK hc)
          (characterLattice.transport bK a haK T ψ))).hom.hom) =
      Gm.pointsEquiv SK ((Over.map a).obj U)
        (descentPoint bK a haK T.toGrp U
          (y ≫ (CommGroupScheme.groupHom (towerIsoOf bL j T bK hc).inv).hom.hom) ≫
            (CommGroupScheme.groupHom ψ).hom.hom) :=
    (congrArg (Gm.pointsEquiv SK U)
      (comp_groupHom_comp y (towerIsoOf bL j T bK hc).inv
        (characterLattice.transport bK a haK T ψ))).trans
      (characterLattice.transport_points bK a haK T ψ U
        (y ≫ (CommGroupScheme.groupHom (towerIsoOf bL j T bK hc).inv).hom.hom))
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact congrArg (fun z => Gm.pointsEquiv SK ((Over.map a).obj U)
    (z ≫ (CommGroupScheme.groupHom ψ).hom.hom))
    (descentPoint_towerIsoOf_inv bL j T bK hc a ha haK U y)

/-- Naturality of the tower isomorphism in the commutative group scheme. -/
theorem towerIsoOf_hom_naturality {T' : CommGroupScheme B} (τ : T' ⟶ T) :
    (CommGroupScheme.baseChange bK).map τ ≫ (towerIsoOf bL j T bK hc).hom =
      (towerIsoOf bL j T' bK hc).hom ≫
        (CommGroupScheme.baseChange j).map ((CommGroupScheme.baseChange bL).map τ) := by
  subst hc
  have h := baseChangeCompIso_hom_naturality bL j (CommGroupScheme.groupHom τ)
  simp only [towerIsoOf, eqToIso_refl, Iso.refl_trans]
  exact congrArg Additive.ofMul h

end TowerTransport

/-- If a base-preserving equivalence of root data intertwines the Galois actions of `σ` and
`τ` on characters, it intertwines their star actions. The two Galois pinning data may have
different ground fields, splitting fields and groups. -/
theorem starAction_comp_of_weightMap_of_fields {k k' K K' : Type u} [Field k] [Field k']
    [Field K] [Field K'] [Algebra k K] [Algebra k' K']
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    {G' : GroupScheme (Spec (CommRingCat.of k'))} [IsAffineHom G'.X.hom]
    [LocallyOfFiniteType G'.X.hom]
    (d' : GaloisPinningData k' K' G') (d : GaloisPinningData k K G)
    (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum)
    (hb : ∀ a, a ∈ d'.toSplitPinning.base.support ↔
      e.indexEquiv a ∈ d.toSplitPinning.base.support)
    (σ : K' ≃ₐ[k'] K') (τ : K ≃ₐ[k] K)
    (hx : ∀ χ, e.weightMap (characterLattice.galoisRepresentation k' K' d'.torus σ χ) =
      characterLattice.galoisRepresentation k K d.torus τ (e.weightMap χ)) :
    RootPairing.Equiv.comp e (d'.starAction σ).val =
      RootPairing.Equiv.comp (d.starAction τ).val e :=
  GaloisPinningData.starAction_comp_of_character_intertwining d' d e hb σ τ hx

end StarActionFiniteStage

/-! ### The tower `k ⊆ E ⊆ K` -/

section FieldTower

variable (k E K : Type u) [Field k] [Field E] [Field K] [Algebra k E] [Algebra k K]
  [Algebra E K] [IsScalarTower k E K]

/-- `Spec K → Spec E → Spec k` is `Spec K → Spec k`. -/
theorem algebraBaseMap_comp_algebraBaseMap :
    algebraBaseMap E K ≫ algebraBaseMap k E = algebraBaseMap k K := by
  unfold algebraBaseMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq k E K]

/-- The actual base-change isomorphism `T_K ≅ (T_E)_K` of a commutative group scheme over
`k`. -/
def torusTowerIso (T : CommGroupScheme (Spec (CommRingCat.of k))) :
    (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T ≅
      (CommGroupScheme.baseChange (algebraBaseMap E K)).obj
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) :=
  StarActionFiniteStage.towerIsoOf (algebraBaseMap k E) (algebraBaseMap E K) T
    (algebraBaseMap k K) (algebraBaseMap_comp_algebraBaseMap k E K)

/-- The actual base-change isomorphism `G_K ≅ (G_E)_K` of a group scheme over `k`. -/
def groupTowerIso (G : GroupScheme (Spec (CommRingCat.of k))) :
    (GroupScheme.baseChange (algebraBaseMap k K)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap E K)).obj
        ((GroupScheme.baseChange (algebraBaseMap k E)).obj G) :=
  StarActionFiniteStage.groupTowerIsoOf (algebraBaseMap k E) (algebraBaseMap E K)
    (algebraBaseMap k K) (algebraBaseMap_comp_algebraBaseMap k E K) G

/-- The torus and group tower isomorphisms are compatible with the base changes of a
homomorphism `T → G`. -/
theorem torusTowerIso_square (T : CommGroupScheme (Spec (CommRingCat.of k)))
    {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G) :
    (GroupScheme.baseChange (algebraBaseMap k K)).map i ≫ (groupTowerIso k E K G).hom =
      CommGroupScheme.groupHom (torusTowerIso k E K T).hom ≫
        (GroupScheme.baseChange (algebraBaseMap E K)).map
          ((GroupScheme.baseChange (algebraBaseMap k E)).map i) :=
  StarActionFiniteStage.towerIsoOf_square (algebraBaseMap k E) (algebraBaseMap E K) T
    (algebraBaseMap k K) (algebraBaseMap_comp_algebraBaseMap k E K) i

/-- The two-step base change of a homomorphism is its one-step base change, up to the group
tower isomorphisms. -/
theorem baseChange_map_eq_groupTowerIso {H G : GroupScheme (Spec (CommRingCat.of k))}
    (i : H ⟶ G) :
    (GroupScheme.baseChange (algebraBaseMap E K)).map
        ((GroupScheme.baseChange (algebraBaseMap k E)).map i) =
      (groupTowerIso k E K H).inv ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map i ≫
        (groupTowerIso k E K G).hom :=
  StarActionFiniteStage.baseChange_map_eq_groupTowerIsoOf (algebraBaseMap k E)
    (algebraBaseMap E K) (algebraBaseMap k K) (algebraBaseMap_comp_algebraBaseMap k E K) i

/-- Naturality of the torus tower isomorphism. -/
theorem torusTowerIso_hom_naturality {T' T : CommGroupScheme (Spec (CommRingCat.of k))}
    (τ : T' ⟶ T) :
    (CommGroupScheme.baseChange (algebraBaseMap k K)).map τ ≫ (torusTowerIso k E K T).hom =
      (torusTowerIso k E K T').hom ≫
        (CommGroupScheme.baseChange (algebraBaseMap E K)).map
          ((CommGroupScheme.baseChange (algebraBaseMap k E)).map τ) :=
  StarActionFiniteStage.towerIsoOf_hom_naturality (algebraBaseMap k E) (algebraBaseMap E K) T
    (algebraBaseMap k K) (algebraBaseMap_comp_algebraBaseMap k E K) τ

/-- The character transport `X^*(T_K) ≃ X^*((T_E)_K)`: precomposition with the inverse of the
actual tower isomorphism. -/
def characterTowerEquiv (T : CommGroupScheme (Spec (CommRingCat.of k))) :
    characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) ≃ₗ[ℤ]
      characterLattice ((CommGroupScheme.baseChange (algebraBaseMap E K)).obj
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)) :=
  (characterLattice.congr (torusTowerIso k E K T)).toIntLinearEquiv

theorem characterTowerEquiv_apply (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) :
    characterTowerEquiv k E K T χ = (torusTowerIso k E K T).inv ≫ χ :=
  rfl

theorem characterTowerEquiv_symm_apply (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (ψ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap E K)).obj
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))) :
    (characterTowerEquiv k E K T).symm ψ = (torusTowerIso k E K T).hom ≫ ψ :=
  rfl

/-- Naturality of the character transport: for a homomorphism `τ : T' → T` over `k`, the
transport commutes with precomposition by `τ_K` and `(τ_E)_K`. -/
theorem characterTowerEquiv_comp {T' T : CommGroupScheme (Spec (CommRingCat.of k))}
    (τ : T' ⟶ T)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) :
    characterTowerEquiv k E K T' ((CommGroupScheme.baseChange (algebraBaseMap k K)).map τ ≫ χ) =
      (CommGroupScheme.baseChange (algebraBaseMap E K)).map
          ((CommGroupScheme.baseChange (algebraBaseMap k E)).map τ) ≫
        characterTowerEquiv k E K T χ := by
  rw [characterTowerEquiv_apply, characterTowerEquiv_apply, ← Category.assoc,
    ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact torusTowerIso_hom_naturality k E K τ

/-- **Galois compatibility.** For `σ ∈ Gal(K/E)`, the character transport intertwines the
Galois action of `σ` through the `k`-structure of `T` with its Galois action through the
`E`-structure of `T_E`. -/
theorem characterTowerEquiv_galoisRepresentation (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (σ : K ≃ₐ[E] K)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) :
    characterTowerEquiv k E K T
        (characterLattice.galoisRepresentation k K T (σ.restrictScalars k) χ) =
      characterLattice.galoisRepresentation E K
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) σ
        (characterTowerEquiv k E K T χ) := by
  rw [characterLattice.galoisRepresentation_apply, characterLattice.galoisRepresentation_apply]
  exact (StarActionFiniteStage.transport_congr_towerIsoOf (algebraBaseMap k E)
    (algebraBaseMap E K) T (algebraBaseMap k K) (algebraBaseMap_comp_algebraBaseMap k E K)
    (galoisBaseMap E K σ) (galoisBaseMap_over E K σ)
    (galoisBaseMap_over k K (σ.restrictScalars k)) χ).symm

end FieldTower

/-! ### Base change of Galois pinning data -/

namespace GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (E : Type u) [Field E] [Algebra k E] [Algebra E K] [IsScalarTower k E K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

instance baseChangeIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k E)))

instance baseChangeLocallyOfFiniteType [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap k E)))

local instance twoStepBaseChangeIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap E K)).obj
      ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd
    ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom (algebraBaseMap E K)))

local instance oneStepBaseChangeIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K)))

variable (d : GaloisPinningData k K G)

include d in
theorem baseChange_isConnectedReductive :
    IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap E K)).obj
      ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)) :=
  IsConnectedReductive.of_iso (groupTowerIso k E K G).symm d.isConnectedReductive

theorem baseChange_isSplitTorus :
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap E K)).obj
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj d.torus)).toGrp :=
  IsSplitTorus.of_iso (groupTowerIso k E K d.torus.toGrp).symm d.isSplitTorus

theorem baseChange_isMaximalTorus :
    IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap E K)).obj
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj d.torus))
      ((GroupScheme.baseChange (algebraBaseMap E K)).map
        ((GroupScheme.baseChange (algebraBaseMap k E)).map d.inclusion)) :=
  IsMaximalTorus.of_eq_iso_comp_comp_iso
    (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj d.torus)
    (T' := (CommGroupScheme.baseChange (algebraBaseMap E K)).obj
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj d.torus))
    d.isMaximalTorus (groupTowerIso k E K d.torus.toGrp).symm (groupTowerIso k E K G)
    (baseChange_map_eq_groupTowerIso k E K d.inclusion)

/-- The root datum of `d`, transported to the torus `(T_E)_K` by the tower isomorphism. -/
def baseChangeRootDatum :
    RootDatum d.rootIndex
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap E K)).obj
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj d.torus)))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap E K)).obj
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj d.torus))) :=
  torusTransportRootDatum (torusTowerIso k E K d.torus) d.rootDatum

theorem baseChange_isRootDatum :
    IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap E K)).obj
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj d.torus))
      ((GroupScheme.baseChange (algebraBaseMap E K)).map
        ((GroupScheme.baseChange (algebraBaseMap k E)).map d.inclusion))
      (d.baseChangeRootDatum E) :=
  d.isRootDatum.torusTransport (torusTowerIso k E K d.torus) (groupTowerIso k E K G)
    (torusTowerIso_square k E K d.torus d.inclusion)

theorem baseChangeRootDatum_isReduced : (d.baseChangeRootDatum E).IsReduced := by
  have := d.isReduced
  exact torusTransportRootDatum_isReduced _ _

/-- The base of `d`, transported to `(T_E)_K`. -/
def baseChangeBase : (d.baseChangeRootDatum E).Base :=
  torusTransportBase (torusTowerIso k E K d.torus) d.rootDatum d.base

/-- **Base change of Galois pinning data.** For a scalar tower `k ⊆ E ⊆ K`, the Galois
pinning data `d` of `G` over `K` give Galois pinning data of `G_E` over the same field `K`:
the torus is `T_E`, its inclusion is the base change of the inclusion of `T`, and the root
datum and base are those of `d` transported by the actual tower isomorphism
`T_K ≅ (T_E)_K`. The simple-root Lie vectors are chosen by the Library's root-line theorem. -/
def baseChange : GaloisPinningData E K ((GroupScheme.baseChange (algebraBaseMap k E)).obj G) where
  torus := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj d.torus
  inclusion := (GroupScheme.baseChange (algebraBaseMap k E)).map d.inclusion
  isConnectedReductive := d.baseChange_isConnectedReductive E
  isSplitTorus := d.baseChange_isSplitTorus E
  isMaximalTorus := d.baseChange_isMaximalTorus E
  rootIndex := d.rootIndex
  rootDatum := d.baseChangeRootDatum E
  isRootDatum := d.baseChange_isRootDatum E
  isReduced := d.baseChangeRootDatum_isReduced E
  base := d.baseChangeBase E
  pinning := RootPinning.ofSplitMaximalTorus (d.baseChange_isConnectedReductive E)
    (d.baseChange_isSplitTorus E) _ (d.baseChange_isMaximalTorus E) (d.baseChangeRootDatum E)
    (d.baseChange_isRootDatum E) (d.baseChangeBase E)

@[simp] theorem baseChange_torus :
    (d.baseChange E).torus = (CommGroupScheme.baseChange (algebraBaseMap k E)).obj d.torus :=
  rfl

@[simp] theorem baseChange_inclusion :
    (d.baseChange E).inclusion = (GroupScheme.baseChange (algebraBaseMap k E)).map d.inclusion :=
  rfl

/-- The weight transport `X^*(T_K) ≃ X^*((T_E)_K)` from the integral weights of `d` to those
of its base change. -/
def weightTransport :
    characterLattice d.toSplitPinning.torus ≃ₗ[ℤ]
      characterLattice (d.baseChange E).toSplitPinning.torus :=
  characterTowerEquiv k E K d.torus

theorem weightTransport_apply (χ : characterLattice d.toSplitPinning.torus) :
    d.weightTransport E χ = (torusTowerIso k E K d.torus).inv ≫ χ :=
  rfl

/-- The base-changed root datum is the root datum of `d` transported along the weight
transport, with the same root indices. -/
def baseChangeRootDatumEquiv :
    RootPairing.Equiv d.toSplitPinning.rootDatum (d.baseChange E).toSplitPinning.rootDatum :=
  torusTransportRootDatumEquiv (torusTowerIso k E K d.torus) d.rootDatum

theorem baseChangeRootDatumEquiv_weightMap (χ : characterLattice d.toSplitPinning.torus) :
    (d.baseChangeRootDatumEquiv E).weightMap χ = d.weightTransport E χ :=
  rfl

theorem baseChangeRootDatumEquiv_indexEquiv :
    (d.baseChangeRootDatumEquiv E).indexEquiv = Equiv.refl d.rootIndex :=
  rfl

/-- The base change keeps the simple-root indices. -/
theorem baseChange_base_support :
    (d.baseChange E).toSplitPinning.base.support = d.toSplitPinning.base.support :=
  torusTransportBase_support _ _ _

theorem mem_baseChange_base_support_iff (a : d.rootIndex) :
    a ∈ d.toSplitPinning.base.support ↔
      (d.baseChangeRootDatumEquiv E).indexEquiv a ∈ (d.baseChange E).toSplitPinning.base.support := by
  show _ ↔ a ∈ (d.baseChange E).toSplitPinning.base.support
  rw [d.baseChange_base_support E]

/-- The weight transport carries roots to roots with the same index. -/
theorem weightTransport_root (a : d.rootIndex) :
    d.weightTransport E (d.toSplitPinning.rootDatum.root a) =
      (d.baseChange E).toSplitPinning.rootDatum.root a :=
  rfl

/-- The coroots of the base change are the coroots of `d`, transported by the tower
isomorphism. -/
theorem baseChange_coroot (a : d.rootIndex) :
    (d.baseChange E).toSplitPinning.rootDatum.coroot a =
      cocharacterLattice.congr (torusTowerIso k E K d.torus)
        (d.toSplitPinning.rootDatum.coroot a) :=
  rfl

/-- The weight transport preserves the pairing of a weight with every coroot. -/
theorem pairing_weightTransport_coroot (χ : characterLattice d.toSplitPinning.torus)
    (a : d.rootIndex) :
    (d.baseChange E).toSplitPinning.rootDatum.toLinearMap (d.weightTransport E χ)
        ((d.baseChange E).toSplitPinning.rootDatum.coroot a) =
      d.toSplitPinning.rootDatum.toLinearMap χ (d.toSplitPinning.rootDatum.coroot a) :=
  torusTransportRootDatum_pairing (torusTowerIso k E K d.torus) d.rootDatum χ
    (d.rootDatum.coroot a)

variable [LocallyOfFiniteType G.X.hom]

/-- **Star compatibility.** For `σ ∈ Gal(K/E)`, the star action of `σ` on the base change
corresponds, under the root-datum transport, to the star action of `σ` viewed in
`Gal(K/k)`. -/
theorem baseChangeRootDatumEquiv_comp_starAction (σ : K ≃ₐ[E] K) :
    RootPairing.Equiv.comp (d.baseChangeRootDatumEquiv E)
        (d.starAction (σ.restrictScalars k)).val =
      RootPairing.Equiv.comp ((d.baseChange E).starAction σ).val
        (d.baseChangeRootDatumEquiv E) :=
  StarActionFiniteStage.starAction_comp_of_weightMap_of_fields d (d.baseChange E)
    (d.baseChangeRootDatumEquiv E) (d.mem_baseChange_base_support_iff E)
    (σ.restrictScalars k) σ
    (fun χ => characterTowerEquiv_galoisRepresentation k E K d.torus σ χ)

/-- Star compatibility on weights. -/
theorem baseChange_starAction_weightTransport (σ : K ≃ₐ[E] K)
    (lam : characterLattice d.toSplitPinning.torus) :
    ((d.baseChange E).starAction σ).val.weightEquiv (d.weightTransport E lam) =
      d.weightTransport E ((d.starAction (σ.restrictScalars k)).val.weightEquiv lam) := by
  have h := congrArg (fun f : RootPairing.Equiv d.toSplitPinning.rootDatum
    (d.baseChange E).toSplitPinning.rootDatum => f.weightMap lam)
    (d.baseChangeRootDatumEquiv_comp_starAction E σ)
  exact h.symm

/-- The weight transport is equivariant for the star action of every `σ ∈ Gal(K/E)`; in
particular a weight fixed by `Gal(K/E)` for `d` goes to a weight fixed by the full star
action of the base change. The converse also holds. -/
theorem forall_fixingSubgroup_starAction_iff (F : IntermediateField k K)
    (lam : characterLattice d.toSplitPinning.torus) :
    (∀ σ ∈ F.fixingSubgroup, (d.starAction σ).val.weightEquiv lam = lam) ↔
      ∀ σ : K ≃ₐ[F] K,
        ((d.baseChange F).starAction σ).val.weightEquiv (d.weightTransport F lam) =
          d.weightTransport F lam := by
  constructor
  · intro h σ
    rw [baseChange_starAction_weightTransport]
    congr 1
    refine h _ ((IntermediateField.mem_fixingSubgroup_iff F _).mpr fun x hx => ?_)
    exact σ.commutes ⟨x, hx⟩
  · intro h σ hσ
    let σ' : K ≃ₐ[F] K := IntermediateField.fixingSubgroupEquiv F ⟨σ, hσ⟩
    have hσ' : σ'.restrictScalars k = σ := by
      ext x
      rfl
    apply (d.weightTransport F).injective
    rw [← hσ', ← baseChange_starAction_weightTransport]
    exact h σ'

end GaloisPinningData

end Langlands.GroupScheme
