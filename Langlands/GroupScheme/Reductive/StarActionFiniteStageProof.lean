import Langlands.GroupScheme.Reductive.StarActionFiniteStageStatement
import Langlands.GroupScheme.Reductive.StarActionFiniteStageTower
import Langlands.GroupScheme.Reductive.AbsoluteStarAction
import Langlands.GroupScheme.Reductive.AlgebraicExtensionReflectionProof
import Langlands.GroupScheme.Reductive.RootDatumBaseChangeProof
import Langlands.GroupScheme.Descent.ClosedSubgroups
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # The star action over the separable closure is realized at a finite Galois stage -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace StarActionFiniteStage

/-! ### Lattice base change of a root datum, as an equivalence -/

section Lattice

variable {L K : Type u} [Field L] [Field K]
  (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of L))
  (T : CommGroupScheme (Spec (CommRingCat.of L))) (hT : IsSplitTorus T.toGrp)
  {J : Type u} (P : RootDatum J (characterLattice T) (cocharacterLattice T))

/-- The canonical equivalence of a root datum of a split torus with its transport to the
pulled-back torus: base change of characters and cocharacters, with the same indices. -/
def latticeBaseChangeEquiv : RootPairing.Equiv P (SplitRootDatum.baseChange b T hT P) where
  weightMap := (characterLattice.baseChangeEquiv b T hT).toIntLinearEquiv
  coweightMap := (cocharacterLattice.baseChangeEquiv b T hT).symm.toIntLinearEquiv
  indexEquiv := Equiv.refl J
  weight_coweight_transpose := by
    ext y x
    obtain ⟨z, rfl⟩ := (cocharacterLattice.baseChangeEquiv b T hT).surjective y
    change (SplitRootDatum.baseChange b T hT P).toLinearMap
      (characterLattice.baseChange b T x) (cocharacterLattice.baseChange b T z) =
      P.toLinearMap x
        ((cocharacterLattice.baseChangeEquiv b T hT).symm
          ((cocharacterLattice.baseChangeEquiv b T hT) z))
    rw [AddEquiv.symm_apply_apply]
    exact SplitRootDatum.baseChange_pairing b T hT P x z
  root_weightMap := rfl
  coroot_coweightMap := by
    funext a
    exact (cocharacterLattice.baseChangeEquiv b T hT).symm_apply_apply (P.coroot a)
  bijective_weightMap := (characterLattice.baseChangeEquiv b T hT).bijective
  bijective_coweightMap := (cocharacterLattice.baseChangeEquiv b T hT).symm.bijective

theorem latticeBaseChangeEquiv_weightMap (χ : characterLattice T) :
    (latticeBaseChangeEquiv b T hT P).weightMap χ = characterLattice.baseChange b T χ := rfl

end Lattice

local instance baseChangeAffine (k E : Type u) [Field k] [Field E] [Algebra k E]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-! ### Star actions over two fields -/

section Star

variable {k L K : Type u} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

/-- If a base-preserving equivalence of root data intertwines the Galois actions of `σ` and
`τ` on characters, it intertwines their star actions. -/
theorem starAction_comp_of_weightMap (d' : GaloisPinningData k L G)
    (d : GaloisPinningData k K G)
    (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum)
    (hb : ∀ a, a ∈ d'.toSplitPinning.base.support ↔
      e.indexEquiv a ∈ d.toSplitPinning.base.support)
    (σ : L ≃ₐ[k] L) (τ : K ≃ₐ[k] K)
    (hx : ∀ χ, e.weightMap (characterLattice.galoisRepresentation k L d'.torus σ χ) =
      characterLattice.galoisRepresentation k K d.torus τ (e.weightMap χ)) :
    RootPairing.Equiv.comp e (d'.starAction σ).val =
      RootPairing.Equiv.comp (d.starAction τ).val e := by
  have hconj : StarActionIndependence.conjAut e (d'.galoisAction σ) = d.galoisAction τ := by
    apply StarActionIndependence.equiv_ext_of_weightMap
    intro y
    rw [StarActionIndependence.conjAut_weightMap]
    obtain ⟨χ, rfl⟩ := e.weightEquiv.surjective y
    rw [LinearEquiv.symm_apply_apply]
    change e.weightMap ((d'.galoisAction σ).weightMap χ) =
      (d.galoisAction τ).weightMap (e.weightMap χ)
    rw [StarActionIndependence.galoisAction_weightMap_apply,
      StarActionIndependence.galoisAction_weightMap_apply]
    exact hx χ
  have hw : d.galoisAction τ * (StarActionIndependence.conjAut e (d'.galoisAction σ))⁻¹ ∈
      d.toSplitPinning.rootDatum.weylGroup := by
    rw [hconj, mul_inv_cancel]
    exact one_mem _
  exact comp_basedRootDatumProjection d'.toSplitPinning d.toSplitPinning e hb
    (d'.galoisAction σ) (d.galoisAction τ) hw

end Star

/-! ### Galois pinning data at an intermediate stage -/

section Stage

variable {k L K : Type u} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
  [Algebra L K] [Algebra.IsAlgebraic k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

omit [Algebra.IsAlgebraic k K] in
/-- Spectra reverse the commutation `ι ∘ σ = τ ∘ ι` of field maps. -/
theorem algebraBaseMap_comp_galoisBaseMap (σ : L ≃ₐ[k] L) (τ : K ≃ₐ[k] K)
    (h : ∀ x, τ (algebraMap L K x) = algebraMap L K (σ x)) :
    algebraBaseMap L K ≫ galoisBaseMap k L σ = galoisBaseMap k K τ ≫ algebraBaseMap L K := by
  simp only [algebraBaseMap, galoisBaseMap, ← Spec.map_comp]
  congr 1
  ext x
  exact (h x).symm

/-- Galois pinning data over `K` whose torus splits over an intermediate field `L` are matched
by Galois pinning data over `L`, through a base-preserving equivalence of root data that
intertwines the star actions of compatible automorphisms. -/
theorem exists_stage (d : GaloisPinningData k K G)
    (hc : algebraBaseMap L K ≫ algebraBaseMap k L = algebraBaseMap k K)
    (hsplit : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus).toGrp) :
    ∃ (d' : GaloisPinningData k L G)
      (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum),
      (∀ a, a ∈ d'.toSplitPinning.base.support ↔
        e.indexEquiv a ∈ d.toSplitPinning.base.support) ∧
      ∀ (σ : L ≃ₐ[k] L) (τ : K ≃ₐ[k] K),
        (∀ x, τ (algebraMap L K x) = algebraMap L K (σ x)) →
          RootPairing.Equiv.comp e (d'.starAction σ).val =
            RootPairing.Equiv.comp (d.starAction τ).val e := by
  -- Connected reductivity over `k`, `L` and, along `L → K`, over `K`.
  have hG : IsConnectedReductive G :=
    connectedReductiveAlgebraicExtensionReflection k K G d.isConnectedReductive
  have hGL := connectedReductiveFieldExtensionStatement k L G hG
  have hGLK := connectedReductiveFieldExtensionStatement L K _ hGL
  have := hGL.smooth
  -- The tower isomorphisms comparing `(·)_K` with `((·)_L)_K`.
  have hsq := towerIsoOf_square (algebraBaseMap k L) (algebraBaseMap L K) d.torus
    (algebraBaseMap k K) hc d.inclusion
  have heq := baseChange_map_eq_groupTowerIsoOf (algebraBaseMap k L) (algebraBaseMap L K)
    (algebraBaseMap k K) hc d.inclusion
  have hiLK : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap L K)).obj
        ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus))
      ((GroupScheme.baseChange (algebraBaseMap L K)).map
        ((GroupScheme.baseChange (algebraBaseMap k L)).map d.inclusion)) :=
    IsMaximalTorus.of_eq_iso_comp_comp_iso
      (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj d.torus)
      (T' := (CommGroupScheme.baseChange (algebraBaseMap L K)).obj
        ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus))
      d.isMaximalTorus
      (groupTowerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) (algebraBaseMap k K) hc
        d.torus.toGrp).symm
      (groupTowerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) (algebraBaseMap k K) hc G)
      heq
  -- Closedness and maximality of `T_L` in `G_L`, by descent along `L → K`.
  have : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj d.torus.toGrp).X.hom :=
    hsplit.isAffineHom
  have : IsAffine ((GroupScheme.baseChange (algebraBaseMap k L)).obj d.torus.toGrp).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj d.torus.toGrp).X.hom
  have : IsAffine ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom
  obtain ⟨hsurj, hflat, -⟩ := fieldExtension_fpqc L K
  have hclL : IsClosedSubgroup ((GroupScheme.baseChange (algebraBaseMap k L)).map d.inclusion) :=
    IsClosedSubgroup.of_baseChange_of_isAffine (algebraBaseMap L K) hiLK.2.1
  have hiL : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map d.inclusion) :=
    (maximalTorusBaseChange L K ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map d.inclusion) hsplit.isTorus hclL).mpr hiLK
  -- A reduced root datum of `(G_L, T_L)` and its transport to `K`.
  obtain ⟨J', hJ', P', hP', hred'⟩ := rootDatumExistence L _ hGL _ hsplit _ hiL
  have hTLK := hsplit.baseChange (algebraBaseMap L K)
  have hP'K := hP'.baseChange (K := K) ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus) hsplit
    ((GroupScheme.baseChange (algebraBaseMap k L)).map d.inclusion)
  let E₁ := latticeBaseChangeEquiv (algebraBaseMap L K) _ hsplit P'
  let E₂ := rootDatumEquivOfTorusCompatibleIso d.isConnectedReductive hGLK d.isSplitTorus hTLK
    d.isMaximalTorus hiLK
    (groupTowerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) (algebraBaseMap k K) hc G)
    (towerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) d.torus (algebraBaseMap k K) hc)
    hsq d.isRootDatum hP'K
  let e := RootPairing.Equiv.comp E₂ E₁
  have he : ∀ χ, e.weightMap χ = towerCharacterOf (algebraBaseMap k L) (algebraBaseMap L K)
      d.torus (algebraBaseMap k K) hc χ := fun χ =>
    rootDatumEquivOfTorusCompatibleIso_weightMap d.isConnectedReductive hGLK d.isSplitTorus hTLK
      d.isMaximalTorus hiLK
      (groupTowerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) (algebraBaseMap k K) hc G)
      (towerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) d.torus (algebraBaseMap k K) hc)
      hsq d.isRootDatum hP'K (E₁.weightMap χ)
  -- The base over `L` pulled back from the base of `d`.
  let base' : P'.Base := d.base.map (RootPairing.Equiv.symm _ _ e)
  let d' : GaloisPinningData k L G :=
    { torus := d.torus
      inclusion := d.inclusion
      isConnectedReductive := hGL
      isSplitTorus := hsplit
      isMaximalTorus := hiL
      rootIndex := J'
      finiteRootIndex := hJ'
      rootDatum := P'
      isRootDatum := hP'
      isReduced := hred'
      base := base'
      pinning := RootPinning.ofSplitMaximalTorus hGL hsplit _ hiL P' hP' base' }
  have hb : ∀ a, a ∈ d'.toSplitPinning.base.support ↔
      e.indexEquiv a ∈ d.toSplitPinning.base.support := by
    classical
    intro a
    change a ∈ (d.base.map (RootPairing.Equiv.symm _ _ e)).support ↔ _
    rw [RootPairing.Base.support_map_eq, Finset.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      change e.indexEquiv (e.indexEquiv.symm c) ∈ d.base.support
      rwa [Equiv.apply_symm_apply]
    · intro h
      exact ⟨e.indexEquiv a, h, e.indexEquiv.symm_apply_apply a⟩
  refine ⟨d', e, hb, fun σ τ hστ => ?_⟩
  refine starAction_comp_of_weightMap d' d e hb σ τ (fun χ => ?_)
  -- `rw` cannot see `e` through the projections of `d'`; chain the equalities in term mode.
  exact (he _).trans ((towerCharacterOf_transport (algebraBaseMap k L) (algebraBaseMap L K)
    d.torus (algebraBaseMap k K) hc (galoisBaseMap k L σ) (galoisBaseMap_over k L σ)
    (galoisBaseMap k K τ) (galoisBaseMap_over k K τ)
    (algebraBaseMap_comp_galoisBaseMap σ τ hστ) χ).trans
    (congrArg (characterLattice.galoisRepresentation k K d.torus τ) (he χ).symm))

end Stage

end StarActionFiniteStage

/-- **The star action is realized at a finite Galois stage.** The maximal torus of `d`
splits over a finite Galois extension `L` of `k`, which embeds in the separable closure; Galois
pinning data over `L` with the same torus and the base pulled back from `d` have the
required base-preserving root-datum equivalence. -/
theorem starActionFiniteStage : StarActionFiniteStageStatement.{u} := by
  intro k _ G _ _ d
  have hT : IsTorus d.torus.toGrp :=
    ⟨SeparableClosure k, inferInstance, inferInstance, d.isSplitTorus⟩
  obtain ⟨L, _, _, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k d.torus.toGrp hT
  let ι : L →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra L (SeparableClosure k) := ι.toRingHom.toAlgebra
  have hc : algebraBaseMap L (SeparableClosure k) ≫ algebraBaseMap k L =
      algebraBaseMap k (SeparableClosure k) := by
    simp only [algebraBaseMap, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg Subtype.val (ι.commutes x)
  obtain ⟨d', e, hb, hstar⟩ := StarActionFiniteStage.exists_stage d hc hsplit
  exact ⟨L, inferInstance, inferInstance, hfin, hgal, ι, d', e, hb,
    fun σ τ hστ => hstar σ τ hστ⟩

end Langlands.GroupScheme
