import Langlands.GroupScheme.Reductive.StarActionFiniteStageProof

/-! # Finite-stage pinning comparison with the actual torus and character map -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.StarActionFiniteStage

section Character

variable {B SL SK : Scheme.{u}} (bL : SL ⟶ B) (j : SK ⟶ SL)
  {T' T : CommGroupScheme B} (t : T' ≅ T) (bK : SK ⟶ B) (hc : j ≫ bL = bK)

/-- The actual tower character map, after transporting the original torus along `t`. -/
def stageCharacter
    (χ : characterLattice ((CommGroupScheme.baseChange bL).obj T')) :
    characterLattice ((CommGroupScheme.baseChange bK).obj T) :=
  towerCharacterOf bL j T bK hc ((CommGroupScheme.baseChange bL).map t.inv ≫ χ)

end Character

local instance stageTorusBaseChangeAffine (k E : Type u) [Field k] [Field E] [Algebra k E]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

section Stage

variable {k L K : Type u} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
  [Algebra L K] [Algebra.IsAlgebraic k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

/-- Intermediate-stage pinning data with a torus-compatible identification with the
original torus and the actual character base-change map on their full root data. -/
theorem exists_stage_torus (d : GaloisPinningData k K G)
    (hc : algebraBaseMap L K ≫ algebraBaseMap k L = algebraBaseMap k K)
    (hsplit : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d.torus).toGrp) :
    ∃ (d' : GaloisPinningData k L G) (t : d'.torus ≅ d.torus)
      (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum),
      CommGroupScheme.groupHom t.hom ≫ d.inclusion = d'.inclusion ∧
      (∀ χ, e.weightMap χ = stageCharacter (algebraBaseMap k L) (algebraBaseMap L K)
        t (algebraBaseMap k K) hc χ) ∧
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
  refine ⟨d', Iso.refl d.torus, e, ?_, ?_, hb, fun σ τ hστ => ?_⟩
  · change (𝟙 d.torus.toGrp) ≫ d.inclusion = d.inclusion
    exact Category.id_comp _
  · intro χ
    change e.weightMap χ = towerCharacterOf (algebraBaseMap k L) (algebraBaseMap L K)
      d.torus (algebraBaseMap k K) hc
        ((CommGroupScheme.baseChange (algebraBaseMap k L)).map (𝟙 d.torus) ≫ χ)
    rw [(CommGroupScheme.baseChange (algebraBaseMap k L)).map_id, Category.id_comp]
    exact he χ
  refine starAction_comp_of_weightMap d' d e hb σ τ (fun χ => ?_)
  -- `rw` cannot see `e` through the projections of `d'`; chain the equalities in term mode.
  exact (he _).trans ((towerCharacterOf_transport (algebraBaseMap k L) (algebraBaseMap L K)
    d.torus (algebraBaseMap k K) hc (galoisBaseMap k L σ) (galoisBaseMap_over k L σ)
    (galoisBaseMap k K τ) (galoisBaseMap_over k K τ)
    (algebraBaseMap_comp_galoisBaseMap σ τ hστ) χ).trans
    (congrArg (characterLattice.galoisRepresentation k K d.torus τ) (he χ).symm))


end Stage

/-- A finite Galois stage retains the actual torus inclusion, its character base-change
map, the chosen base, and the star actions of every compatible pair of automorphisms. -/
theorem exists_finiteGaloisStage_torus {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : GaloisPinningData k (SeparableClosure k) G) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : IsGalois k L) (ι : L →ₐ[k] SeparableClosure k),
      let : Algebra L (SeparableClosure k) := ι.toRingHom.toAlgebra
      ∃ (hc : algebraBaseMap L (SeparableClosure k) ≫ algebraBaseMap k L =
          algebraBaseMap k (SeparableClosure k))
        (d' : GaloisPinningData k L G) (t : d'.torus ≅ d.torus)
        (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum),
        CommGroupScheme.groupHom t.hom ≫ d.inclusion = d'.inclusion ∧
        (∀ χ, e.weightMap χ = stageCharacter (algebraBaseMap k L)
          (algebraBaseMap L (SeparableClosure k)) t (algebraBaseMap k (SeparableClosure k)) hc χ) ∧
        (∀ a, a ∈ d'.toSplitPinning.base.support ↔
          e.indexEquiv a ∈ d.toSplitPinning.base.support) ∧
        ∀ (σ : L ≃ₐ[k] L) (τ : SeparableClosure k ≃ₐ[k] SeparableClosure k),
          (∀ x, τ (ι x) = ι (σ x)) →
            RootPairing.Equiv.comp e (d'.starAction σ).val =
              RootPairing.Equiv.comp (d.starAction τ).val e := by
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
  obtain ⟨d', t, e, hi, he, hb, hs⟩ := exists_stage_torus d hc hsplit
  exact ⟨L, inferInstance, inferInstance, hfin, hgal, ι, hc, d', t, e, hi, he, hb, hs⟩

end Langlands.GroupScheme.StarActionFiniteStage
