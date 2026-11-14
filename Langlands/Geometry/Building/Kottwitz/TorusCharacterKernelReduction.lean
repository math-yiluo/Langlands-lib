import Langlands.GroupScheme.Rational.AffineCharacterTowerDescent
import Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelStatement
import Langlands.Geometry.Building.Kottwitz.TorusMapStatement
import Langlands.Geometry.Building.Kottwitz.NormalizedValuationStatement
import Langlands.Geometry.Building.KPCharacterValuationDescentProof
import Langlands.Geometry.Building.KPCharacterValuationExtension
import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.GroupScheme.GaloisPointTransitivity
import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Langlands.GroupScheme.Rational.CharacterBaseChange

/-! # Reduction of the torus character-kernel theorem to the norm law -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

/-- Evaluating a character after a comparison of test objects whose underlying scheme map is the
identity changes nothing. The test objects are written as `Over.mk f` and `Over.mk g` for
variables `f` and `g`, which keeps kernel conversion checks between them cheap. -/
theorem characterEval_comp_of_left_eq_id {S X : Scheme.{u}} {G : GroupScheme S}
    (χ : rationalCharacters G) {f g : X ⟶ S} (a : Over.mk f ⟶ Over.mk g) (ha : a.left = 𝟙 X)
    (y : Over.mk g ⟶ G.X) :
    characterEval χ (Over.mk f) (a ≫ y) = characterEval χ (Over.mk g) y := by
  rw [characterEval_naturality, ha]
  change Units.map (𝟙 X : X ⟶ X).appTop.hom.toMonoidHom _ = _
  simp

section Generic

variable {S S' S'' : Scheme.{u}} (b : S' ⟶ S) (c : S'' ⟶ S')

/-- The identity comparison between a test object over `S''` viewed over `S` directly and
through `S'`. -/
def compTestHom (V : Over S'') :
    (Over.map (c ≫ b)).obj V ⟶ (Over.map b).obj ((Over.map c).obj V) :=
  Over.homMk (𝟙 V.left) (by
    change 𝟙 V.left ≫ (V.hom ≫ c) ≫ b = V.hom ≫ c ≫ b
    rw [Category.id_comp, Category.assoc])

theorem compTestHom_left (V : Over S'') : (compTestHom b c V).left = 𝟙 V.left :=
  rfl

/-- Restricting a character base-changed along `d = c ≫ b` along any group comparison that is
compatible with the projections gives the iterated base change. -/
theorem characterRestrict_baseChange_comp (d : S'' ⟶ S) (h : c ≫ b = d)
    (G : GroupScheme S) (χ : rationalCharacters G)
    (e : (GroupScheme.baseChange c).obj ((GroupScheme.baseChange b).obj G) ⟶
      (GroupScheme.baseChange d).obj G)
    (he : e.hom.hom.left ≫ Limits.pullback.fst G.X.hom d =
      Limits.pullback.fst (Limits.pullback.snd G.X.hom b) c ≫ Limits.pullback.fst G.X.hom b) :
    characterRestrict e (rationalCharacters.baseChange d χ) =
      rationalCharacters.baseChange c (rationalCharacters.baseChange b χ) := by
  subst h
  apply rationalCharacters.ext_characterEval
  intro V x
  have hpt : baseChangePointsEquiv (c ≫ b) G V (x ≫ e.hom.hom) =
      compTestHom b c V ≫ baseChangePointsEquiv b G _
        (baseChangePointsEquiv c ((GroupScheme.baseChange b).obj G) V x) := by
    apply Over.OverMorphism.ext
    rw [baseChangePointsEquiv_left, Over.comp_left, Over.comp_left, baseChangePointsEquiv_left,
      baseChangePointsEquiv_left, compTestHom_left]
    change (x.left ≫ e.hom.hom.left) ≫ _ = 𝟙 V.left ≫ _
    rw [Category.id_comp, Category.assoc, he, Category.assoc]
    rfl
  rw [characterEval_characterRestrict, rationalCharacters.characterEval_baseChange,
    rationalCharacters.characterEval_baseChange, rationalCharacters.characterEval_baseChange,
    hpt]
  exact characterEval_comp_of_left_eq_id χ (f := V.hom ≫ c ≫ b) (g := (V.hom ≫ c) ≫ b)
    (compTestHom b c V) (compTestHom_left b c V) _

end Generic

section Tower

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]

/-- Restricting a directly base-changed rational character along the tower comparison gives
the iterated base change. -/
theorem characterRestrict_towerBaseChangeIso (G : GroupScheme (Spec (CommRingCat.of k)))
    (χ : rationalCharacters G) :
    characterRestrict (towerBaseChangeIso k L M G).hom
        (rationalCharacters.baseChange (baseMap k M) χ) =
      rationalCharacters.baseChange (baseMap L M)
        (rationalCharacters.baseChange (baseMap k L) χ) :=
  characterRestrict_baseChange_comp (baseMap k L) (baseMap L M) (baseMap k M)
    (baseMap_tower k L M) G χ (towerBaseChangeIso k L M G).hom
    (towerBaseChangeIso_hom_fst k L M G)

variable (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The commutative-group-scheme form of the tower comparison used by
`extendGeometricCocharacters`. -/
abbrev commTowerIso :
    (CommGroupScheme.baseChange (baseMap L M)).obj
        ((CommGroupScheme.baseChange (baseMap k L)).obj T) ≅
      (CommGroupScheme.baseChange (baseMap k M)).obj T :=
  CommGroupScheme.isoOfGroupIso (towerBaseChangeIso k L M T.toGrp)

/-- Character-lattice form of `characterRestrict_towerBaseChangeIso`. -/
theorem characterLattice_baseChange_tower (χ : characterLattice T) :
    characterLattice.baseChange (baseMap k M) T χ =
      characterLattice.congr (commTowerIso k L M T)
        (characterLattice.baseChange (baseMap L M) _
          (characterLattice.baseChange (baseMap k L) T χ)) := by
  apply (characterLattice.congr (commTowerIso k L M T)).symm.injective
  rw [AddEquiv.symm_apply_apply, characterLattice.congr_symm_apply]
  exact characterRestrict_towerBaseChangeIso k L M T.toGrp χ

/-- Pairing a directly base-changed character with an extended cocharacter is the pairing in
the intermediate field. -/
theorem latticePairing_extendGeometricCocharacters (χ : characterLattice T)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (baseMap k L)).obj T)) :
    latticePairing ((CommGroupScheme.baseChange (baseMap k M)).obj T)
        (characterLattice.baseChange (baseMap k M) T χ)
        (extendGeometricCocharacters k L M T ν) =
      latticePairing ((CommGroupScheme.baseChange (baseMap k L)).obj T)
        (characterLattice.baseChange (baseMap k L) T χ) ν := by
  rw [characterLattice_baseChange_tower k L M T χ]
  change latticePairing _ (characterLattice.congr (commTowerIso k L M T) _)
    (cocharacterLattice.congr (commTowerIso k L M T) _) = _
  rw [latticePairing_congr, latticePairing_baseChange]

/-- The relative norm of an extended point is its power by the relative degree. -/
theorem relativeNorm_relativeExtend [FiniteDimensional L M] [IsGalois L M] [IsAffine T.X.left]
    (y : affinePoints T.toGrp (CommAlgCat.of k L)) :
    GaloisPoint.relativeNorm k L M T (GaloisPoint.relativeExtend k L M T.toGrp y) =
      y ^ Fintype.card (M ≃ₐ[L] M) := by
  apply GaloisPoint.relativeExtend_injective k L M T.toGrp
  rw [GaloisPoint.relativeExtend_norm, map_pow]
  simp only [GaloisPoint.relativeConjugate_extend, Finset.prod_const, Finset.card_univ]

/-- Extending a rational point in two steps and comparing with the direct base change gives
the direct extension. -/
theorem towerBaseChangeIso_rationalExtend (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] (x : rationalPoints G) :
    rationalPoints.map (towerBaseChangeIso k L M G).hom
        (rationalExtend L M (baseChanged k L G) (rationalExtend k L G x)) =
      rationalExtend k M G x := by
  apply (baseChangeCoeffEquiv k M G).injective
  rw [baseChangeCoeffEquiv_towerBaseChangeIso, baseChangeCoeffEquiv_rationalExtend,
    coefficientBaseChangeEquiv_extend, coefficientBaseChangeEquiv_rationalCoeffEquiv,
    baseChangeCoeffEquiv_rationalExtend, GaloisPoint.relativeExtend_extend,
    baseChangeCoeffEquiv_rationalExtend]

end Tower

/-- Actual base changes of affine group schemes over fields have affine total spaces. -/
instance baseChanged_isAffine (k L : Type u) [Field k] [Field L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left] :
    IsAffine (baseChanged k L G).X.left := by
  exact Langlands.GroupScheme.AffineCharacterTowerDescent.baseChanged_isAffine L G

/-- The pairing with a base-changed character vanishes on every cocharacter whose image in the
coinvariants for some subgroup of the Galois group is torsion. -/
theorem latticePairing_baseChange_eq_zero_of_nsmul (k E : Type u) [Field k] [Field E]
    [Algebra k E] (T : CommGroupScheme (Spec (CommRingCat.of k))) (H : Subgroup (E ≃ₐ[k] E))
    (χ : characterLattice T)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
    {m : ℕ} (hm : m ≠ 0)
    (h : m • Representation.Coinvariants.mk
      ((cocharacterLattice.galoisRepresentation k E T).comp H.subtype) ν = 0) :
    latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      (characterLattice.baseChange (algebraBaseMap k E) T χ) ν = 0 := by
  let φ := latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
    (characterLattice.baseChange (algebraBaseMap k E) T χ)
  have hφ : ∀ σ : H,
      φ ∘ₗ ((cocharacterLattice.galoisRepresentation k E T).comp H.subtype) σ = φ := by
    intro σ
    apply LinearMap.ext
    intro ν'
    change latticePairing _ (characterLattice.baseChange (algebraBaseMap k E) T χ)
        (cocharacterLattice.galoisRepresentation k E T σ.1 ν') =
      latticePairing _ (characterLattice.baseChange (algebraBaseMap k E) T χ) ν'
    rw [latticePairing_galoisRepresentation_right,
      characterLattice.galoisRepresentation_baseChange]
  have h' := congrArg (Representation.Coinvariants.lift _ φ hφ) h
  rw [map_nsmul, map_zero, Representation.Coinvariants.lift_mk] at h'
  exact (smul_eq_zero.mp h').resolve_left hm

section Local

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

instance intermediateField_isScalarTower_sepClosure
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) :
    IsScalarTower F L (SeparableClosure F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
  (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap F L)).obj T).toGrp)

/-- The norm law at one splitting field computes a power of the Kottwitz value of an
`F`-point. -/
theorem pow_card_eq_of_torusNormLawAt
    (κ : torusKPoints F F T →* Multiplicative (TorusTarget F F T))
    (hκ : TorusNormLawAt F F T L hL κ) (t0 : rationalPoints T.toGrp) :
    κ (GaloisPoint.extend F (UnramifiedClosure F) T.toGrp (rationalCoeffEquiv F T.toGrp t0)) ^
        Fintype.card (L ≃ₐ[UnramifiedClosure F] L) =
      Multiplicative.ofAdd
        (inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
          (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T)
          (extendGeometricCocharacters F L (SeparableClosure F) T
            (splitValuation ((CommGroupScheme.baseChange (baseMap F L)).obj T) hL
              (normalizedIntermediateValuation F L)
              (rationalExtend F L T.toGrp t0)).toAdd)) := by
  have h := hκ (rationalExtend F L T.toGrp t0)
  rw [baseChangeCoeffEquiv_rationalExtend,
    ← GaloisPoint.relativeExtend_extend F (UnramifiedClosure F) L,
    relativeNorm_relativeExtend, map_pow] at h
  exact h


/-- An `F`-point in the character-valuation kernel extends into the character-valuation kernel
over the maximal unramified extension. -/
theorem rationalExtend_mem_characterValuationKernel_unramified
    (t0 : rationalPoints T.toGrp)
    (ht0 : t0 ∈ characterValuationKernel (ValuativeRel.valuation F) T.toGrp) :
    t0 ∈ (characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F)
      (baseChanged F (UnramifiedClosure F) T.toGrp)).comap
        (rationalExtend F (UnramifiedClosure F) T.toGrp) := by
  rw [characterValuationKernelDescent_proof F T.toGrp,
    ← characterValuationKernel_eq_rationalCommonNormKernel]
  exact ht0

/-- Two-step form: the unramified extension of a kernel point extends further into the
character-valuation kernel of the iterated base change to `L`. -/
theorem rationalExtend_mem_characterValuationKernel_tower
    (t0 : rationalPoints T.toGrp)
    (ht0 : t0 ∈ characterValuationKernel (ValuativeRel.valuation F) T.toGrp) :
    rationalExtend (UnramifiedClosure F) L (baseChanged F (UnramifiedClosure F) T.toGrp)
        (rationalExtend F (UnramifiedClosure F) T.toGrp t0) ∈
      characterValuationKernel (intermediateValuation F L)
        (baseChanged (UnramifiedClosure F) L (baseChanged F (UnramifiedClosure F) T.toGrp)) :=
  characterValuationKernel_le_comap (k := UnramifiedClosure F) (L := L)
    (LocalGalois.Separable.fixedFieldValuation F) (intermediateValuation F L)
    (intermediateValuation_conjugate F L) (baseChanged F (UnramifiedClosure F) T.toGrp)
    (rationalExtend_mem_characterValuationKernel_unramified F T t0 ht0)

/-- The two-step extension of a kernel point, transported along the tower comparison, lies in
the character-valuation kernel of the direct base change to `L`. -/
theorem map_rationalExtend_mem_characterValuationKernel_tower
    (t0 : rationalPoints T.toGrp)
    (ht0 : t0 ∈ characterValuationKernel (ValuativeRel.valuation F) T.toGrp) :
    rationalPoints.map (towerBaseChangeIso F (UnramifiedClosure F) L T.toGrp).hom
        (rationalExtend (UnramifiedClosure F) L (baseChanged F (UnramifiedClosure F) T.toGrp)
          (rationalExtend F (UnramifiedClosure F) T.toGrp t0)) ∈
      characterValuationKernel (intermediateValuation F L) (baseChanged F L T.toGrp) :=
  map_characterValuationKernel_le _ (towerBaseChangeIso F (UnramifiedClosure F) L T.toGrp).hom
    (Subgroup.mem_map_of_mem _ (rationalExtend_mem_characterValuationKernel_tower F T L t0 ht0))

/-- An `F`-point in the character-valuation kernel extends into the character-valuation kernel
over a finite Galois extension of the maximal unramified extension. -/
theorem rationalExtend_mem_characterValuationKernel_split
    (t0 : rationalPoints T.toGrp)
    (ht0 : t0 ∈ characterValuationKernel (ValuativeRel.valuation F) T.toGrp) :
    rationalExtend F L T.toGrp t0 ∈
      characterValuationKernel (intermediateValuation F L) (baseChanged F L T.toGrp) := by
  have h := map_rationalExtend_mem_characterValuationKernel_tower F T L t0 ht0
  rwa [towerBaseChangeIso_rationalExtend] at h

/-- An `F`-point in the character-valuation kernel has trivial split valuation after extension
to a splitting field. -/
theorem splitValuation_rationalExtend_eq_one
    (hv : IsNormalizedIntermediateValuation F L (normalizedIntermediateValuation F L))
    (t0 : rationalPoints T.toGrp)
    (ht0 : t0 ∈ characterValuationKernel (ValuativeRel.valuation F) T.toGrp) :
    splitValuation ((CommGroupScheme.baseChange (baseMap F L)).obj T) hL
      (normalizedIntermediateValuation F L) (rationalExtend F L T.toGrp t0) = 1 := by
  have h3 := rationalExtend_mem_characterValuationKernel_split F T L t0 ht0
  rw [mem_characterValuationKernel] at h3
  apply Multiplicative.toAdd.injective
  apply (cocharacterDualEquiv _ hL).injective
  apply LinearMap.ext
  intro χ
  rw [cocharacterDualEquiv_apply, cocharacterDualEquiv_apply, toAdd_one, map_zero,
    splitValuation_pairing]
  have h5 := hv.1.eq_one_iff_eq_one.mpr (h3 ((rationalCharacters.equivCharacterLattice _).symm χ))
  exact toAdd_eq_zero.mpr ((IntegerValuation.orderUnits_eq_one_iff _ _).mpr h5)

omit [IsAffine T.X.left] [FiniteDimensional (UnramifiedClosure F) L]
  [IsGalois (UnramifiedClosure F) L] in
/-- If the image of the split valuation in the inertia coinvariants is torsion, the original
`F`-point lies in the character-valuation kernel. -/
theorem mem_characterValuationKernel_of_isOfFinOrder
    (hv : IsNormalizedIntermediateValuation F L (normalizedIntermediateValuation F L))
    (t0 : rationalPoints T.toGrp)
    (h : IsOfFinOrder (Multiplicative.ofAdd
        (inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
          (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T)
          (extendGeometricCocharacters F L (SeparableClosure F) T
            (splitValuation ((CommGroupScheme.baseChange (baseMap F L)).obj T) hL
              (normalizedIntermediateValuation F L)
              (rationalExtend F L T.toGrp t0)).toAdd)))) :
    t0 ∈ characterValuationKernel (ValuativeRel.valuation F) T.toGrp := by
  obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  rw [← ofAdd_nsmul, ofAdd_eq_one] at hpow
  rw [mem_characterValuationKernel]
  intro χ
  have h0 := latticePairing_baseChange_eq_zero_of_nsmul F (SeparableClosure F) T
    (relativeInertia F (UnramifiedClosure F) (SeparableClosure F))
    (rationalCharacters.equivCharacterLattice T χ) _ hm.ne' hpow
  rw [latticePairing_extendGeometricCocharacters F L (SeparableClosure F) T,
    splitValuation_pairing] at h0
  change (IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
    (rationalCharacterEval (rationalCharacters.baseChange (baseMap F L) χ)
      (rationalExtend F L T.toGrp t0))).toAdd = 0 at h0
  rw [rationalCharacterEval_extend, toAdd_eq_zero, IntegerValuation.orderUnits_eq_one_iff,
    hv.1.eq_one_iff_eq_one, intermediateValuation_apply, Units.coe_map] at h0
  exact (Valuation.HasExtension.val_map_eq_one_iff (ValuativeRel.valuation F)
    (LocalGalois.Separable.sepClosureValuation F) _).mp h0

end Local

/-- The two unpublished inputs of the reduction: KP Proposition 11.1.1 for the torus Kottwitz
homomorphisms and the integer normalization of the splitting-field valuations. -/
def TorusCharacterKernelInputs : Prop :=
  TorusKottwitzExistenceStatement.{u} ∧ NormalizedIntermediateValuationStatement.{u}

/-- KP Lemma 11.1.3 and its rational restriction follow from the two inputs. -/
theorem TorusCharacterKernelInputs.torusCharacterKernel
    (h : TorusCharacterKernelInputs.{u}) : TorusCharacterKernelStatement.{u} := by
  obtain ⟨hE, hN⟩ := h
  intro F _ _ _ _ T hT
  let : IsAffine T.X.left := torusIsAffine F T hT
  have hκ := (hE F F T hT).2.1
  obtain ⟨L, _, _, hsplit⟩ := exists_finiteGaloisSplittingField_inside (SeparableClosure F)
    (baseChanged F (UnramifiedClosure F) T.toGrp)
    (IsTorus.baseChange (K := UnramifiedClosure F) hT)
  have hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap F L)).obj T).toGrp :=
    IsSplitTorus.of_iso (towerBaseChangeIso F (UnramifiedClosure F) L T.toGrp).symm hsplit
  have hv := normalizedIntermediateValuation_spec F L (hN F L).exists
  have hpow := pow_card_eq_of_torusNormLawAt F T L hL _ (hκ L hL)
  have hcard : 0 < Fintype.card (L ≃ₐ[UnramifiedClosure F] L) := Fintype.card_pos
  ext t0
  rw [Subgroup.mem_comap, CommGroup.mem_torsion]
  constructor
  · intro ht0
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨_, hcard, ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hpow t0,
      splitValuation_rationalExtend_eq_one F T L hL hv t0 ht0, toAdd_one, map_zero, map_zero,
      ofAdd_zero]
  · intro ht0
    apply mem_characterValuationKernel_of_isOfFinOrder F T L hL hv t0
    rw [← hpow t0]
    exact ht0.pow

end Langlands.Geometry.Building.Kottwitz
