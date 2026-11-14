import Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelReduction
import Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelStatement
import Langlands.Geometry.Building.Kottwitz.TorusMapStatement
import Langlands.Geometry.Building.Kottwitz.NormalizedValuationStatement
import Langlands.Geometry.Building.KPCharacterValuationDescentProof
import Langlands.Geometry.Building.KPCharacterValuationExtension
import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.GaloisPointTransitivity
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleRestriction

/-! # Reduction of the torus character-kernel theorem -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

section Tower

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]

/-- Base change of a character in two steps is direct base change, under the standard
comparison along an equality `c ≫ b = d` of structure maps. -/
theorem characterLattice_baseChange_comp_eq {B S' S'' : Scheme.{u}}
    (b : S' ⟶ B) (c : S'' ⟶ S') (d : S'' ⟶ B) (h : c ≫ b = d)
    (T : CommGroupScheme B) (χ : characterLattice T) :
    (CommGroupScheme.isoOfGroupIso
        (T := (CommGroupScheme.baseChange c).obj ((CommGroupScheme.baseChange b).obj T))
        (U := (CommGroupScheme.baseChange d).obj T)
        ((baseChangeCompIso b c T.toGrp).symm ≪≫
          eqToIso (congrArg (fun e => (Over.pullback e).mapGrp.obj T.toGrp) h))).hom ≫
        characterLattice.baseChange d T χ =
      characterLattice.baseChange c ((CommGroupScheme.baseChange b).obj T)
        (characterLattice.baseChange b T χ) := by
  subst h
  rw [← StarActionFiniteStage.towerCharacter_baseChange b c T χ]
  unfold StarActionFiniteStage.towerCharacter
  have hid : (CommGroupScheme.isoOfGroupIso
        (T := (CommGroupScheme.baseChange c).obj ((CommGroupScheme.baseChange b).obj T))
        (U := (CommGroupScheme.baseChange (c ≫ b)).obj T)
        ((baseChangeCompIso b c T.toGrp).symm ≪≫
          eqToIso (congrArg (fun e => (Over.pullback e).mapGrp.obj T.toGrp)
            (rfl : c ≫ b = c ≫ b)))).hom ≫
        (StarActionFiniteStage.towerIso b c T).hom = 𝟙 _ := by
    apply congrArg Additive.ofMul
    exact (baseChangeCompIso b c T.toGrp).inv_hom_id
  rw [← Category.assoc, hid, Category.id_comp]

end Tower

section TowerFields

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]

/-- Base change of a character in two steps is direct base change under the tower
comparison. -/
theorem characterLattice_baseChange_tower_hom
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (χ : characterLattice T) :
    (CommGroupScheme.isoOfGroupIso (towerBaseChangeIso k L M T.toGrp)).hom ≫
        characterLattice.baseChange (baseMap k M) T χ =
      characterLattice.baseChange (baseMap L M)
        ((CommGroupScheme.baseChange (baseMap k L)).obj T)
        (characterLattice.baseChange (baseMap k L) T χ) :=
  characterLattice_baseChange_comp_eq (baseMap k L) (baseMap L M) (baseMap k M)
    (baseMap_tower k L M) T χ

set_option maxHeartbeats 200000 in
/-- The tower comparison carries the character kernel after two successive extensions into
the character kernel after the direct extension. -/
theorem towerBaseChangeIso_map_mem_characterValuationKernel {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation M Γ)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (y : rationalPoints (baseChanged L M (baseChanged k L G)))
    (h : y ∈ characterValuationKernel v (baseChanged L M (baseChanged k L G))) :
    rationalPoints.map (towerBaseChangeIso k L M G).hom y ∈
      characterValuationKernel v (baseChanged k M G) :=
  map_characterValuationKernel_le v _ ⟨y, h, rfl⟩

set_option maxHeartbeats 200000 in
/-- Transport of character-kernel membership along the tower comparison of extended points. -/
theorem rationalExtend_mem_characterValuationKernel_of_map_tower {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation M Γ)
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left] (x : rationalPoints G)
    (h : rationalPoints.map (towerBaseChangeIso k L M G).hom
        (rationalExtend L M (baseChanged k L G) (rationalExtend k L G x)) ∈
      characterValuationKernel v (baseChanged k M G)) :
    rationalExtend k M G x ∈ characterValuationKernel v (baseChanged k M G) := by
  rw [← towerBaseChangeIso_rationalExtend k L M G x]
  exact h

omit [Algebra k M] [IsScalarTower k L M] in
set_option maxHeartbeats 200000 in
/-- Unfolding membership in the inverse image under the second extension. -/
theorem rationalExtend_rationalExtend_mem_of_mem_comap {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation M Γ)
    (G : GroupScheme (Spec (CommRingCat.of k))) (x : rationalPoints G)
    (h : rationalExtend k L G x ∈
      (characterValuationKernel v (baseChanged L M (baseChanged k L G))).comap
        (rationalExtend L M (baseChanged k L G))) :
    rationalExtend L M (baseChanged k L G) (rationalExtend k L G x) ∈
      characterValuationKernel v (baseChanged L M (baseChanged k L G)) :=
  h

set_option maxHeartbeats 200000 in
/-- Character-kernel membership after two successive extensions gives membership after the
direct extension. -/
theorem rationalExtend_mem_characterValuationKernel_of_tower
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation M Γ)
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left] (x : rationalPoints G)
    (h : rationalExtend k L G x ∈
      (characterValuationKernel v (baseChanged L M (baseChanged k L G))).comap
        (rationalExtend L M (baseChanged k L G))) :
    rationalExtend k M G x ∈ characterValuationKernel v (baseChanged k M G) :=
  rationalExtend_mem_characterValuationKernel_of_map_tower k L M v G x
    (towerBaseChangeIso_map_mem_characterValuationKernel k L M v G _
      (rationalExtend_rationalExtend_mem_of_mem_comap k L M v G x h))

end TowerFields

section SplitKernel

variable {k : Type u} [Field k] (S : CommGroupScheme (Spec (CommRingCat.of k)))
  (hS : IsSplitTorus S.toGrp)

/-- On the character kernel of an equivalent valuation, the split-torus valuation is trivial. -/
theorem splitValuation_eq_one_of_mem {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation k (WithZero (Multiplicative ℤ))) (w : Valuation k Γ) (hvw : v.IsEquiv w)
    (t : rationalPoints S.toGrp) (ht : t ∈ characterValuationKernel w S.toGrp) :
    splitValuation S hS v t = 1 := by
  apply Multiplicative.toAdd.injective
  apply (cocharacterDualEquiv S hS).injective
  apply LinearMap.ext
  intro χ
  rw [cocharacterDualEquiv_apply, splitValuation_pairing, toAdd_one, map_zero,
    LinearMap.zero_apply]
  have h5 := (mem_characterValuationKernel.mp ht)
    ((rationalCharacters.equivCharacterLattice S).symm χ)
  rw [← hvw.eq_one_iff_eq_one, ← IntegerValuation.orderUnits_eq_one_iff] at h5
  exact (congrArg Multiplicative.toAdd h5).trans toAdd_one

end SplitKernel

section Local

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private instance intermediateScalarTowerF
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) :
    IsScalarTower F L (SeparableClosure F) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- An inertia-invariant integral functional vanishes on representatives of torsion classes
in the inertia coinvariants. -/
theorem functional_eq_zero_of_isOfFinAddOrder (k K E : Type u) [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [Normal k K]
    {V : Type u} [AddCommGroup V] [Module ℤ V] (ρ : Representation ℤ (E ≃ₐ[k] E) V)
    (f : V →ₗ[ℤ] ℤ) (hf : ∀ (σ : E ≃ₐ[k] E) (x : V), f (ρ σ x) = f x) (x : V)
    (h : IsOfFinAddOrder (inertiaProjection k K E ρ x)) : f x = 0 := by
  have hφ : ∀ g : relativeInertia k K E, f ∘ₗ (ρ.comp (relativeInertia k K E).subtype) g = f :=
    fun g => LinearMap.ext fun y => hf g y
  obtain ⟨m, hm, hm'⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp h
  have h0 := congrArg (Representation.Coinvariants.lift _ f hφ) hm'
  rw [map_nsmul, map_zero] at h0
  exact (smul_eq_zero.mp h0).resolve_left hm.ne'

/-- A base-field character pairs to zero with every cocharacter of a subextension whose
geometric extension is torsion in the inertia coinvariants. -/
theorem latticePairing_eq_zero_of_isOfFinAddOrder
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    (χ : characterLattice T)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (baseMap F L)).obj T))
    (h : IsOfFinAddOrder (inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
      (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T)
      (extendGeometricCocharacters F L (SeparableClosure F) T ν))) :
    latticePairing ((CommGroupScheme.baseChange (baseMap F L)).obj T)
      (characterLattice.baseChange (baseMap F L) T χ) ν = 0 := by
  rw [← latticePairing_extendGeometricCocharacters F L (SeparableClosure F)]
  refine functional_eq_zero_of_isOfFinAddOrder F (UnramifiedClosure F) (SeparableClosure F)
    (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T) _ (fun σ w => ?_) _ h
  rw [latticePairing_galoisRepresentation_right,
    characterLattice.galoisRepresentation_baseChange]

/-- The norm law evaluated on the extension of a base-field point. -/
theorem normLaw_pow_card
    (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
    (κ : torusKPoints F F T →* Multiplicative (TorusTarget F F T))
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap F L)).obj T).toGrp)
    (hκ : TorusNormLawAt F F T L hL κ) (x : rationalPoints T.toGrp) :
    κ (GaloisPoint.extend F (UnramifiedClosure F) T.toGrp (rationalCoeffEquiv F T.toGrp x)) ^
        Fintype.card (L ≃ₐ[UnramifiedClosure F] L) =
      Multiplicative.ofAdd (inertiaProjection F (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation F (SeparableClosure F) T)
        (extendGeometricCocharacters F L (SeparableClosure F) T
          (splitValuation ((CommGroupScheme.baseChange (baseMap F L)).obj T) hL
            (normalizedIntermediateValuation F L) (rationalExtend F L T.toGrp x)).toAdd)) := by
  rw [← map_pow, ← relativeNorm_relativeExtend F (UnramifiedClosure F) L T,
    GaloisPoint.relativeExtend_extend,
    ← baseChangeCoeffEquiv_rationalExtend (k := F) (L := L)]
  exact hκ (rationalExtend F L T.toGrp x)

/-- Descent: a base-field character-kernel point extends into the character kernel over the
maximal unramified extension. -/
theorem rationalExtend_unramified_mem_characterValuationKernel
    (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
    (x : rationalPoints T.toGrp)
    (hx : x ∈ characterValuationKernel (ValuativeRel.valuation F) T.toGrp) :
    rationalExtend F (UnramifiedClosure F) T.toGrp x ∈
      characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F)
        (baseChanged F (UnramifiedClosure F) T.toGrp) := by
  have hd := characterValuationKernelDescent_proof F T.toGrp
  rw [← characterValuationKernel_eq_rationalCommonNormKernel] at hd
  have hx' : x ∈ (characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F)
      (baseChanged F (UnramifiedClosure F) T.toGrp)).comap
        (rationalExtend F (UnramifiedClosure F) T.toGrp) := by
    rw [hd]
    exact hx
  exact Subgroup.mem_comap.mp hx'

set_option maxHeartbeats 200000 in
/-- A base-field character-kernel point extends into the character kernel over every finite
Galois subextension of the separable closure over the maximal unramified extension. -/
theorem rationalExtend_mem_characterValuationKernel
    (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (x : rationalPoints T.toGrp)
    (hx : x ∈ characterValuationKernel (ValuativeRel.valuation F) T.toGrp) :
    rationalExtend F L T.toGrp x ∈
      characterValuationKernel (intermediateValuation F L) (baseChanged F L T.toGrp) := by
  let : (LocalGalois.Separable.fixedFieldValuation F).HasExtension
      (intermediateValuation F L) := intermediateValuation_extends_fixedField F L
  have : IsAffine (baseChanged F (UnramifiedClosure F) T.toGrp).X.left := by
    change IsAffine (pullback T.X.hom (baseMap F (UnramifiedClosure F)))
    infer_instance
  have h2 := characterValuationKernel_le_comap (k := UnramifiedClosure F) (L := L)
    (LocalGalois.Separable.fixedFieldValuation F) (intermediateValuation F L)
    (intermediateValuation_conjugate F L) (baseChanged F (UnramifiedClosure F) T.toGrp)
    (rationalExtend_unramified_mem_characterValuationKernel F T x hx)
  exact rationalExtend_mem_characterValuationKernel_of_tower F (UnramifiedClosure F) L
    (intermediateValuation F L) T.toGrp x h2

/-- A base-field character whose base change pairs to zero with the split valuation of an
extended point has unit valuation at that point. -/
theorem valuation_rationalCharacterEval_eq_one_of_pairing
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap F L)).obj T).toGrp)
    (w : Valuation L (WithZero (Multiplicative ℤ))) (hw : w.IsEquiv (intermediateValuation F L))
    (x : rationalPoints T.toGrp) (χ : rationalCharacters T.toGrp)
    (hz : latticePairing ((CommGroupScheme.baseChange (baseMap F L)).obj T)
      (characterLattice.baseChange (baseMap F L) T (rationalCharacters.equivCharacterLattice T χ))
      (splitValuation ((CommGroupScheme.baseChange (baseMap F L)).obj T) hL w
        (rationalExtend F L T.toGrp x)).toAdd = 0) :
    ValuativeRel.valuation F (rationalCharacterEval χ x : F) = 1 := by
  let : (LocalGalois.Separable.fixedFieldValuation F).HasExtension
      (intermediateValuation F L) := intermediateValuation_extends_fixedField F L
  rw [splitValuation_pairing] at hz
  have h5 : IntegerValuation.orderUnits w
      (rationalCharacterEval (rationalCharacters.baseChange (baseMap F L) χ)
        (rationalExtend F L T.toGrp x)) = 1 :=
    Multiplicative.toAdd.injective (hz.trans toAdd_one.symm)
  rw [IntegerValuation.orderUnits_eq_one_iff, hw.eq_one_iff_eq_one,
    rationalCharacterEval_extend] at h5
  change intermediateValuation F L (algebraMap F L (rationalCharacterEval χ x : F)) = 1 at h5
  rw [IsScalarTower.algebraMap_apply F (UnramifiedClosure F) L,
    Valuation.HasExtension.val_map_eq_one_iff (LocalGalois.Separable.fixedFieldValuation F)
      (intermediateValuation F L),
    Valuation.HasExtension.val_map_eq_one_iff (ValuativeRel.valuation F)
      (LocalGalois.Separable.fixedFieldValuation F)] at h5
  exact h5

/-- A base-field point whose image under a homomorphism with the norm law is torsion lies in
the character kernel. -/
theorem mem_characterValuationKernel_of_isOfFinOrder_of_normLaw
    (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
    (κ : torusKPoints F F T →* Multiplicative (TorusTarget F F T))
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap F L)).obj T).toGrp)
    (hκ : TorusNormLawAt F F T L hL κ)
    (hw : (normalizedIntermediateValuation F L).IsEquiv (intermediateValuation F L))
    (x : rationalPoints T.toGrp)
    (hx : IsOfFinOrder
      (κ (GaloisPoint.extend F (UnramifiedClosure F) T.toGrp (rationalCoeffEquiv F T.toGrp x)))) :
    x ∈ characterValuationKernel (ValuativeRel.valuation F) T.toGrp := by
  rw [mem_characterValuationKernel]
  intro χ
  have hν := hx.pow (n := Fintype.card (L ≃ₐ[UnramifiedClosure F] L))
  rw [normLaw_pow_card F T κ L hL hκ x, isOfFinOrder_ofAdd_iff] at hν
  exact valuation_rationalCharacterEval_eq_one_of_pairing F T L hL _ hw x χ
    (latticePairing_eq_zero_of_isOfFinAddOrder F T L _ _ hν)

/-- The split valuation of the extension of a character-kernel point is trivial. -/
theorem splitValuation_rationalExtend_eq_one_of_isEquiv
    (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap F L)).obj T).toGrp)
    (hw : (normalizedIntermediateValuation F L).IsEquiv (intermediateValuation F L))
    (x : rationalPoints T.toGrp)
    (hx : x ∈ characterValuationKernel (ValuativeRel.valuation F) T.toGrp) :
    splitValuation ((CommGroupScheme.baseChange (baseMap F L)).obj T) hL
      (normalizedIntermediateValuation F L) (rationalExtend F L T.toGrp x) = 1 :=
  splitValuation_eq_one_of_mem _ hL _ _ hw _
    (rationalExtend_mem_characterValuationKernel F T L x hx)

/-- The image of a character-kernel point under a homomorphism with the norm law is
torsion. -/
theorem isOfFinOrder_of_mem_characterValuationKernel
    (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
    (κ : torusKPoints F F T →* Multiplicative (TorusTarget F F T))
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap F L)).obj T).toGrp)
    (hκ : TorusNormLawAt F F T L hL κ)
    (hw : (normalizedIntermediateValuation F L).IsEquiv (intermediateValuation F L))
    (x : rationalPoints T.toGrp)
    (hx : x ∈ characterValuationKernel (ValuativeRel.valuation F) T.toGrp) :
    IsOfFinOrder
      (κ (GaloisPoint.extend F (UnramifiedClosure F) T.toGrp
        (rationalCoeffEquiv F T.toGrp x))) := by
  refine isOfFinOrder_iff_pow_eq_one.mpr
    ⟨Fintype.card (L ≃ₐ[UnramifiedClosure F] L), Fintype.card_pos, ?_⟩
  rw [normLaw_pow_card F T κ L hL hκ x, splitValuation_rationalExtend_eq_one_of_isEquiv F T L hL hw x hx,
    toAdd_one, map_zero, map_zero, ofAdd_zero]

/-- The character-kernel identity for one torus, from the norm law of a homomorphism at one
finite Galois splitting field whose chosen integer valuation is equivalent to the spectral
one. -/
theorem characterValuationKernel_eq_comap_torsion_of_normLaw
    (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
    (κ : torusKPoints F F T →* Multiplicative (TorusTarget F F T))
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (hL : IsSplitTorus ((CommGroupScheme.baseChange (baseMap F L)).obj T).toGrp)
    (hκ : TorusNormLawAt F F T L hL κ)
    (hw : (normalizedIntermediateValuation F L).IsEquiv (intermediateValuation F L)) :
    characterValuationKernel (ValuativeRel.valuation F) T.toGrp =
      (CommGroup.torsion (Multiplicative (TorusTarget F F T))).comap
        (κ.comp ((GaloisPoint.extend F (UnramifiedClosure F) T.toGrp).comp
          (rationalCoeffEquiv F T.toGrp).toMonoidHom)) :=
  le_antisymm
    (fun x hx => (CommGroup.mem_torsion _).mpr
      (isOfFinOrder_of_mem_characterValuationKernel F T κ L hL hκ hw x hx))
    (fun x hx => mem_characterValuationKernel_of_isOfFinOrder_of_normLaw F T κ L hL hκ hw x
      ((CommGroup.mem_torsion _).mp hx))

end Local

end Langlands.Geometry.Building.Kottwitz
