import Langlands.Geometry.Building.Kottwitz.TorusKernelStatement
import Langlands.Geometry.Building.Kottwitz.TorusMapProof
import Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelNormLawReduction
import Langlands.Geometry.Building.KPZeroNormKernel

/-! # Proof of KP Proposition 11.1.5: the torus Iwahori subgroup is the Kottwitz kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.Kottwitz

open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPoint
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.TorusPointsTensorGalois

section Norm

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  [FiniteDimensional L M] [IsGalois L M]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- The relative norm is invariant under the relative Galois action. -/
theorem relativeNorm_relativeConjugate (σ : M ≃ₐ[L] M)
    (x : affinePoints T.toGrp (CommAlgCat.of k M)) :
    relativeNorm k L M T (relativeConjugate k L M T.toGrp σ x) = relativeNorm k L M T x := by
  apply relativeExtend_injective k L M T.toGrp
  rw [relativeExtend_norm, relativeExtend_norm]
  simp only [← relativeConjugate_mul]
  exact Fintype.prod_equiv (Equiv.mulRight σ) _ _ (fun _ => rfl)

end Norm

section Local

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
  (hL : IsSplitTorus (baseChanged k L T).toGrp)

/-- The split-torus valuation of `T_L`, with the normalized valuation of `L`, on the original
`L`-coefficient points. -/
def coeffSplitValuation :
    affinePoints T.toGrp (CommAlgCat.of k L) →*
      Multiplicative (cocharacterLattice (baseChanged k L T)) :=
  (splitValuation (baseChanged k L T) hL (normalizedIntermediateValuation F L)).comp
    (baseChangeCoeffEquiv k L T.toGrp).symm.toMonoidHom

omit [IsAffine T.X.left] [Normal k (UnramifiedClosure F)] [IsGalois (UnramifiedClosure F) L]
  [FiniteDimensional (UnramifiedClosure F) L] in
/-- Unfolding of `coeffSplitValuation`. -/
theorem coeffSplitValuation_apply (x : affinePoints T.toGrp (CommAlgCat.of k L)) :
    coeffSplitValuation F k T L hL x =
      splitValuation (baseChanged k L T) hL (normalizedIntermediateValuation F L)
        ((baseChangeCoeffEquiv k L T.toGrp).symm x) :=
  rfl

omit [IsAffine T.X.left] [Normal k (UnramifiedClosure F)] [IsGalois (UnramifiedClosure F) L]
  [FiniteDimensional (UnramifiedClosure F) L] in
/-- On a coefficient projection, `coeffSplitValuation` is the split valuation of the point of
`T_L`. -/
theorem coeffSplitValuation_baseChangeCoeffEquiv (y : rationalPoints (baseChanged k L T.toGrp)) :
    coeffSplitValuation F k T L hL (baseChangeCoeffEquiv k L T.toGrp y) =
      splitValuation (baseChanged k L T) hL (normalizedIntermediateValuation F L) y :=
  congrArg (splitValuation (baseChanged k L T) hL (normalizedIntermediateValuation F L))
    ((baseChangeCoeffEquiv k L T.toGrp).symm_apply_apply y)

omit [IsAffine T.X.left] [Normal k (UnramifiedClosure F)] [IsGalois (UnramifiedClosure F) L]
  [FiniteDimensional (UnramifiedClosure F) L] in
/-- The split valuation of a pure cocharacter evaluation. -/
theorem coeffSplitValuation_tmul (w : Additive Lˣ) (ν : cocharacterLattice (baseChanged k L T)) :
    coeffSplitValuation F k T L hL (coefficientEvaluation k L T (w ⊗ₜ[ULift.{u} ℤ] ν)).toMul =
      Multiplicative.ofAdd
        ((IntegerValuation.orderUnits (normalizedIntermediateValuation F L) w.toMul).toAdd • ν) := by
  rw [coefficientEvaluation_tmul_eq, coeffSplitValuation_apply, MulEquiv.symm_apply_apply]
  exact splitValuation_cocharacterPoints (baseChanged k L T) hL _ ν w.toMul

omit [IsAffine T.X.left] [Normal k (UnramifiedClosure F)] [IsGalois (UnramifiedClosure F) L]
  [FiniteDimensional (UnramifiedClosure F) L] in
/-- A cocharacter evaluated at a unit of order one has split valuation that cocharacter. -/
theorem coeffSplitValuation_tmul_of_order_eq_one (b : Lˣ)
    (hb : (IntegerValuation.orderUnits (normalizedIntermediateValuation F L) b).toAdd = 1)
    (ν : cocharacterLattice (baseChanged k L T)) :
    coeffSplitValuation F k T L hL
        (coefficientEvaluation k L T (Additive.ofMul b ⊗ₜ[ULift.{u} ℤ] ν)).toMul =
      Multiplicative.ofAdd ν := by
  rw [coeffSplitValuation_tmul, toMul_ofMul, hb, one_smul]

omit [IsAffine T.X.left] [IsGalois (UnramifiedClosure F) L]
  [FiniteDimensional (UnramifiedClosure F) L] in
/-- The norm-square value is the inertia class of the extended split valuation. -/
theorem normLawValue_eq_coeffSplitValuation (x : affinePoints T.toGrp (CommAlgCat.of k L)) :
    normLawValue F k T L hL (Additive.ofMul x) =
      inertiaProjection k (UnramifiedClosure F) (SeparableClosure F)
        (cocharacterLattice.galoisRepresentation k (SeparableClosure F) T)
        (extendGeometricCocharacters k L (SeparableClosure F) T
          (coeffSplitValuation F k T L hL x).toAdd) :=
  rfl

omit [Normal k (UnramifiedClosure F)] in
/-- A Galois difference of cocharacters is the split valuation of a point of norm one. -/
theorem exists_relativeNorm_eq_one_galois_sub (τ : L ≃ₐ[UnramifiedClosure F] L)
    (c₀ : cocharacterLattice (baseChanged k L T)) :
    ∃ z : affinePoints T.toGrp (CommAlgCat.of k L),
      relativeNorm k (UnramifiedClosure F) L T z = 1 ∧
        coeffSplitValuation F k T L hL z = Multiplicative.ofAdd
          (cocharacterLattice.galoisRepresentation k L T (τ.restrictScalars k) c₀ - c₀) := by
  obtain ⟨a, ha⟩ := exists_orderUnits_eq_one F L
  obtain ⟨y, hy⟩ : ∃ y : affinePoints T.toGrp (CommAlgCat.of k L),
      y = (coefficientEvaluation k L T (Additive.ofMul a ⊗ₜ[ULift.{u} ℤ] c₀)).toMul :=
    ⟨_, rfl⟩
  have hconj : relativeConjugate k (UnramifiedClosure F) L T.toGrp τ y =
      (coefficientEvaluation k L T
        (Additive.ofMul (Units.map (τ.restrictScalars k).toMonoidHom a) ⊗ₜ[ULift.{u} ℤ]
          cocharacterLattice.galoisRepresentation k L T (τ.restrictScalars k) c₀)).toMul := by
    have h := coefficientEvaluation_galois_tmul k L T (τ.restrictScalars k) (Additive.ofMul a) c₀
    rw [toMul_ofMul] at h
    rw [hy]
    exact (congrArg Additive.toMul h).symm
  have hn : (IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
      (Units.map (τ.restrictScalars k).toMonoidHom a)).toAdd = 1 :=
    (congrArg Multiplicative.toAdd (orderUnits_algEquiv F L τ a)).trans ha
  have h1 : coeffSplitValuation F k T L hL
      (relativeConjugate k (UnramifiedClosure F) L T.toGrp τ y) =
      Multiplicative.ofAdd
        (cocharacterLattice.galoisRepresentation k L T (τ.restrictScalars k) c₀) :=
    (congrArg (coeffSplitValuation F k T L hL) hconj).trans
      (coeffSplitValuation_tmul_of_order_eq_one F k T L hL _ hn _)
  have h2 : coeffSplitValuation F k T L hL y = Multiplicative.ofAdd c₀ :=
    (congrArg (coeffSplitValuation F k T L hL) hy).trans
      (coeffSplitValuation_tmul_of_order_eq_one F k T L hL a ha c₀)
  refine ⟨relativeConjugate k (UnramifiedClosure F) L T.toGrp τ y / y, ?_, ?_⟩
  · exact (map_div (relativeNorm k (UnramifiedClosure F) L T) _ _).trans
      ((congrArg (· / relativeNorm k (UnramifiedClosure F) L T y)
        (relativeNorm_relativeConjugate k (UnramifiedClosure F) L T τ y)).trans (div_self' _))
  · exact (map_div (coeffSplitValuation F k T L hL) _ _).trans
      ((congrArg₂ (· / ·) h1 h2).trans (ofAdd_sub _ _).symm)

omit [IsAffine T.X.left] [FiniteDimensional (UnramifiedClosure F) L] in
/-- An automorphism of `F^sep` that is trivial on `K` restricts to an automorphism of the
finite Galois extension `L/K`. -/
theorem exists_restrict_of_mem_relativeInertia
    (g : SeparableClosure F ≃ₐ[k] SeparableClosure F)
    (hg : g ∈ relativeInertia k (UnramifiedClosure F) (SeparableClosure F)) :
    ∃ τ : L ≃ₐ[UnramifiedClosure F] L, ∀ a : L,
      g (algebraMap L (SeparableClosure F) a) =
        algebraMap L (SeparableClosure F) ((τ.restrictScalars k) a) := by
  have hfix : ∀ r : UnramifiedClosure F,
      g (algebraMap (UnramifiedClosure F) (SeparableClosure F) r) =
        algebraMap (UnramifiedClosure F) (SeparableClosure F) r := by
    intro r
    have h1 : g.restrictNormal (UnramifiedClosure F) = 1 := hg
    rw [← AlgEquiv.restrictNormal_commutes g (UnramifiedClosure F) r, h1]
    rfl
  let g' : SeparableClosure F ≃ₐ[UnramifiedClosure F] SeparableClosure F :=
    { g.toRingEquiv with commutes' := hfix }
  refine ⟨g'.restrictNormal L, fun a => ?_⟩
  rw [AlgEquiv.restrictScalars_apply, AlgEquiv.restrictNormal_commutes]
  rfl

/-- Every element of the inertia augmentation is the extended split valuation of a point of
norm one. -/
theorem exists_relativeNorm_eq_one_of_mem_ker
    (w : geometricCocharacters k (SeparableClosure F) T)
    (hw : w ∈ Representation.Coinvariants.ker
      ((cocharacterLattice.galoisRepresentation k (SeparableClosure F) T).comp
        (relativeInertia k (UnramifiedClosure F) (SeparableClosure F)).subtype)) :
    ∃ z : affinePoints T.toGrp (CommAlgCat.of k L),
      relativeNorm k (UnramifiedClosure F) L T z = 1 ∧
        extendGeometricCocharacters k L (SeparableClosure F) T
          (coeffSplitValuation F k T L hL z).toAdd = w := by
  have hE : IsSplitTorus (baseChanged k (SeparableClosure F) T).toGrp :=
    IsSplitTorus.baseChange_fieldTower k L (SeparableClosure F) T.toGrp hL
  obtain ⟨u₀, hu₀⟩ := exists_not_isOfFinOrder F L
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨⟨g, hg⟩, v⟩, rfl⟩ := hw
    obtain ⟨c₀, rfl⟩ := (extendGeometricCocharacters_bijective k L (SeparableClosure F) T hL).2 v
    obtain ⟨τ, hτ⟩ := exists_restrict_of_mem_relativeInertia F k L g hg
    obtain ⟨z, hz1, hz2⟩ := exists_relativeNorm_eq_one_galois_sub F k T L hL τ c₀
    refine ⟨z, hz1, ?_⟩
    rw [hz2, toAdd_ofAdd, map_sub,
      extendGeometricCocharacters_galois k L (SeparableClosure F) T hE hu₀
        (τ.restrictScalars k) g hτ c₀]
    rfl
  | zero =>
    exact ⟨1, map_one _, by rw [map_one, toAdd_one, map_zero]⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨z₁, hz₁, hw₁⟩ := h₁
    obtain ⟨z₂, hz₂, hw₂⟩ := h₂
    refine ⟨z₁ * z₂, by rw [map_mul, hz₁, hz₂, mul_one], ?_⟩
    rw [map_mul, toAdd_mul, map_add, hw₁, hw₂]
  | smul n w _ h =>
    obtain ⟨z, hz, hw'⟩ := h
    refine ⟨z ^ n, by rw [map_zpow, hz, one_zpow], ?_⟩
    rw [map_zpow, toAdd_zpow, map_zsmul, hw']

/-- A point whose norm-square value vanishes has the split valuation of a point of norm one. -/
theorem exists_relativeNorm_eq_one_of_normLawValue_eq_zero
    (x : affinePoints T.toGrp (CommAlgCat.of k L))
    (hx : normLawValue F k T L hL (Additive.ofMul x) = 0) :
    ∃ z : affinePoints T.toGrp (CommAlgCat.of k L),
      relativeNorm k (UnramifiedClosure F) L T z = 1 ∧
        coeffSplitValuation F k T L hL z = coeffSplitValuation F k T L hL x := by
  rw [normLawValue_eq_coeffSplitValuation] at hx
  obtain ⟨z, hz, hzw⟩ := exists_relativeNorm_eq_one_of_mem_ker F k T L hL _
    ((Representation.Coinvariants.mk_eq_zero _).mp hx)
  exact ⟨z, hz, Multiplicative.toAdd.injective
    ((extendGeometricCocharacters_bijective k L (SeparableClosure F) T hL).1 hzw)⟩

/-- The kernel of a homomorphism with the norm square at `L` is the norm image of the points of
trivial split valuation. -/
theorem eq_one_iff_exists_coeffSplitValuation
    (κ : torusKPoints F k T →* Multiplicative (TorusTarget F k T))
    (hκ : TorusNormLawAt F k T L hL κ) (t : torusKPoints F k T) :
    κ t = 1 ↔ ∃ y : affinePoints T.toGrp (CommAlgCat.of k L),
      coeffSplitValuation F k T L hL y = 1 ∧ relativeNorm k (UnramifiedClosure F) L T y = t := by
  rw [torusNormLawAt_iff] at hκ
  constructor
  · intro ht
    obtain ⟨x, rfl⟩ := relativeNorm_unramifiedClosure_surjective F k T L hL t
    have hx : normLawValue F k T L hL (Additive.ofMul x) = 0 := by
      rw [hκ] at ht
      exact ofAdd_eq_one.mp ht
    obtain ⟨z, hz, hzx⟩ := exists_relativeNorm_eq_one_of_normLawValue_eq_zero F k T L hL x hx
    refine ⟨x * z⁻¹, ?_, ?_⟩
    · rw [map_mul, map_inv, hzx, mul_inv_cancel]
    · rw [map_mul, map_inv, hz, inv_one, mul_one]
  · rintro ⟨y, hy, rfl⟩
    rw [hκ, normLawValue_eq_coeffSplitValuation, hy, toAdd_one, map_zero, map_zero, ofAdd_zero]

omit [IsAffine T.X.left] [Normal k (UnramifiedClosure F)] [IsGalois (UnramifiedClosure F) L] in
/-- On the split torus `T_L`, the bounded subgroup for the spectral valuation is the kernel of
the split valuation for the normalized valuation. -/
theorem mem_characterValuationKernel_iff_splitValuation_eq_one
    (y : rationalPoints (baseChanged k L T).toGrp) :
    y ∈ characterValuationKernel (intermediateValuation F L) (baseChanged k L T).toGrp ↔
      splitValuation (baseChanged k L T) hL (normalizedIntermediateValuation F L) y = 1 := by
  have hw := (normalizedIntermediateValuation_spec' F L).1
  refine ⟨splitValuation_eq_one_of_mem _ hL _ _ hw y, fun hy => ?_⟩
  rw [mem_characterValuationKernel]
  intro χ
  have h := splitValuation_pairing (baseChanged k L T) hL (normalizedIntermediateValuation F L) y
    (rationalCharacters.equivCharacterLattice _ χ)
  rw [hy, toAdd_one, map_zero, (rationalCharacters.equivCharacterLattice _).symm_apply_apply] at h
  have h5 : IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
      (rationalCharacterEval χ y) = 1 :=
    Multiplicative.toAdd.injective (h.symm.trans toAdd_one.symm)
  rw [IntegerValuation.orderUnits_eq_one_iff, hw.eq_one_iff_eq_one] at h5
  exact h5

end Local

/-- Mapping a rational point along the inverse and then the forward map of an isomorphism
returns the point. -/
theorem rationalPoints_map_hom_map_inv {R : Type u} [CommRing R]
    {G G' : GroupScheme (Spec (CommRingCat.of R))} (e : G ≅ G') (x : rationalPoints G') :
    rationalPoints.map e.hom (rationalPoints.map e.inv x) = x := by
  change (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x
  simp only [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

section TowerKernel

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))

/-- The inverse tower comparison maps bounded points of `G_L` to bounded points of `(G_K)_L`. -/
theorem towerBaseChangeIso_inv_mem_baseChanged (G : GroupScheme (Spec (CommRingCat.of k)))
    (z : rationalPoints (GaloisPointComparison.baseChanged k L G))
    (hz : z ∈ characterValuationKernel (intermediateValuation F L)
      (GaloisPointComparison.baseChanged k L G)) :
    rationalPoints.map (towerBaseChangeIso k (UnramifiedClosure F) L G).inv z ∈
      characterValuationKernel (intermediateValuation F L)
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) L
          (GaloisPointComparison.baseChanged k (UnramifiedClosure F) G)) :=
  map_characterValuationKernel_le _ _ (Subgroup.mem_map_of_mem _ hz)

omit [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)] in
/-- Bounded points of the iterated base change of the underlying group scheme are bounded points
of the iterated commutative base change. -/
theorem mem_characterValuationKernel_of_mem_baseChanged
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (y : rationalPoints ((CommGroupScheme.baseChange (baseMap (UnramifiedClosure F) L)).obj
          ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T)).toGrp)
    (h : y ∈ characterValuationKernel (intermediateValuation F L)
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) L
          (GaloisPointComparison.baseChanged k (UnramifiedClosure F) T.toGrp))) :
    y ∈ characterValuationKernel (intermediateValuation F L)
        ((CommGroupScheme.baseChange (baseMap (UnramifiedClosure F) L)).obj
          ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T)).toGrp :=
  h

end TowerKernel

section Tower

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
  [IsAffine ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T).X.left]
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
  (hL : IsSplitTorus (baseChanged k L T).toGrp)

omit [Normal k (UnramifiedClosure F)] in
/-- The relative norm of the transported point is the norm of `T_K` from `L` to `K`. -/
theorem relativeNorm_towerBaseChangeIso
    (x : rationalPoints ((CommGroupScheme.baseChange (baseMap (UnramifiedClosure F) L)).obj
      ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T)).toGrp) :
    relativeNorm k (UnramifiedClosure F) L T (baseChangeCoeffEquiv k L T.toGrp
        (rationalPoints.map (towerBaseChangeIso k (UnramifiedClosure F) L T.toGrp).hom x)) =
      baseChangeCoeffEquiv k (UnramifiedClosure F) T.toGrp
        (rationalNorm (UnramifiedClosure F) L
          ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T) x) :=
  (baseChangeCoeffEquiv_relativeRationalNorm k (UnramifiedClosure F) L T _).symm.trans
    (congrArg (baseChangeCoeffEquiv k (UnramifiedClosure F) T.toGrp)
      (relativeRationalNorm_towerBaseChangeIso k (UnramifiedClosure F) L T x))

omit [Normal k (UnramifiedClosure F)] in
/-- The norm of the transport of a point of `T_L` is its relative norm. -/
theorem relativeNorm_towerBaseChangeIso_inv (y : affinePoints T.toGrp (CommAlgCat.of k L)) :
    baseChangeCoeffEquiv k (UnramifiedClosure F) T.toGrp
        (rationalNorm (UnramifiedClosure F) L
          ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T)
          (rationalPoints.map (towerBaseChangeIso k (UnramifiedClosure F) L T.toGrp).inv
            ((baseChangeCoeffEquiv k L T.toGrp).symm y))) =
      relativeNorm k (UnramifiedClosure F) L T y :=
  (relativeNorm_towerBaseChangeIso F k T L _).symm.trans
    ((congrArg (fun z => relativeNorm k (UnramifiedClosure F) L T (baseChangeCoeffEquiv k L T.toGrp z))
      (rationalPoints_map_hom_map_inv _ _)).trans
      (congrArg (relativeNorm k (UnramifiedClosure F) L T)
        ((baseChangeCoeffEquiv k L T.toGrp).apply_symm_apply y)))

omit [IsAffine T.X.left] [Normal k (UnramifiedClosure F)]
  [IsAffine ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T).X.left]
  [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L] in
/-- The tower comparison maps bounded points of `T_K` over `L` to bounded points of `T_L`. -/
theorem towerHom_mem_characterValuationKernel
    (x : rationalPoints ((CommGroupScheme.baseChange (baseMap (UnramifiedClosure F) L)).obj
      ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T)).toGrp)
    (hx : x ∈ characterValuationKernel (intermediateValuation F L)
      ((CommGroupScheme.baseChange (baseMap (UnramifiedClosure F) L)).obj
        ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T)).toGrp) :
    rationalPoints.map (towerBaseChangeIso k (UnramifiedClosure F) L T.toGrp).hom x ∈
      characterValuationKernel (intermediateValuation F L) (baseChanged k L T.toGrp) :=
  map_characterValuationKernel_le _ _ (Subgroup.mem_map_of_mem _ hx)

omit [IsAffine T.X.left] [Normal k (UnramifiedClosure F)]
  [IsAffine ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T).X.left]
  [IsGalois (UnramifiedClosure F) L] in
/-- A bounded point of `T_L` has trivial split valuation. -/
theorem coeffSplitValuation_eq_one_of_mem
    (y : rationalPoints (GaloisPointComparison.baseChanged k L T.toGrp))
    (hy : y ∈ characterValuationKernel (intermediateValuation F L)
      (GaloisPointComparison.baseChanged k L T.toGrp)) :
    coeffSplitValuation F k T L hL (baseChangeCoeffEquiv k L T.toGrp y) = 1 :=
  (coeffSplitValuation_baseChangeCoeffEquiv F k T L hL y).trans
    ((mem_characterValuationKernel_iff_splitValuation_eq_one F k T L hL y).mp hy)

omit [IsAffine T.X.left] [Normal k (UnramifiedClosure F)]
  [IsAffine ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T).X.left]
  [IsGalois (UnramifiedClosure F) L] in
/-- A bounded point of `T_K` over `L` has trivial split valuation after transport to `T_L`. -/
theorem coeffSplitValuation_towerBaseChangeIso_eq_one
    (x : rationalPoints ((CommGroupScheme.baseChange (baseMap (UnramifiedClosure F) L)).obj
      ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T)).toGrp)
    (hx : x ∈ characterValuationKernel (intermediateValuation F L)
      ((CommGroupScheme.baseChange (baseMap (UnramifiedClosure F) L)).obj
        ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T)).toGrp) :
    coeffSplitValuation F k T L hL (baseChangeCoeffEquiv k L T.toGrp
      (rationalPoints.map (towerBaseChangeIso k (UnramifiedClosure F) L T.toGrp).hom x)) = 1 :=
  coeffSplitValuation_eq_one_of_mem F k T L hL _ (towerHom_mem_characterValuationKernel F k T L x hx)

omit [IsAffine T.X.left] [Normal k (UnramifiedClosure F)]
  [IsAffine ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T).X.left]
  [IsGalois (UnramifiedClosure F) L] in
/-- A point of `T_L` with trivial split valuation is bounded. -/
theorem mem_characterValuationKernel_of_coeffSplitValuation_eq_one
    (y : affinePoints T.toGrp (CommAlgCat.of k L)) (hy : coeffSplitValuation F k T L hL y = 1) :
    (baseChangeCoeffEquiv k L T.toGrp).symm y ∈
      characterValuationKernel (intermediateValuation F L)
        (GaloisPointComparison.baseChanged k L T.toGrp) :=
  (mem_characterValuationKernel_iff_splitValuation_eq_one F k T L hL _).mpr
    ((coeffSplitValuation_apply F k T L hL y).symm.trans hy)

omit [IsAffine T.X.left] [Normal k (UnramifiedClosure F)]
  [IsAffine ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T).X.left]
  [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L] in
/-- The inverse tower comparison maps bounded points of `T_L` to bounded points of `T_K` over
`L`. -/
theorem towerInv_mem_characterValuationKernel
    (z : rationalPoints (GaloisPointComparison.baseChanged k L T.toGrp))
    (hz : z ∈ characterValuationKernel (intermediateValuation F L)
      (GaloisPointComparison.baseChanged k L T.toGrp)) :
    rationalPoints.map (towerBaseChangeIso k (UnramifiedClosure F) L T.toGrp).inv z ∈
      characterValuationKernel (intermediateValuation F L)
        ((CommGroupScheme.baseChange (baseMap (UnramifiedClosure F) L)).obj
          ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T)).toGrp :=
  mem_characterValuationKernel_of_mem_baseChanged F k L T _
    (towerBaseChangeIso_inv_mem_baseChanged F k L T.toGrp z hz)

omit [IsAffine T.X.left] [Normal k (UnramifiedClosure F)] [IsGalois (UnramifiedClosure F) L]
  [IsAffine ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T).X.left] in
/-- A point of `T_L` with trivial split valuation transports to a bounded point of `T_K` over
`L`. -/
theorem towerBaseChangeIso_inv_mem_characterValuationKernel
    (y : affinePoints T.toGrp (CommAlgCat.of k L)) (hy : coeffSplitValuation F k T L hL y = 1) :
    rationalPoints.map (towerBaseChangeIso k (UnramifiedClosure F) L T.toGrp).inv
        ((baseChangeCoeffEquiv k L T.toGrp).symm y) ∈
      characterValuationKernel (intermediateValuation F L)
        ((CommGroupScheme.baseChange (baseMap (UnramifiedClosure F) L)).obj
          ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T)).toGrp :=
  towerInv_mem_characterValuationKernel F k T L _
    (mem_characterValuationKernel_of_coeffSplitValuation_eq_one F k T L hL y hy)

/-- The norm subgroup of `T_K` for `L` is the kernel of any homomorphism satisfying the norm
square at `L`. -/
theorem torusNormIwahori_eq_comap_ker
    (κ : torusKPoints F k T →* Multiplicative (TorusTarget F k T))
    (hκ : TorusNormLawAt F k T L hL κ) :
    torusNormIwahori (UnramifiedClosure F) L (intermediateValuation F L)
        ((CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T) =
      κ.ker.comap (baseChangeCoeffEquiv k (UnramifiedClosure F) T.toGrp).toMonoidHom := by
  ext t
  rw [mem_torusNormIwahori, Subgroup.mem_comap, MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom,
    eq_one_iff_exists_coeffSplitValuation F k T L hL κ hκ]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, coeffSplitValuation_towerBaseChangeIso_eq_one F k T L hL x hx,
      relativeNorm_towerBaseChangeIso F k T L x⟩
  · rintro ⟨y, hy, hN⟩
    exact ⟨_, towerBaseChangeIso_inv_mem_characterValuationKernel F k T L hL y hy,
      (baseChangeCoeffEquiv k (UnramifiedClosure F) T.toGrp).injective
        ((relativeNorm_towerBaseChangeIso_inv F k T L y).trans hN)⟩

end Tower

/-- KP Proposition 11.1.5: `T(K)^0 = ker(κ_T)`. -/
theorem torusKottwitzKernel : TorusKottwitzKernelStatement.{u} := by
  intro F _ _ _ _ k _ _ _ _ _ T hT TK L _ _ hsplit
  let : IsAffine T.X.left := torusIsAffine k T hT
  have hL : IsSplitTorus (baseChanged k L T).toGrp :=
    IsSplitTorus.of_iso (towerBaseChangeIso k (UnramifiedClosure F) L T.toGrp).symm hsplit
  exact torusNormIwahori_eq_comap_ker F k T L hL _
    ((torusKottwitzExistence F k T hT).2.1 L hL)

end Langlands.Geometry.Building.Kottwitz
