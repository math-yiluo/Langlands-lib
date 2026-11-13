import Langlands.GroupScheme.IntegralModel.SplitIntegralPoints
import Langlands.GroupScheme.HenselianIwasawaFactorization
import Langlands.GroupScheme.Reductive.LocalRootGroupFibre
import Langlands.Geometry.Building.SplitIntegralPinningOfRoots
import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.Geometry.Building.IntegerCentralizerStabilizer
import Langlands.BruhatTits.Cartan.CentralizerRealComparison

/-! # Generic split tori of the maximal unramified base change of a good model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

/-! ### Coordinates and real valuation vectors on the coordinate torus -/

namespace Langlands.Geometry.Building.SplitIntegralPinning

variable {k : Type u} [Field k] {I : Type u} [Fintype I]

/-- A rational point of the coordinate torus is the point whose coordinates are the values of
the coordinate characters. -/
theorem eq_pointsEquiv_symm_torusCharEval (t : rationalPoints (coordTorus k I).toGrp) :
    t = (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm
      (fun j => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom
        (torusCharEval (coordTorus k I) (splitTorus.proj _ I j) t)) := by
  apply (splitTorus.pointsEquiv I (Over.mk (𝟙 (Spec (CommRingCat.of k))))).injective
  rw [MulEquiv.apply_symm_apply]
  funext j
  apply Units.ext
  rw [← splitTorus.comp_proj]
  exact ChevalleyRootFamily.charValue_eq_rationalCharacterEval (splitTorus.proj _ I j) t

/-- The real valuation vector of a point of the coordinate torus (the centralizer valuation of
the identity) evaluates every character to the order of its value. -/
theorem eval_centralizerValuation_id (v : Valuation k (WithZero (Multiplicative ℤ)))
    (t : rationalPoints (coordTorus k I).toGrp) (a : characterLattice (coordTorus k I)) :
    eval (coordTorus k I) a
        (IntegerValuation.centralizerValuation v (𝟙 _)
          (Langlands.BruhatTits.Cartan.restrictionEvaluation_id_bijective
            (isSplitTorus_splitTorus I)) t).toAdd =
      IntegerValuation.order v (torusCharEval (coordTorus k I) a t) := by
  have h := IntegerValuation.centralizerValuation_spec v (𝟙 _)
    (Langlands.BruhatTits.Cartan.restrictionEvaluation_id_bijective (isSplitTorus_splitTorus I))
    t ((rationalCharacters.equivCharacterLattice (coordTorus k I)).symm a)
  simpa only [Langlands.BruhatTits.Cartan.characterRestriction, AddMonoidHom.comp_apply,
    characterRestrict_id, AddMonoidHom.id_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.apply_symm_apply] using h

/-- **Bounded points of the coordinate torus.** A point of the coordinate torus on which every
character has order zero has coordinates of valuation one. -/
theorem valuation_coordinate_eq_one_of_eval_eq_zero
    (v : Valuation k (WithZero (Multiplicative ℤ))) (t : rationalPoints (coordTorus k I).toGrp)
    (ht : (IntegerValuation.centralizerValuation v (𝟙 _)
      (Langlands.BruhatTits.Cartan.restrictionEvaluation_id_bijective
        (isSplitTorus_splitTorus I)) t).toAdd = 0) (j : I) :
    v (torusCharEval (coordTorus k I) (splitTorus.proj _ I j) t : k) = 1 := by
  have htk : t ∈ characterValuationKernel v (coordTorus k I).toGrp := by
    rw [← IntegerValuation.centralizerValuation_ker v (𝟙 _)
      (Langlands.BruhatTits.Cartan.restrictionEvaluation_id_bijective
        (isSplitTorus_splitTorus I)), MonoidHom.mem_ker, ← ofAdd_toAdd (IntegerValuation.centralizerValuation v (𝟙 _)
      (Langlands.BruhatTits.Cartan.restrictionEvaluation_id_bijective
        (isSplitTorus_splitTorus I)) t), ht, ofAdd_zero]
  exact (mem_characterValuationKernel.mp htk) _

end Langlands.Geometry.Building.SplitIntegralPinning

namespace Langlands.GroupScheme.IntegralModel

open Langlands.Geometry.Building Langlands.LocalGalois.Separable GaloisPointComparison

section General

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)
  {I : Type u} [Fintype I]

/-- The generic fibre of an integral exponent cocharacter of a split torus, followed by the
generic identification, is the exponent cocharacter followed by the generic split torus. -/
theorem baseChangeCocharacter_exponentCocharacter_comp
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ M.group) (n : I → ℤ) :
    Dynamic.baseChangeCocharacter (Spec.algebraMap R K)
        (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I n) ≫ i) ≫
          M.genericIso.hom =
      CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I n) ≫
        M.genericSplitTorusHom i := by
  rw [LocalRootGroup.baseChangeCocharacter_groupHom_comp, genericSplitTorusHom, genericHom]
  simp only [Category.assoc]

omit [IsDomain R] in
/-- When `R` is the valuation ring of `v` in `K`, a unit of `K` of valuation one comes from a
unit of `R`. -/
theorem exists_units_map_eq_of_valuation_eq_one {v : Valuation K (WithZero (Multiplicative ℤ))}
    (hv : ∀ c : K, v c ≤ 1 ↔ c ∈ (algebraMap R K).range) (c : Kˣ) (hc : v (c : K) = 1) :
    ∃ s : Rˣ, Units.map (algebraMap R K : R →* K) s = c := by
  obtain ⟨r, hr⟩ := (hv c).1 hc.le
  obtain ⟨r', hr'⟩ := (hv (c⁻¹ : Kˣ)).1 (by rw [Units.val_inv_eq_inv_val, map_inv₀, hc, inv_one])
  have hrr' : r * r' = 1 := IsFractionRing.injective R K (by
    rw [map_mul, hr, hr', Units.mul_inv, map_one])
  refine ⟨⟨r, r', hrr', by rw [mul_comm]; exact hrr'⟩, Units.ext ?_⟩
  simp [hr]

/-- **Integrality on a generic split torus.** Let `R` be the valuation ring of `v`, and let
`i` be a closed split torus of the model whose generic fibre is a maximal split torus of the
connected reductive group `G`. A point `t` of the torus on which every relative root has order
zero, and whose image lies in `G(K)^1`, has integral image. -/
theorem map_genericSplitTorusHom_mem_integralPoints
    {v : Valuation K (WithZero (Multiplicative ℤ))}
    (hv : ∀ c : K, v c ≤ 1 ↔ c ∈ (algebraMap R K).range)
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ M.group) (hi : IsClosedSubgroup i)
    (hsplit : IsMaximalSplitTorus (T := SplitIntegralPinning.coordTorus K I)
      (M.genericSplitTorusHom i))
    (t : rationalPoints (SplitIntegralPinning.coordTorus K I).toGrp)
    (ht : ∀ a ∈ relativeRoots (T := SplitIntegralPinning.coordTorus K I)
        (M.genericSplitTorusHom i),
      IntegerValuation.order v (torusCharEval (SplitIntegralPinning.coordTorus K I) a t) = 0)
    (hk : rationalPoints.map (M.genericSplitTorusHom i) t ∈ characterValuationKernel v G) :
    rationalPoints.map (M.genericSplitTorusHom i) t ∈ M.integralPoints := by
  have hw : (IntegerValuation.centralizerValuation v (𝟙 _)
      (Langlands.BruhatTits.Cartan.restrictionEvaluation_id_bijective
        (isSplitTorus_splitTorus I)) t).toAdd = 0 := by
    apply eq_zero_of_eval_relativeRoots_of_eval_torusCharacterRestrict hG _ hsplit
    · intro a ha
      rw [SplitIntegralPinning.eval_centralizerValuation_id]
      exact ht a ha
    · intro χ
      rw [SplitIntegralPinning.eval_centralizerValuation_id]
      have h1 : torusCharEval (SplitIntegralPinning.coordTorus K I)
          (torusCharacterRestrict (M.genericSplitTorusHom i) χ) t =
          rationalCharacterEval χ (rationalPoints.map (M.genericSplitTorusHom i) t) :=
        rationalCharacterEval_characterRestrict _ χ t
      have h2 : IntegerValuation.orderUnits v
          (rationalCharacterEval χ (rationalPoints.map (M.genericSplitTorusHom i) t)) = 1 :=
        (IntegerValuation.orderUnits_eq_one_iff v _).2 ((mem_characterValuationKernel.mp hk) χ)
      rw [h1, IntegerValuation.order, h2, toAdd_one, Int.cast_zero]
  have hval := (M.genericSplitTorusValue_mem_integralPoints_iff i hi
    (fun j => torusCharEval (SplitIntegralPinning.coordTorus K I) (splitTorus.proj _ I j) t)).2
    fun j => exists_units_map_eq_of_valuation_eq_one hv _
      (SplitIntegralPinning.valuation_coordinate_eq_one_of_eval_eq_zero v t hw j)
  rwa [genericSplitTorusValue, ← SplitIntegralPinning.eq_pointsEquiv_symm_torusCharEval] at hval

end General

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The normalized valuation of the maximal unramified extension has the integers
`fixedFieldIntegers F` as its valuation ring. -/
theorem _root_.Langlands.Geometry.Building.MaximalUnramified.valuation_le_one_iff_mem_range
    (c : inertiaFixedField F) :
    MaximalUnramified.valuation F c ≤ 1 ↔
      c ∈ (algebraMap (fixedFieldIntegers F) (inertiaFixedField F)).range := by
  rw [← Valuation.mem_valuationSubring_iff, MaximalUnramified.valuationSubring_eq]
  exact ⟨fun h => ⟨⟨c, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (M : IntegralModel ↥𝒪[F] F G)

private instance unramifiedGenericSplitTorusAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Integrality on a generic split torus after maximal unramified base change.** For a closed
split torus of `M.baseChangeUnramified` whose generic fibre is a maximal split torus, a point of
the torus on which every relative root has order zero and whose image lies in `G(L)^1` has
image in the integral points. This is the torus condition of
`SplitIntegralPinning.ofRootParametrizations` for `K = M.baseChangeUnramified.integralPoints`. -/
theorem baseChangeUnramified_map_genericSplitTorusHom_mem_integralPoints
    (hGL : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
    {I : Type u} [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of (fixedFieldIntegers F))) I ⟶
      M.baseChangeUnramified.group)
    (hi : IsClosedSubgroup i)
    (hsplit : IsMaximalSplitTorus (T := SplitIntegralPinning.coordTorus (inertiaFixedField F) I)
      (M.baseChangeUnramified.genericSplitTorusHom i))
    (t : rationalPoints (SplitIntegralPinning.coordTorus (inertiaFixedField F) I).toGrp)
    (ht : ∀ a ∈ relativeRoots (T := SplitIntegralPinning.coordTorus (inertiaFixedField F) I)
        (M.baseChangeUnramified.genericSplitTorusHom i),
      IntegerValuation.order (MaximalUnramified.valuation F)
        (torusCharEval (SplitIntegralPinning.coordTorus (inertiaFixedField F) I) a t) = 0)
    (hk : rationalPoints.map (M.baseChangeUnramified.genericSplitTorusHom i) t ∈
      characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G)) :
    rationalPoints.map (M.baseChangeUnramified.genericSplitTorusHom i) t ∈
      M.baseChangeUnramified.integralPoints :=
  M.baseChangeUnramified.map_genericSplitTorusHom_mem_integralPoints
    (MaximalUnramified.valuation_le_one_iff_mem_range (F := F)) hGL i hi hsplit t ht hk

/-- **Integral Iwasawa factorization for generic split tori.** For a split torus of the
maximal unramified base change of a good model, every rational point of the base-changed
group is an integral point times a point of the dynamic parabolic of an arbitrary
cocharacter of the generic split torus. -/
theorem baseChangeUnramified_exists_integral_mul_parabolic_genericSplitTorus
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group))
    {I : Type u} [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of (fixedFieldIntegers F))) I ⟶
      M.baseChangeUnramified.group)
    (ν : cocharacterLattice (SplitIntegralPinning.coordTorus (inertiaFixedField F) I))
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) :
    ∃ κ ∈ M.baseChangeUnramified.integralPoints,
      ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫
          M.baseChangeUnramified.genericSplitTorusHom i)).carrier (Over.mk (𝟙 _)),
        g = κ * p := by
  set n := splitTorus.cocharacterLatticeEquiv (inertiaFixedField F) I ν
  have hν : ν = splitTorus.exponentCocharacter _ I n := by
    rw [splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm]
    exact ((splitTorus.cocharacterLatticeEquiv _ I).symm_apply_apply ν).symm
  rw [hν]
  exact HenselianParabolicCovering.baseChangeUnramified_exists_integral_mul_parabolic M hG
    hSpecial _ (M.baseChangeUnramified.baseChangeCocharacter_exponentCocharacter_comp i n) g

end Unramified

end Langlands.GroupScheme.IntegralModel
