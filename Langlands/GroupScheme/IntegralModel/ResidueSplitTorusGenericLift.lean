import Langlands.GroupScheme.IntegralModel.UnramifiedGenericSplitTorus
import Langlands.GroupScheme.IntegralModel.UnramifiedSplitMaximalTorus
import Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom
import Langlands.GroupScheme.Torus.HenselianSplitSubgroupLifting
import Langlands.GroupScheme.Torus.MaximalTorusImageSplitLift
import Langlands.GroupScheme.Rational.SplitRankMaximality
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.Geometry.Building.TorusUnitFixedPoint
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction

/-! # Exact residue split-source lifts with maximal generic fibre and integral units -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IntegralModel

open Langlands.Geometry.Building

section IntegralUnits

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  (hv : ∀ c : K, v c ≤ 1 ↔ c ∈ (algebraMap R K).range)

include hv

/-- Units of the standard generic split torus have integral images under a
closed integral split-torus map. No generic maximality is required. -/
theorem map_genericSplitTorusHom_mem_integralPoints_of_characterKernel
    {I : Type u} [Fintype I]
    (j : splitTorus (Spec (CommRingCat.of R)) I ⟶ M.group)
    (hj : IsClosedSubgroup j)
    (t : rationalPoints (SplitIntegralPinning.coordTorus K I).toGrp)
    (ht : t ∈ characterValuationKernel v (SplitIntegralPinning.coordTorus K I).toGrp) :
    rationalPoints.map (M.genericSplitTorusHom j) t ∈ M.integralPoints := by
  have hval := (M.genericSplitTorusValue_mem_integralPoints_iff j hj
    (fun a => torusCharEval (SplitIntegralPinning.coordTorus K I)
      (splitTorus.proj _ I a) t)).2
    (fun a => exists_units_map_eq_of_valuation_eq_one hv _
      ((mem_characterValuationKernel.mp ht) (splitTorus.proj _ I a)))
  rwa [genericSplitTorusValue, ← SplitIntegralPinning.eq_pointsEquiv_symm_torusCharEval] at hval

/-- The character-valuation kernel of any closed integral split source maps
into the actual integral-point group. -/
theorem map_genericHom_mem_integralPoints_of_split_characterKernel
    {H : GroupScheme (Spec (CommRingCat.of R))}
    (hH : IsSplitTorus H) (j : H ⟶ M.group) (hj : IsClosedSubgroup j)
    (t : rationalPoints ((GroupScheme.baseChange (Spec.algebraMap R K)).obj H))
    (ht : t ∈ characterValuationKernel v
      ((GroupScheme.baseChange (Spec.algebraMap R K)).obj H)) :
    rationalPoints.map (M.genericHom j) t ∈ M.integralPoints := by
  obtain ⟨I, _, ⟨e⟩⟩ := hH
  let : Fintype I := Fintype.ofFinite I
  let eK := (GroupScheme.baseChange (Spec.algebraMap R K)).mapIso e ≪≫
    splitTorus.baseChangeIso (Spec.algebraMap R K) I
  have htk : rationalPoints.map eK.hom t ∈
      characterValuationKernel v (SplitIntegralPinning.coordTorus K I).toGrp :=
    map_characterValuationKernel_le v eK.hom ⟨t, ht, rfl⟩
  have h := M.map_genericSplitTorusHom_mem_integralPoints_of_characterKernel hv
    (e.inv ≫ j) (hj.iso_comp e.symm) _ htk
  have hcomp : eK.hom ≫ M.genericSplitTorusHom (e.inv ≫ j) = M.genericHom j := by
    simp [eK, genericSplitTorusHom, genericHom, Functor.map_comp]
  change (t ≫ eK.hom.hom.hom) ≫
    (M.genericSplitTorusHom (e.inv ≫ j)).hom.hom ∈ M.integralPoints at h
  rw [Category.assoc, ← Grp.comp_hom_hom, hcomp] at h
  exact h

/-- If the integral group of a model is split, every unit of its specified
generic group is integral, independently of its chosen generic identification. -/
theorem characterValuationKernel_le_integralPoints_of_isSplitTorus
    (hM : IsSplitTorus M.group) :
    characterValuationKernel v G ≤ M.integralPoints := by
  intro t ht
  have ht' : rationalPoints.map M.genericIso.inv t ∈
      characterValuationKernel v M.genericFibre :=
    map_characterValuationKernel_le v M.genericIso.inv ⟨t, ht, rfl⟩
  have h := M.map_genericHom_mem_integralPoints_of_split_characterKernel hv hM
    (𝟙 M.group) (by
      change IsClosedImmersion (𝟙 M.group.X.left)
      infer_instance)
    (rationalPoints.map M.genericIso.inv t) ht'
  simpa [genericHom, Functor.map_id, rationalPoints.map, Category.assoc,
    ← Grp.comp_hom_hom] using h

end IntegralUnits

section CoefficientUnits

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  {v : Valuation L (WithZero (Multiplicative ℤ))}
  (hv : ∀ c : L, v c ≤ 1 ↔ c ∈ (algebraMap A L).range)

include hv

/-- After any commuting coefficient extension to a valuation ring, units of
an integral split source have integral images in the extended model. -/
theorem map_baseChange_genericHom_mem_integralPoints_of_split_characterKernel
    {H : GroupScheme (Spec (CommRingCat.of R))}
    (hH : IsSplitTorus H) (j : H ⟶ M.group)
    (t : rationalPoints ((GroupScheme.baseChange (Spec.algebraMap K L)).obj
      ((GroupScheme.baseChange (Spec.algebraMap R K)).obj H)))
    (ht : t ∈ characterValuationKernel v
      ((GroupScheme.baseChange (Spec.algebraMap K L)).obj
        ((GroupScheme.baseChange (Spec.algebraMap R K)).obj H))) :
    rationalPoints.map ((GroupScheme.baseChange (Spec.algebraMap K L)).map
      (M.genericHom j)) t ∈ (M.baseChange A L).integralPoints := by
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let S : IntegralModel R K ((GroupScheme.baseChange (Spec.algebraMap R K)).obj H) :=
    { group := H
      genericIso := Iso.refl _ }
  let φ : S.Hom M (M.genericHom j) :=
    { hom := j
      generic_comm := by simp [S, genericHom] }
  exact (φ.baseChangeCoefficients A L).map_mem_integralPoints
    ((S.baseChange A L).characterValuationKernel_le_integralPoints_of_isSplitTorus
      hv (hH.baseChange (Spec.algebraMap R A)) ht)

end CoefficientUnits

section SameSource

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

/-- A closed integral split source is maximal in the generic group if another
map from that very generic source is maximal split. -/
theorem isMaximalSplitTorus_genericTorusMap_of_same_source
    (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of R))) (hS : IsSplitTorus S.toGrp)
    (j : S.toGrp ⟶ M.group) (hj : IsClosedSubgroup j)
    (a : ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj S).toGrp ⟶ G)
    (ha : IsMaximalSplitTorus a) :
    IsMaximalSplitTorus (M.genericTorusMap S j) := by
  have hSK := hS.baseChange (Spec.algebraMap R K)
  have hsplit : IsSplitSubtorus (M.genericTorusMap S j) :=
    ⟨hSK, (hj.baseChange (Spec.algebraMap R K)).comp_iso M.genericIso⟩
  obtain ⟨I, _, ⟨e⟩⟩ := hSK
  exact hsplit.isMaximalSplitTorus_of_card_le
    (maximalSplitTorusConjugacy K G hG).2 ha I I e e le_rfl

end SameSource

section ResidueLift

variable {R K k : Type u} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field k] [Algebra R k]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G) [Smooth M.group.X.hom]

/-- Lift a prescribed split source through a residue homomorphism and then
integrally, with maximality in the generic group supplied by the same source. -/
theorem exists_closed_splitSource_lift_of_maximalTorus_images
    (hk : Function.Surjective (algebraMap R k))
    (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of R))) (hS : IsSplitTorus S.toGrp)
    (a : ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj S).toGrp ⟶ G)
    (ha : IsMaximalSplitTorus a)
    (Q : GroupScheme (Spec (CommRingCat.of k)))
    (q : (GroupScheme.baseChange (Spec.algebraMap R k)).obj M.group ⟶ Q)
    (hmax : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ (GroupScheme.baseChange (Spec.algebraMap R k)).obj M.group),
      IsMaximalTorus i → IsMaximalTorus (i ≫ q))
    (hQ : IsConnectedReductive Q)
    (hpar : ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ Q),
      IsParabolicSubgroup p → IsIso p)
    (s : ((CommGroupScheme.baseChange (Spec.algebraMap R k)).obj S).toGrp ⟶ Q)
    (hs : IsMaximalSplitTorus s) :
    ∃ j : S.toGrp ⟶ M.group, IsClosedSubgroup j ∧
      (GroupScheme.baseChange (Spec.algebraMap R k)).map j ≫ q = s ∧
      IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj S)
        ((GroupScheme.baseChange (Spec.algebraMap R k)).map j) ∧
      IsMaximalSplitTorus (M.genericTorusMap S j) := by
  obtain ⟨T, i, hi, f, hf, -, hfmax⟩ :=
    hs.exists_maximalTorus_commFactor_of_maximalTorus_images q hmax hQ hpar
  obtain ⟨j, hj, hjres⟩ :=
    exists_closed_splitHom_lift hk S.toGrp M.group hS
      (CommGroupScheme.groupHom f ≫ i) hfmax.1.2
  refine ⟨j, hj, ?_, ?_, M.isMaximalSplitTorus_genericTorusMap_of_same_source
    hG S hS j hj a ha⟩
  · rw [hjres]
    exact hf
  · rwa [hjres]

end ResidueLift

section UnramifiedUnits

open Langlands.LocalGalois.Separable GaloisPointComparison
open scoped ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- Every integral split source fixes all points fixed by the actual
maximal-unramified integral-point group of the model. -/
theorem isFixedByUnramifiedTorusUnits_genericTorusMap_of_isSplitTorus
    (S : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F])))
    (hS : IsSplitTorus S.toGrp) (j : S.toGrp ⟶ M.group)
    {Y : Type u}
    [MulAction (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y]
    (y : Y)
    (hfix : ∀ g ∈ M.baseChangeUnramified.integralPoints, g • y = y) :
    IsFixedByUnramifiedTorusUnits F (M.genericTorusMap S j) y := by
  intro t ht
  exact hfix _
    (M.map_baseChange_genericHom_mem_integralPoints_of_split_characterKernel
      (fixedFieldIntegers F) (inertiaFixedField F)
      (MaximalUnramified.valuation_le_one_iff_mem_range (F := F)) hS j t ht)

/-- A maximal split residue source lifts with its prescribed quotient map,
is maximal over the original field by the same-source comparison, and has
unramified units fixing every point fixed by the extended model. -/
theorem exists_closed_splitSource_lift_isFixedByUnramifiedTorusUnits
    [Smooth M.group.X.hom]
    (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F])))
    (hS : IsSplitTorus S.toGrp)
    (a : ((CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj S).toGrp ⟶ G)
    (ha : IsMaximalSplitTorus a)
    (Q : GroupScheme (Spec (CommRingCat.of 𝓀[F])))
    (q : M.specialFibre ⟶ Q)
    (hmax : ∀ (T : CommGroupScheme (Spec (CommRingCat.of 𝓀[F])))
      (i : T.toGrp ⟶ M.specialFibre),
      IsMaximalTorus i → IsMaximalTorus (i ≫ q))
    (hQ : IsConnectedReductive Q)
    (hpar : ∀ (P : GroupScheme (Spec (CommRingCat.of 𝓀[F]))) (p : P ⟶ Q),
      IsParabolicSubgroup p → IsIso p)
    (s : ((CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj S).toGrp ⟶ Q)
    (hs : IsMaximalSplitTorus s)
    {Y : Type u}
    [MulAction (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y]
    (y : Y)
    (hfix : ∀ g ∈ M.baseChangeUnramified.integralPoints, g • y = y) :
    ∃ j : S.toGrp ⟶ M.group, IsClosedSubgroup j ∧
      (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).map j ≫ q = s ∧
      IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj S)
        ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).map j) ∧
      IsMaximalSplitTorus (M.genericTorusMap S j) ∧
      IsFixedByUnramifiedTorusUnits F (M.genericTorusMap S j) y := by
  let : HenselianLocalRing ↥𝒪[F] :=
    Langlands.BruhatTits.IntegralModels.henselianLocalRing_integer
  obtain ⟨j, hj, hjq, hjres, hjgen⟩ :=
    M.exists_closed_splitSource_lift_of_maximalTorus_images
      IsLocalRing.residue_surjective hG S hS a ha Q q hmax hQ hpar s hs
  exact ⟨j, hj, hjq, hjres, hjgen,
    M.isFixedByUnramifiedTorusUnits_genericTorusMap_of_isSplitTorus S hS j y hfix⟩

end UnramifiedUnits

/-- A prescribed split residue source lifts to a closed integral split
source, maximal over the original field, whose unramified units fix the
supplied point. All residue geometry and the model's point-fixing property
remain explicit. -/
def ResidueSplitTorusGenericLiftStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (M : IntegralModel ↥𝒪[F] F G)
    [Smooth M.group.X.hom],
    IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F]))),
    IsSplitTorus S.toGrp →
    ∀ (a : ((CommGroupScheme.baseChange
      (Spec.algebraMap ↥𝒪[F] F)).obj S).toGrp ⟶ G),
    IsMaximalSplitTorus a →
    ∀ (Q : GroupScheme (Spec (CommRingCat.of
      𝓀[F])))
    (q : M.specialFibre ⟶ Q),
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of
        𝓀[F])))
      (i : T.toGrp ⟶ M.specialFibre),
      IsMaximalTorus i → IsMaximalTorus (i ≫ q)) →
    IsConnectedReductive Q →
    (∀ (P : GroupScheme (Spec (CommRingCat.of
        𝓀[F]))) (p : P ⟶ Q),
      IsParabolicSubgroup p → IsIso p) →
    ∀ (s : ((CommGroupScheme.baseChange (Spec.algebraMap
      ↥𝒪[F]
      𝓀[F])).obj S).toGrp ⟶ Q),
    IsMaximalSplitTorus s →
    ∀ (Y : Type u)
    [MulAction (rationalPoints (GaloisPointComparison.baseChanged F
      (Langlands.LocalGalois.Separable.inertiaFixedField F) G)) Y]
    (y : Y),
    (∀ g ∈ M.baseChangeUnramified.integralPoints, g • y = y) →
    ∃ j : S.toGrp ⟶ M.group, IsClosedSubgroup j ∧
      (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F]
        𝓀[F])).map j ≫ q = s ∧
      IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (Spec.algebraMap
          ↥𝒪[F]
          𝓀[F])).obj S)
        ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F]
          𝓀[F])).map j) ∧
      IsMaximalSplitTorus (M.genericTorusMap S j) ∧
      IsFixedByUnramifiedTorusUnits F (M.genericTorusMap S j) y

/-- Compose the exact residue-source lift, same-source generic maximality
and the coefficient unit bound. -/
theorem residueSplitTorusGenericLift : ResidueSplitTorusGenericLiftStatement.{u} := by
  intro F _ _ _ _ G M _ hG S hS a ha Q q hmax hQ hpar s hs Y _ y hfix
  exact M.exists_closed_splitSource_lift_isFixedByUnramifiedTorusUnits
    hG S hS a ha Q q hmax hQ hpar s hs y hfix

end Langlands.GroupScheme.IntegralModel
