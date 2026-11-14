import Langlands.Geometry.Building.ResidueMaximalTorusApartment
import Langlands.Geometry.Building.TorusUnitFixedPoint

/-! # Unit fixation from a maximal residue torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme
open Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- A conjugacy by a point of a subgroup transfers the character-kernel
bound to the second source without assuming its bound separately. -/
theorem map_characterValuationKernel_le_of_conjugacy
    {K : Type u} [Field K]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀)
    {A B G : GroupScheme (Spec (CommRingCat.of K))}
    {i : A ⟶ G} {j : B ⟶ G} (e : A ≅ B) (g : rationalPoints G)
    (he : i ≫ (G.innerIso g).hom = e.hom ≫ j)
    (P : Subgroup (rationalPoints G)) (hg : g ∈ P)
    (hb : (characterValuationKernel v A).map (rationalPoints.map i) ≤ P) :
    (characterValuationKernel v B).map (rationalPoints.map j) ≤ P := by
  rintro _ ⟨t, ht, rfl⟩
  have hs : rationalPoints.map e.inv t ∈ characterValuationKernel v A :=
    map_characterValuationKernel_le v e.inv ⟨t, ht, rfl⟩
  have hi : rationalPoints.map i (rationalPoints.map e.inv t) ∈ P :=
    hb ⟨_, hs, rfl⟩
  have h : e.inv ≫ i ≫ (G.innerIso g).hom = j := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun f => e.inv ≫ f) he
  have hp := congrArg (fun f => rationalPoints.map f t) h
  change (t ≫ e.inv.hom.hom ≫ i.hom.hom) ≫ (G.innerIso g).hom.hom.hom =
    t ≫ j.hom.hom at hp
  rw [comp_innerIso_hom, constantPoint_self] at hp
  have hpoint : g * rationalPoints.map i (rationalPoints.map e.inv t) * g⁻¹ =
      rationalPoints.map j t := by
    exact hp
  rw [← hpoint]
  exact P.mul_mem (P.mul_mem hg hi) (P.inv_mem hg)

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [ValuationRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    [ConnectedSpace M.specialFibre.X.left]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (hv : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    {T : CommGroupScheme (Spec (CommRingCat.of K))} {i : T.toGrp ⟶ G}
    {U : CommGroupScheme (Spec (CommRingCat.of R))} (j : U.toGrp ⟶ M.group)

include hv

/-- Actual residue maximality and one bounded generic maximal split torus
give both generic maximality and the unit bound of the supplied integral torus. -/
theorem isMaximalSplitTorus_and_characterValuationKernel_le_of_bounded_residueMaximal
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hb : (characterValuationKernel v T.toGrp).map (rationalPoints.map i) ≤
      M.integralPoints)
    (hU : IsSplitTorus U.toGrp)
    (hres : IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj U)
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).map j)) :
    IsMaximalSplitTorus (M.genericTorusMap U j) ∧
      (characterValuationKernel v
        ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj U).toGrp).map
          (rationalPoints.map (M.genericTorusMap U j)) ≤ M.integralPoints := by
  have : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj
        M.group).X.left := by
    change ConnectedSpace M.specialFibre.X.left
    infer_instance
  obtain ⟨hmax, g, hg, e, he⟩ :=
    M.exists_integralPoint_conjugacy_of_bounded_residueMaximal v hv j hG hi hb hU hres
  let a : T.toGrp ≅ ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj U).toGrp :=
    { hom := CommGroupScheme.groupHom e.hom
      inv := CommGroupScheme.groupHom e.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id }
  exact ⟨hmax,
    map_characterValuationKernel_le_of_conjugacy v a g he M.integralPoints hg hb⟩

end IntegralModel

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.BruhatTits.IntegralModels

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom]

local instance : HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F

local instance : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

local instance : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).isAlgClosed

local instance : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

/-- The actual apartment bound supplies both generic maximality and the
second torus's unit bound. Every scalar-extended source factoring through
that torus fixes every point fixed by the model's integral points. -/
theorem isFixedByUnramifiedTorusUnits_of_residueMaximal
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Ω : Set C.Apartment)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    [Smooth M.group.X.hom] [ConnectedSpace M.specialFibre.X.left]
    {U : CommGroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))}
    (j : U.toGrp ⟶ M.group) (hU : IsSplitTorus U.toGrp)
    (hres : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap (fixedFieldIntegers F)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj U)
      ((GroupScheme.baseChange (Spec.algebraMap (fixedFieldIntegers F)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).map j))
    (hpts : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤ M.integralPoints)
    (Y : Set C.ReducedBuilding) (hfix : M.integralPoints ≤ C.pointwiseFixer Y)
    {A : GroupScheme (Spec (CommRingCat.of F))} (a : A ⟶ G)
    (f : baseChanged F (inertiaFixedField F) A ⟶
      ((CommGroupScheme.baseChange
        (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).obj U).toGrp)
    (hf : (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map a =
      f ≫ M.genericTorusMap U j) :
    IsMaximalSplitTorus (M.genericTorusMap U j) ∧
      (characterValuationKernel (MaximalUnramified.valuation F)
        ((CommGroupScheme.baseChange
          (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).obj U).toGrp).map
            (rationalPoints.map (M.genericTorusMap U j)) ≤ M.integralPoints ∧
      ∀ y ∈ Y, IsFixedByUnramifiedTorusUnits F a y := by
  obtain ⟨hmax, hbound⟩ :=
    M.isMaximalSplitTorus_and_characterValuationKernel_le_of_bounded_residueMaximal
      (MaximalUnramified.valuation F) (SpecialTorusIntegralModel.valuation_units_eq_one F)
      j C.isConnectedReductive C.isMaximalSplitTorus
      ((map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer C E Ω).trans hpts)
      hU hres
  refine ⟨hmax, hbound, ?_⟩
  intro y hy t ht
  change rationalPoints.map
    ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map a) t • y = y
  rw [hf]
  have ht' := map_characterValuationKernel_le (MaximalUnramified.valuation F) f
    ⟨t, ht, rfl⟩
  have himage :
      rationalPoints.map (M.genericTorusMap U j) (rationalPoints.map f t) ∈
        M.integralPoints :=
    hbound ⟨_, ht', rfl⟩
  exact (C.apartment.mem_pointwiseFixer.mp (hfix himage)) y hy

end Unramified

/-- A supplied split integral torus with maximal actual residue map has
maximal split generic map and bounded unit image, from one bounded generic
maximal split torus in the same smooth model. -/
def ResidueMaximalTorusUnitsStatement : Prop :=
  ∀ (R K Γ₀ : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [ValuationRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] [Field K]
    [Algebra R K] [IsFractionRing R K] [LinearOrderedCommGroupWithZero Γ₀]
    (G : GroupScheme (Spec (CommRingCat.of K)))
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    [ConnectedSpace M.specialFibre.X.left]
    (v : Valuation K Γ₀) (_ : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
    (U : CommGroupScheme (Spec (CommRingCat.of R))) (j : U.toGrp ⟶ M.group),
    IsConnectedReductive G →
    IsMaximalSplitTorus i →
    (characterValuationKernel v T.toGrp).map (rationalPoints.map i) ≤ M.integralPoints →
    IsSplitTorus U.toGrp →
    IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj U)
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).map j) →
    IsMaximalSplitTorus (M.genericTorusMap U j) ∧
      (characterValuationKernel v
        ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj U).toGrp).map
          (rationalPoints.map (M.genericTorusMap U j)) ≤ M.integralPoints

/-- Transfer the known bound by the actual integral conjugacy. -/
theorem residueMaximalTorusUnits : ResidueMaximalTorusUnitsStatement.{u} := by
  intro R K Γ₀ _ _ _ _ _ _ _ _ _ _ G M _ _ v hv T i U j hG hi hb hU hres
  exact M.isMaximalSplitTorus_and_characterValuationKernel_le_of_bounded_residueMaximal
    v hv j hG hi hb hU hres

end Langlands.Geometry.Building
