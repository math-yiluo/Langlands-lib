import Langlands.Shimura.RestrictedLevelGaloisColimit
import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientReduction

/-! # Towers over sufficiently small levels with a commuting action, as representations of the
finite-adelic group -/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace Langlands.Shimura

open LevelHecke

namespace CompactOpenLevel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The image of the ordinary level `inverseOpposite U` under `g ↦ op g⁻¹` is `U`. -/
theorem map_inverseOpposite_subgroup (U : CompactOpenLevel Gᵐᵒᵖ) :
    (inverseOpposite U).subgroup.map
        (inverseOppositeContinuousEquiv (G := G)).toMulEquiv.toMonoidHom = U.subgroup := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hx
    refine ⟨(MulOpposite.unop x)⁻¹, ?_, ?_⟩
    · change MulOpposite.op (MulOpposite.unop x)⁻¹⁻¹ ∈ U.subgroup
      simpa using hx
    · change MulOpposite.op (MulOpposite.unop x)⁻¹⁻¹ = x
      simp

/-- Conjugating an opposite level by `op g⁻¹` conjugates the ordinary level by `g`:
`inverseOpposite (op g⁻¹ U (op g⁻¹)⁻¹) = g (inverseOpposite U) g⁻¹`. -/
theorem mem_inverseOpposite_conjLevel (g x : G) (U : CompactOpenLevel Gᵐᵒᵖ) :
    x ∈ (inverseOpposite (conjLevel (MulOpposite.op g⁻¹) U)).subgroup ↔
      g⁻¹ * x * g ∈ (inverseOpposite U).subgroup := by
  rw [mem_inverseOpposite, mem_inverseOpposite, mem_conjLevel]
  have h : (MulOpposite.op g⁻¹)⁻¹ * MulOpposite.op x⁻¹ * MulOpposite.op g⁻¹ =
      MulOpposite.op (g⁻¹ * x * g)⁻¹ := by
    apply MulOpposite.unop_injective
    simp [mul_assoc]
  rw [h]

end CompactOpenLevel

namespace SmallLevelGaloisTower

open CompactOpenLevel RestrictedLevelColimit

variable {B : Type} [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (σ : AlgebraInvolution ℚ B)
  {R : Type} [CommRing R] {Γ : Type} [Monoid Γ]

local notation "small" => σ.LevelSufficientlySmall

/-- The continuous homomorphism `g ↦ op g⁻¹` from the finite-adelic points to their opposite
group, on which the small levels live. -/
abbrev inverseOppositeHom : σ.FiniteAdelicPoints →* σ.FiniteAdelicPointsᵐᵒᵖ :=
  (inverseOppositeContinuousEquiv (G := σ.FiniteAdelicPoints)).toMulEquiv.toMonoidHom

theorem continuous_inverseOppositeHom : Continuous (inverseOppositeHom σ) :=
  (inverseOppositeContinuousEquiv (G := σ.FiniteAdelicPoints)).continuous

variable {σ} (F : σ.SmallLevelCategoryᵒᵖ ⥤ Action (ModuleCat.{0} R) Γ) (hF : IsLevelTrivial F)

/-- The colimit over sufficiently small levels of a level-trivial presheaf of modules with an
action of `Γ`, as a smooth representation of the finite-adelic points `G(A_f)`, on which
`g` acts as the element `op g⁻¹` of the opposite group, with the commuting action of `Γ`. -/
def towerAction : Action (SmoothRep.{0, 0, 0} R σ.FiniteAdelicPoints) Γ :=
  smoothRepActionPullback F hF (inverseOppositeHom σ) (continuous_inverseOppositeHom σ)

/-- The action of `γ ∈ Γ` on a class from level `U` is its action at level `U`. -/
theorem towerAction_ρ_ι_apply (γ : Γ) (U : σ.SmallLevelCategory) (x : (F.obj (op U)).V) :
    ((towerAction F hF).ρ γ).hom.hom ((ι (F ⋙ Action.forget (ModuleCat.{0} R) Γ) U).hom x) =
      (ι (F ⋙ Action.forget (ModuleCat.{0} R) Γ) U).hom (((F.obj (op U)).ρ γ).hom x) :=
  smoothRepAction_ρ_ι_apply F hF γ U x

/-- The action of `g ∈ G(A_f)` on a class from level `U`: it is the action of `op g⁻¹`, so the
class comes from the conjugate level `op g⁻¹ U (op g⁻¹)⁻¹` through the transition map of
the arrow with element `op g⁻¹`. -/
theorem towerAction_representation_ι_apply (g : σ.FiniteAdelicPoints) (U : σ.SmallLevelCategory)
    (x : (F.obj (op U)).V) :
    (towerAction F hF).V.obj.ρ g ((ι (F ⋙ Action.forget (ModuleCat.{0} R) Γ) U).hom x) =
      (ι (F ⋙ Action.forget (ModuleCat.{0} R) Γ)
          (restrictedConj small (MulOpposite.op g⁻¹) U)).hom
        ((F.map (restrictedConjArrow small (MulOpposite.op g⁻¹) U).op).hom.hom x) :=
  smoothRepAction_representation_ι_apply F hF (MulOpposite.op g⁻¹) U x

/-- The ordinary level of the conjugate level in `towerAction_representation_ι_apply` is
`g K g⁻¹`, where `K = inverseOpposite U` is the ordinary level of `U`. -/
theorem mem_inverseOpposite_restrictedConj (g : σ.FiniteAdelicPoints) (U : σ.SmallLevelCategory)
    (x : σ.FiniteAdelicPoints) :
    x ∈ (inverseOpposite (restrictedConj small (MulOpposite.op g⁻¹) U).obj).subgroup ↔
      g⁻¹ * x * g ∈ (inverseOpposite U.obj).subgroup :=
  mem_inverseOpposite_conjLevel g x U.obj

/-- The actions of `G(A_f)` and of `Γ` commute. -/
theorem towerAction_comm (γ : Γ) (g : σ.FiniteAdelicPoints) (z : (towerAction F hF).V) :
    ((towerAction F hF).ρ γ).hom.hom ((towerAction F hF).V.obj.ρ g z) =
      (towerAction F hF).V.obj.ρ g (((towerAction F hF).ρ γ).hom.hom z) :=
  Representation.IntertwiningMap.isIntertwining _ _ ((towerAction F hF).ρ γ).hom.hom g z

/-- The `Γ`-equivariant map from level `U` into the vectors of the tower fixed by the ordinary
level `inverseOpposite U = {g | op g⁻¹ ∈ U}` of `G(A_f)`. -/
def towerFixedLeg (U : σ.SmallLevelCategory) :
    F.obj (op U) ⟶
      (fixedVectorsActionFunctor R Γ (inverseOpposite U.obj).subgroup).obj (towerAction F hF) :=
  fixedLegPullback F hF (inverseOppositeHom σ) (continuous_inverseOppositeHom σ) U
    (map_inverseOpposite_subgroup U.obj)

@[simp] theorem towerFixedLeg_hom_apply_coe (U : σ.SmallLevelCategory) (x : (F.obj (op U)).V) :
    Subtype.val (show fixedVectors (towerAction F hF).V.obj.ρ (inverseOpposite U.obj).subgroup
        from (towerFixedLeg F hF U).hom.hom x) =
      (ι (F ⋙ Action.forget (ModuleCat.{0} R) Γ) U).hom x := rfl

/-- The fixed-vector comparison at every sufficiently small level: each level injects into the
tower with image the vectors fixed by that level. -/
def TowerFixedVectorComparison : Prop :=
  ∀ U : σ.SmallLevelCategory, FixedVectorComparison (F ⋙ Action.forget (ModuleCat.{0} R) Γ) U

/-- Under the fixed-vector comparison, level `U` is isomorphic, compatibly with `Γ`, to the
vectors of the tower fixed by the ordinary level `inverseOpposite U`. -/
def towerFixedLegIso (h : TowerFixedVectorComparison F) (U : σ.SmallLevelCategory) :
    F.obj (op U) ≅
      (fixedVectorsActionFunctor R Γ (inverseOpposite U.obj).subgroup).obj (towerAction F hF) :=
  fixedLegPullbackIso F hF (inverseOppositeHom σ) (continuous_inverseOppositeHom σ) U
    (map_inverseOpposite_subgroup U.obj) (h U)

@[simp] theorem towerFixedLegIso_hom (h : TowerFixedVectorComparison F)
    (U : σ.SmallLevelCategory) :
    (towerFixedLegIso F hF h U).hom = towerFixedLeg F hF U := rfl

/-- The vectors of the tower fixed by the ordinary level `inverseOpposite U`, as a module over
the Hecke algebra of that level, with the commuting action of `Γ`. -/
abbrev towerHeckeModule (U : σ.SmallLevelCategory) :
    Action (ModuleCat.{0} (LevelHeckeAlgebra R (inverseOpposite U.obj).subgroup)) Γ :=
  (heckeModuleActionFunctor R Γ (inverseOpposite U.obj).subgroup).obj (towerAction F hF)

/-- Each element of `Γ` commutes with the Hecke algebra. -/
theorem towerHeckeModule_ρ_smul (U : σ.SmallLevelCategory) (γ : Γ)
    (a : LevelHeckeAlgebra R (inverseOpposite U.obj).subgroup)
    (x : (towerHeckeModule F hF U).V) :
    ((towerHeckeModule F hF U).ρ γ).hom (a • x) = a • ((towerHeckeModule F hF U).ρ γ).hom x :=
  heckeModuleActionFunctor_ρ_smul Γ _ (towerAction F hF) γ a x

/-- The double coset `[K g K]` of the ordinary level `K = inverseOpposite U` acts on the
`K`-fixed vectors as the double-coset operator. -/
theorem doubleCoset_smul_towerHeckeModule (U : σ.SmallLevelCategory) (g : σ.FiniteAdelicPoints)
    (x : fixedVectors (towerAction F hF).V.obj.ρ (inverseOpposite U.obj).subgroup) :
    (doubleCoset (inverseOpposite U.obj) g :
        LevelHeckeAlgebra R (inverseOpposite U.obj).subgroup) •
        (show (towerHeckeModule F hF U).V from x) =
      heckeOperator (towerAction F hF).V.obj.ρ (inverseOpposite U.obj) (inverseOpposite U.obj)
        g x :=
  doubleCoset_smul _ (inverseOpposite U.obj) g x

end SmallLevelGaloisTower

end Langlands.Shimura
