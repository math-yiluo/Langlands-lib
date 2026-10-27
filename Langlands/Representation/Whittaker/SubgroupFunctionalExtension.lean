import Langlands.Representation.Whittaker.FunctionalExactness
import Langlands.Representation.RankinSelberg.LocalFactor

/-! Extension from a subgroup representation and actual coefficient images. -/

noncomputable section

namespace Langlands.Whittaker

universe uR uG uV uW uI uF

section Algebraic

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- Restricting the ambient action to the localizing subgroup changes neither
the underlying functional nor its character covariance equation. -/
def functionalsRestrictionEquiv (U : Subgroup G) (θ : U →* Rˣ)
    (ρ : Representation R G V) :
    functionals U θ ρ ≃ₗ[R]
      functionals (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype)
        (ρ.comp U.subtype) where
  toFun ℓ := ⟨ℓ.val, fun u v => ℓ.property u.val v⟩
  invFun ℓ := ⟨ℓ.val, fun u v => ℓ.property ⟨u, Subgroup.mem_top u⟩ v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem functionalsRestrictionEquiv_apply (U : Subgroup G) (θ : U →* Rˣ)
    (ρ : Representation R G V) (ℓ : functionals U θ ρ) (v : V) :
    (functionalsRestrictionEquiv U θ ρ ℓ).val v = ℓ.val v := rfl

@[simp]
theorem functionalsRestrictionEquiv_symm_apply (U : Subgroup G) (θ : U →* Rˣ)
    (ρ : Representation R G V)
    (ℓ : functionals (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype)
      (ρ.comp U.subtype)) (v : V) :
    ((functionalsRestrictionEquiv U θ ρ).symm ℓ).val v = ℓ.val v := rfl

end Algebraic

section Smooth

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Compact containment is preserved when a subgroup is viewed as a group in
its own right and localized at its top subgroup. -/
theorem isLimitOfCompactSubgroups_top (U : Subgroup G)
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    Jacquet.Localization.IsLimitOfCompactSubgroups (⊤ : Subgroup U) := by
  let e : (⊤ : Subgroup U) ≃ₜ U :=
    { toEquiv := (Subgroup.topEquiv : (⊤ : Subgroup U) ≃* U).toEquiv
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  intro C hC
  obtain ⟨K, hK, hCK⟩ := hU (e '' C) (hC.image e.continuous)
  refine ⟨K.comap (⊤ : Subgroup U).subtype, ?_, ?_⟩
  · change IsCompact (e ⁻¹' (K : Set U))
    exact e.isCompact_preimage.mpr hK
  · intro c hc
    exact hCK ⟨c, hc, rfl⟩

variable [IsTopologicalGroup G]
  (U : Subgroup G) (θ : U →* ℂˣ)
  (ρ : Representation ℂ G V) (τ : Representation ℂ U W)

/-- A character-equivariant functional extends along an injective intertwiner
for the restricted subgroup action into a smooth ambient representation. -/
theorem exists_functional_extension_of_subgroup_intertwiner
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    (i : τ.IntertwiningMap (ρ.comp U.subtype)) (hi : Function.Injective i)
    (hρ : IsSmooth ρ)
    (ℓ : functionals (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype) τ) :
    ∃ L : functionals U θ ρ, ∀ w : W, L.val (i w) = ℓ.val w := by
  obtain ⟨L, hL⟩ := functionalsComap_surjective_of_smooth
    (⊤ : Subgroup U) (isLimitOfCompactSubgroups_top U hU)
    (θ.comp (⊤ : Subgroup U).subtype)
    (hθ.comp_continuous continuous_subtype_val) i hi
    (isSmooth_comp U.subtype continuous_subtype_val hρ) ℓ
  refine ⟨(functionalsRestrictionEquiv U θ ρ).symm L, fun w => ?_⟩
  exact congrArg (fun t => t.val w) hL

/-- Choose an extension supplied by smooth character-localization exactness.
No equivariance for elements outside `U` is required of the injection. -/
def extendSubgroupFunctional
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    (i : τ.IntertwiningMap (ρ.comp U.subtype)) (hi : Function.Injective i)
    (hρ : IsSmooth ρ)
    (ℓ : functionals (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype) τ) :
    functionals U θ ρ :=
  Classical.choose (exists_functional_extension_of_subgroup_intertwiner
    U θ ρ τ hU hθ i hi hρ ℓ)

@[simp]
theorem extendSubgroupFunctional_apply
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    (i : τ.IntertwiningMap (ρ.comp U.subtype)) (hi : Function.Injective i)
    (hρ : IsSmooth ρ)
    (ℓ : functionals (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype) τ)
    (w : W) :
    (extendSubgroupFunctional U θ ρ τ hU hθ i hi hρ ℓ).val (i w) = ℓ.val w :=
  Classical.choose_spec (exists_functional_extension_of_subgroup_intertwiner
    U θ ρ τ hU hθ i hi hρ ℓ) w

/-- Values calculated on vectors in the subgroup representation are values
of an actual ambient coefficient image whenever the translated vectors lift. -/
theorem exists_coefficientModel_extension
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    (i : τ.IntertwiningMap (ρ.comp U.subtype)) (hi : Function.Injective i)
    (hρ : IsSmooth ρ)
    (ℓ : functionals (⊤ : Subgroup U) (θ.comp (⊤ : Subgroup U).subtype) τ)
    (w : W) {I : Type uI} (g : I → G) (w' : I → W)
    (hw' : ∀ t, i (w' t) = ρ (g t) (i w)) :
    ∃ L : functionals U θ ρ, ∃ c : (coefficientModel ρ L).toSubmodule,
      ∀ t, c.val.val (g t) = ℓ.val (w' t) := by
  let L := extendSubgroupFunctional U θ ρ τ hU hθ i hi hρ ℓ
  refine ⟨L, modelMap ρ L (i w), fun t => ?_⟩
  change L.val (ρ (g t) (i w)) = ℓ.val (w' t)
  rw [← hw' t]
  exact extendSubgroupFunctional_apply U θ ρ τ hU hθ i hi hρ ℓ (w' t)

end Smooth

section GeneralLinear

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {n : ℕ} [IsTopologicalGroup (Langlands.GeneralLinear (n + 1) F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The preceding extension produces membership in the actual Rankin--Selberg
Whittaker set, including when the ambient representation is reducible. -/
theorem exists_whittakerSet_extension
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (τ : Representation ℂ (GeneralLinear.upperUnipotent (n + 1) F) W)
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups
      (GeneralLinear.upperUnipotent (n + 1) F))
    (hθ : IsLocallyConstant (fun u : GeneralLinear.upperUnipotent (n + 1) F =>
      (standardCharacter ψ n u : ℂ)))
    (i : τ.IntertwiningMap (ρ.comp (GeneralLinear.upperUnipotent (n + 1) F).subtype))
    (hi : Function.Injective i) (hρ : IsSmooth ρ)
    (ℓ : functionals (⊤ : Subgroup (GeneralLinear.upperUnipotent (n + 1) F))
      ((standardCharacter ψ n).comp
        (⊤ : Subgroup (GeneralLinear.upperUnipotent (n + 1) F)).subtype) τ)
    (w : W) {I : Type uI} (g : I → Langlands.GeneralLinear (n + 1) F)
    (w' : I → W) (hw' : ∀ t, i (w' t) = ρ (g t) (i w)) :
    ∃ c : RankinSelberg.WhittakerFunctions ψ n,
      c ∈ RankinSelberg.whittakerSet ψ n ρ ∧
        ∀ t, c.val (g t) = ℓ.val (w' t) := by
  obtain ⟨L, c, hc⟩ := exists_coefficientModel_extension
    (GeneralLinear.upperUnipotent (n + 1) F) (standardCharacter ψ n)
    ρ τ hU hθ i hi hρ ℓ w g w' hw'
  exact ⟨c.val, ⟨L, c.property⟩, hc⟩

end GeneralLinear

end Langlands.Whittaker
