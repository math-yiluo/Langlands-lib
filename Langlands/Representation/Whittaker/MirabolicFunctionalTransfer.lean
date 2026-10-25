import Langlands.Representation.Whittaker.MirabolicModels
import Langlands.Representation.Whittaker.FunctionalLength
import Langlands.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! Functional spaces and exactness inputs for the actual mirabolic restriction. -/

noncomputable section

namespace Langlands.Whittaker

universe uF uG uV

/-- A nonzero equivariant functional on a smooth representation forces the
scalar character to be locally constant. -/
theorem character_isLocallyConstant_of_hasFunctional
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (U : Subgroup G) (θ : U →* ℂˣ) (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hℓ : HasFunctional (N := U) (θ := θ) ρ) :
    IsLocallyConstant (fun u : U => (θ u : ℂ)) := by
  obtain ⟨ℓ, hℓ⟩ := hℓ
  obtain ⟨v, hv⟩ : ∃ v : V, ℓ.val v ≠ 0 := by
    by_contra! h
    exact hℓ (LinearMap.ext h)
  have hcoef : IsLocallyConstant (fun u : U => matrixCoefficient ρ ℓ.val v u.val) :=
    (matrixCoefficient_isLocallyConstant ρ ℓ.val v (hρ v)).comp_continuous
      continuous_subtype_val
  have heq : (fun u : U => (θ u : ℂ)) =
      (fun u : U => matrixCoefficient ρ ℓ.val v u.val / ℓ.val v) := by
    funext u
    rw [matrixCoefficient_apply, ℓ.property u v, mul_div_cancel_right₀ _ hv]
  rw [heq]
  exact hcoef.div (IsLocallyConstant.const _)

section Algebraic

open GeneralLinear

variable {F : Type uF} [CommRing F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Restriction to the actual mirabolic group preserves the full functional
space for any character of its upper-unipotent subgroup. -/
def mirabolicFunctionalsEquiv
    (θ : GeneralLinear.upperUnipotent (n + 1) F →* ℂˣ)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    functionals (GeneralLinear.upperUnipotent (n + 1) F) θ ρ ≃ₗ[ℂ]
      functionals (Mirabolic.upperUnipotent n F)
        (θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom)
        (ρ.comp (mirabolic n F).subtype) where
  toFun ℓ := ⟨ℓ.val, fun u v => ℓ.property (Mirabolic.upperUnipotentEquiv u) v⟩
  invFun ℓ := ⟨ℓ.val, fun u v => ℓ.property (Mirabolic.upperUnipotentEquiv.symm u) v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem mirabolicFunctionalsEquiv_val
    (θ : GeneralLinear.upperUnipotent (n + 1) F →* ℂˣ)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : functionals (GeneralLinear.upperUnipotent (n + 1) F) θ ρ) :
    (mirabolicFunctionalsEquiv θ ρ ℓ).val = ℓ.val := rfl

end Algebraic

end Langlands.Whittaker

namespace Langlands.GeneralLinear.Mirabolic

universe uF

/-- Compact containment transports through the actual unipotent group
identification, for the supplied field topology. -/
theorem upperUnipotent_isLimitOfCompactSubgroups {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    Jacquet.Localization.IsLimitOfCompactSubgroups (upperUnipotent n F.Carrier) := by
  let := T.topology
  let e := upperUnipotentContinuousEquiv (n := n) (F := F.Carrier)
  intro C hC
  obtain ⟨K, hK, hCK⟩ := GeneralLinear.upperUnipotent_isLimitOfCompactSubgroups F T (n + 1)
    (e '' C) (hC.image e.continuous)
  refine ⟨K.comap e.toMonoidHom, e.toHomeomorph.isCompact_preimage.mpr hK, ?_⟩
  intro u hu
  exact hCK (Set.mem_image_of_mem e hu)

end Langlands.GeneralLinear.Mirabolic

namespace Langlands.Whittaker

open GeneralLinear

universe uF uV

/-- A smooth GL representation with a one-dimensional functional space has
exactly one functional-bearing factor in any supplied finite mirabolic filtration. -/
theorem mirabolic_existsUnique_hasFunctional_factor {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (θ : GeneralLinear.upperUnipotent (n + 1) F.Carrier →* ℂˣ) :
    letI := T.topology
    ∀ (_hρ : IsSmooth ρ)
      (_e : functionals (GeneralLinear.upperUnipotent (n + 1) F.Carrier) θ ρ ≃ₗ[ℂ] ℂ)
      {m : ℕ} (f : ObjectRepFiltration (Rep.of (ρ.comp (mirabolic n F.Carrier).subtype)) m),
      ∃! i : Fin m, HasFunctional (N := Mirabolic.upperUnipotent n F.Carrier)
        (θ := θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom)
        (f.gradedRepresentation i).ρ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hρ e m f
  let ρP := ρ.comp (mirabolic n F.Carrier).subtype
  let θP := θ.comp Mirabolic.upperUnipotentEquiv.toMonoidHom
  let eP : functionals (Mirabolic.upperUnipotent n F.Carrier) θP ρP ≃ₗ[ℂ] ℂ :=
    (mirabolicFunctionalsEquiv θ ρ).symm.trans e
  have hρP : IsSmooth ρP := isSmooth_comp _ continuous_subtype_val hρ
  have hfun : HasFunctional (N := Mirabolic.upperUnipotent n F.Carrier) (θ := θP) ρP :=
    (functionalLength_ne_zero_iff _ _ _).mp (by
      rw [functionalLength_eq_one_of_equiv _ _ _ eP]
      exact one_ne_zero)
  exact existsUnique_hasFunctional_factor _ (Mirabolic.upperUnipotent_isLimitOfCompactSubgroups F T n)
    θP (character_isLocallyConstant_of_hasFunctional _ _ _ hρP hfun) f hρP eP

end Langlands.Whittaker
