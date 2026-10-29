import Langlands.Algebra.RenardEndomorphismQuotientStatements
import Langlands.Algebra.RenardEndomorphismLocalizationKernelProof

/-! # Injectivity and localization comparison for the actual power-kernel quotient -/

set_option autoImplicit false

universe u v

noncomputable section

namespace Langlands.Renard.EndomorphismLocalization

section

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-- The endomorphism induced on the actual quotient by the power kernel is injective. -/
theorem quotientEnd_injective (a : Module.End R V) :
    Function.Injective (quotientEnd a) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  obtain ⟨z, rfl⟩ := quotientProjection_surjective a q
  rw [quotientEnd_projection] at hq
  change a z ∈ LinearMap.ker (quotientProjection a) at hq
  rw [ker_quotientProjection, mem_powerKernel_iff] at hq
  obtain ⟨n, hn⟩ := hq
  change z ∈ LinearMap.ker (quotientProjection a)
  rw [ker_quotientProjection, mem_powerKernel_iff]
  exact ⟨n + 1, by rw [pow_succ, Module.End.mul_apply]; exact hn⟩

/-- The quotient embeds into its actual localization. -/
theorem quotientIota_injective (a : Module.End R V) :
    Function.Injective (iota (quotientEnd a)) :=
  iota_injective (quotientEnd a) (quotientEnd_injective a)

/-- Descent of the original localization map along the actual quotient projection. -/
def quotientIotaLift (a : Module.End R V) :
    PowerKernelQuotient a →ₗ[R] Localized a :=
  (powerKernel a).liftQ (iota a) (by
    intro z hz
    change iota a z = 0
    exact (iota_eq_zero_iff a z).mpr ((mem_powerKernel_iff a z).mp hz))

theorem quotientIotaLift_projection (a : Module.End R V) (z : V) :
    quotientIotaLift a (quotientProjection a z) = iota a z :=
  rfl

theorem quotientIotaLift_intertwines (a : Module.End R V) (q : PowerKernelQuotient a) :
    quotientIotaLift a (quotientEnd a q) = localizedEnd a (quotientIotaLift a q) := by
  obtain ⟨z, rfl⟩ := quotientProjection_surjective a q
  rw [quotientEnd_projection, quotientIotaLift_projection, quotientIotaLift_projection]
  exact iota_intertwines a z

/-- The map from the localized quotient to the original localization. -/
def quotientLocalizationMap (a : Module.End R V) :
    Localized (quotientEnd a) →ₗ[R] Localized a :=
  factor (quotientEnd a) (localizedEnd a) (isUnit_localizedEnd a)
    (quotientIotaLift a) (quotientIotaLift_intertwines a)

theorem quotientLocalizationMap_iota (a : Module.End R V) (q : PowerKernelQuotient a) :
    quotientLocalizationMap a (iota (quotientEnd a) q) = quotientIotaLift a q :=
  LinearMap.congr_fun
    (factor_comp_iota (quotientEnd a) (localizedEnd a) (isUnit_localizedEnd a)
      (quotientIotaLift a) (quotientIotaLift_intertwines a)) q

theorem quotientLocalizationMap_intertwines (a : Module.End R V)
    (z : Localized (quotientEnd a)) :
    quotientLocalizationMap a (localizedEnd (quotientEnd a) z) =
      localizedEnd a (quotientLocalizationMap a z) :=
  factor_intertwines (quotientEnd a) (localizedEnd a) (isUnit_localizedEnd a)
    (quotientIotaLift a) (quotientIotaLift_intertwines a) z

theorem quotientProjection_iota_intertwines (a : Module.End R V) (z : V) :
    ((iota (quotientEnd a)).comp (quotientProjection a)) (a z) =
      localizedEnd (quotientEnd a)
        (((iota (quotientEnd a)).comp (quotientProjection a)) z) := by
  change iota (quotientEnd a) (quotientProjection a (a z)) =
    localizedEnd (quotientEnd a) (iota (quotientEnd a) (quotientProjection a z))
  rw [← quotientEnd_projection, iota_intertwines]

/-- The map in the reverse direction, obtained by localizing the quotient projection. -/
def localizationQuotientMap (a : Module.End R V) :
    Localized a →ₗ[R] Localized (quotientEnd a) :=
  factor a (localizedEnd (quotientEnd a)) (isUnit_localizedEnd (quotientEnd a))
    ((iota (quotientEnd a)).comp (quotientProjection a))
    (quotientProjection_iota_intertwines a)

theorem localizationQuotientMap_iota (a : Module.End R V) (z : V) :
    localizationQuotientMap a (iota a z) =
      iota (quotientEnd a) (quotientProjection a z) :=
  LinearMap.congr_fun
    (factor_comp_iota a (localizedEnd (quotientEnd a)) (isUnit_localizedEnd (quotientEnd a))
      ((iota (quotientEnd a)).comp (quotientProjection a))
      (quotientProjection_iota_intertwines a)) z

theorem localizationQuotientMap_intertwines (a : Module.End R V) (z : Localized a) :
    localizationQuotientMap a (localizedEnd a z) =
      localizedEnd (quotientEnd a) (localizationQuotientMap a z) :=
  factor_intertwines a (localizedEnd (quotientEnd a)) (isUnit_localizedEnd (quotientEnd a))
    ((iota (quotientEnd a)).comp (quotientProjection a))
    (quotientProjection_iota_intertwines a) z

theorem quotientLocalizationMap_comp_localizationQuotientMap (a : Module.End R V) :
    (quotientLocalizationMap a).comp (localizationQuotientMap a) = LinearMap.id := by
  refine eq_of_intertwines a (localizedEnd a)
    ((Module.End.isUnit_iff _).mp (isUnit_localizedEnd a)).injective
    _ _ ?_ (fun _ => rfl) ?_
  · intro z
    change quotientLocalizationMap a (localizationQuotientMap a (localizedEnd a z)) =
      localizedEnd a (quotientLocalizationMap a (localizationQuotientMap a z))
    rw [localizationQuotientMap_intertwines, quotientLocalizationMap_intertwines]
  · ext z
    change quotientLocalizationMap a (localizationQuotientMap a (iota a z)) = iota a z
    rw [localizationQuotientMap_iota, quotientLocalizationMap_iota, quotientIotaLift_projection]

theorem localizationQuotientMap_comp_quotientLocalizationMap (a : Module.End R V) :
    (localizationQuotientMap a).comp (quotientLocalizationMap a) = LinearMap.id := by
  refine eq_of_intertwines (quotientEnd a) (localizedEnd (quotientEnd a))
    ((Module.End.isUnit_iff _).mp (isUnit_localizedEnd (quotientEnd a))).injective
    _ _ ?_ (fun _ => rfl) ?_
  · intro z
    change localizationQuotientMap a
        (quotientLocalizationMap a (localizedEnd (quotientEnd a) z)) =
      localizedEnd (quotientEnd a) (localizationQuotientMap a (quotientLocalizationMap a z))
    rw [quotientLocalizationMap_intertwines, localizationQuotientMap_intertwines]
  · apply LinearMap.ext
    intro q
    change localizationQuotientMap a (quotientLocalizationMap a (iota (quotientEnd a) q)) =
      iota (quotientEnd a) q
    rw [quotientLocalizationMap_iota]
    obtain ⟨z, rfl⟩ := quotientProjection_surjective a q
    rw [quotientIotaLift_projection, localizationQuotientMap_iota]

/-- The canonical equivalence between the actual localized quotient and original localization. -/
def quotientLocalizationEquiv (a : Module.End R V) :
    Localized (quotientEnd a) ≃ₗ[R] Localized a :=
  LinearEquiv.ofLinearMap (quotientLocalizationMap a) (localizationQuotientMap a)
    (quotientLocalizationMap_comp_localizationQuotientMap a)
    (localizationQuotientMap_comp_quotientLocalizationMap a)

theorem quotientLocalizationEquiv_comp_iota_projection (a : Module.End R V) :
    (quotientLocalizationEquiv a).toLinearMap.comp
      ((iota (quotientEnd a)).comp (quotientProjection a)) = iota a := by
  ext z
  change quotientLocalizationMap a (iota (quotientEnd a) (quotientProjection a z)) = iota a z
  rw [quotientLocalizationMap_iota, quotientIotaLift_projection]

theorem quotientLocalizationEquiv_intertwines (a : Module.End R V)
    (z : Localized (quotientEnd a)) :
    quotientLocalizationEquiv a (localizedEnd (quotientEnd a) z) =
      localizedEnd a (quotientLocalizationEquiv a z) :=
  quotientLocalizationMap_intertwines a z

/-- The two compatibility laws characterize the comparison equivalence uniquely. -/
theorem quotientLocalizationEquiv_unique (a : Module.End R V)
    (e : Localized (quotientEnd a) ≃ₗ[R] Localized a)
    (he : e.toLinearMap.comp
      ((iota (quotientEnd a)).comp (quotientProjection a)) = iota a)
    (he' : ∀ z, e (localizedEnd (quotientEnd a) z) = localizedEnd a (e z)) :
    e = quotientLocalizationEquiv a := by
  apply LinearEquiv.toLinearMap_injective
  refine eq_of_intertwines (quotientEnd a) (localizedEnd a)
    ((Module.End.isUnit_iff _).mp (isUnit_localizedEnd a)).injective
    _ _ he' (quotientLocalizationEquiv_intertwines a) ?_
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := quotientProjection_surjective a q
  exact (LinearMap.congr_fun he z).trans
    (LinearMap.congr_fun (quotientLocalizationEquiv_comp_iota_projection a) z).symm

theorem quotientLocalizationComparison (a : Module.End R V) :
    ∃! e : Localized (quotientEnd a) ≃ₗ[R] Localized a,
      e.toLinearMap.comp ((iota (quotientEnd a)).comp (quotientProjection a)) = iota a ∧
        ∀ z : Localized (quotientEnd a),
          e (localizedEnd (quotientEnd a) z) = localizedEnd a (e z) := by
  exact ⟨quotientLocalizationEquiv a,
    ⟨quotientLocalizationEquiv_comp_iota_projection a, quotientLocalizationEquiv_intertwines a⟩,
    fun e he => quotientLocalizationEquiv_unique a e he.1 he.2⟩

end

/-- Renard's quotient injectivity and comparison claims, over rings and in the field case. -/
theorem quotientLocalizationStatements : QuotientLocalizationStatements.{u, v} :=
  ⟨⟨fun _ _ _ _ _ a => quotientEnd_injective a,
      fun _ _ _ _ _ a => quotientIota_injective a,
      fun _ _ _ _ _ a => quotientLocalizationComparison a⟩,
    fun _ _ _ _ _ a =>
      ⟨quotientEnd_injective a, quotientIota_injective a, quotientLocalizationComparison a⟩⟩

end Langlands.Renard.EndomorphismLocalization
