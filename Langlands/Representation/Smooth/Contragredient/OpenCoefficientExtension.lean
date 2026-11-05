import Langlands.Representation.Smooth.Contragredient.FixedExtension
import Langlands.Representation.Smooth.Contragredient.OpenRestriction

/-! # Full-dual coefficient extension from an open subgroup -/

noncomputable section

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Extend an invariant algebraic functional into an ambient smooth dual,
retaining the given subgroup level and every inverse coefficient. -/
theorem exists_open_subgroup_coefficient_extension
    (H : OpenSubgroup G)
    (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)
    (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap (σ.comp H.toSubgroup.subtype))
    (hf : Function.Injective f)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    (ℓ : Module.Dual ℂ V)
    (hℓ : ∀ k ∈ K, ∀ v, ℓ (ρ k v) = ℓ v) :
    ∃ m : SmoothDual σ,
      (∀ k ∈ K.toSubgroup.map H.toSubgroup.subtype, ∀ w, m.val (σ k w) = m.val w) ∧
      (∀ v, v ∈ fixedVectors ρ K.toSubgroup →
        f v ∈ fixedVectors σ (K.toSubgroup.map H.toSubgroup.subtype)) ∧
      ∀ (v : V) (h : H), m.val (σ (h : G)⁻¹ (f v)) = ℓ (ρ h⁻¹ v) := by
  have : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  have hσH : IsSmooth (σ.comp H.toSubgroup.subtype) :=
    fun w => isSmoothVector_comp H.toSubgroup.subtype continuous_subtype_val (hσ w)
  have hfix (k : K) : ρ.dual k.val ℓ = ℓ := by
    ext v
    exact hℓ k.val⁻¹ (K.inv_mem k.property) v
  let ℓs : SmoothDual ρ := ⟨ℓ, K, hfix⟩
  let ℓK : fixedVectors (smoothContragredient ρ) K.toSubgroup :=
    ⟨ℓs, fun k => Subtype.ext (hfix k)⟩
  let mK := smoothDualFixedExtension hρ hσH f K hK ℓK
  let m : SmoothDual σ :=
    ⟨mK.val.val, (isSmoothVector_restrict_open_iff σ.dual H mK.val.val).mp
      mK.val.property⟩
  refine ⟨m, ?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩ w
    change mK.val.val (σ (k : G) w) = mK.val.val w
    have hm := congrArg (fun a : SmoothDual (σ.comp H.toSubgroup.subtype) => a.val w)
      (mK.property ⟨k⁻¹, K.inv_mem hk⟩)
    change mK.val.val (σ ((k : G)⁻¹)⁻¹ w) = mK.val.val w at hm
    simpa only [inv_inv] using hm
  · intro v hv k
    obtain ⟨a, ha, heq⟩ := k.property
    change σ k.val (f v) = f v
    rw [← heq]
    change (σ.comp H.toSubgroup.subtype) a (f v) = f v
    rw [← f.isIntertwining]
    exact congrArg f (hv ⟨a, ha⟩)
  · intro v h
    exact smoothDualFixedExtension_inverseCoefficient hρ hσH f hf K hK ℓK v h

/-- A chosen ambient smooth functional with the prescribed subgroup level. -/
def openSubgroupDualExtension
    (H : OpenSubgroup G)
    (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)
    (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap (σ.comp H.toSubgroup.subtype))
    (hf : Function.Injective f)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    (ℓ : Module.Dual ℂ V)
    (hℓ : ∀ k ∈ K, ∀ v, ℓ (ρ k v) = ℓ v) : SmoothDual σ :=
  Classical.choose
    (exists_open_subgroup_coefficient_extension H ρ hρ σ hσ f hf K hK ℓ hℓ)

theorem openSubgroupDualExtension_spec
    (H : OpenSubgroup G)
    (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)
    (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap (σ.comp H.toSubgroup.subtype))
    (hf : Function.Injective f)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    (ℓ : Module.Dual ℂ V)
    (hℓ : ∀ k ∈ K, ∀ v, ℓ (ρ k v) = ℓ v) :
    let m := openSubgroupDualExtension H ρ hρ σ hσ f hf K hK ℓ hℓ
    (∀ k ∈ K.toSubgroup.map H.toSubgroup.subtype, ∀ w, m.val (σ k w) = m.val w) ∧
      (∀ v, v ∈ fixedVectors ρ K.toSubgroup →
        f v ∈ fixedVectors σ (K.toSubgroup.map H.toSubgroup.subtype)) ∧
      ∀ (v : V) (h : H), m.val (σ (h : G)⁻¹ (f v)) = ℓ (ρ h⁻¹ v) :=
  Classical.choose_spec
    (exists_open_subgroup_coefficient_extension H ρ hρ σ hσ f hf K hK ℓ hℓ)

/-- The entire inverse-coefficient support is the preimage of the ambient
support under the actual subgroup inclusion. -/
theorem support_openSubgroupDualExtension_inverseCoefficient
    (H : OpenSubgroup G)
    (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)
    (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap (σ.comp H.toSubgroup.subtype))
    (hf : Function.Injective f)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    (ℓ : Module.Dual ℂ V)
    (hℓ : ∀ k ∈ K, ∀ v, ℓ (ρ k v) = ℓ v) (v : V) :
    Function.support (fun h : H => ℓ (ρ h⁻¹ v)) =
      Subtype.val ⁻¹' Function.support (fun g : G =>
        (openSubgroupDualExtension H ρ hρ σ hσ f hf K hK ℓ hℓ).val (σ g⁻¹ (f v))) := by
  ext h
  change (ℓ (ρ h⁻¹ v) ≠ 0) ↔
    (openSubgroupDualExtension H ρ hρ σ hσ f hf K hK ℓ hℓ).val
      (σ (h : G)⁻¹ (f v)) ≠ 0
  rw [(openSubgroupDualExtension_spec H ρ hρ σ hσ f hf K hK ℓ hℓ).2.2 v h]

end Langlands
