import Langlands.Algebra.RenardAlgebraLocalizationUniversalStatements

/-! # The B-linear universal property of the localized algebra action: proof -/

set_option autoImplicit false

universe u v w x

namespace Langlands.Renard.AlgebraActionLocalization

open Langlands.Algebra EndomorphismLocalization

section

variable {k : Type u} [CommRing k] {B : Type v} [NonUnitalRing B] [Module k B]
  {V : Type w} [AddCommGroup V] [Module k V] {W : Type x} [AddCommGroup W] [Module k W]

/-- The published scalar-linear factor of a B-linear map through an invertible B-linear
target operator is B-linear for the localized action. -/
theorem factor_map_localizedAction (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) (σ : B →ₙₐ[k] Module.End k W)
    (c : LinearIntertwiner σ σ) (hc : IsUnit c.toLinearMap) (f : LinearIntertwiner ρ σ)
    (hf : ∀ z, f (a z) = c (f z)) (b : B) (z : Localized a) :
    factor a c.toLinearMap hc f.toLinearMap hf (localizedAction a ρ ha b z) =
      σ b (factor a c.toLinearMap hc f.toLinearMap hf z) := by
  set g₀ := factor a c.toLinearMap hc f.toLinearMap hf
  have hg₀a : ∀ z, g₀ (localizedEnd a z) = c (g₀ z) :=
    factor_intertwines a c.toLinearMap hc f.toLinearMap hf
  have hg₀ι : ∀ v, g₀ (iota a v) = f v := fun v =>
    LinearMap.congr_fun (factor_comp_iota a c.toLinearMap hc f.toLinearMap hf) v
  -- The B-translate `f ∘ ρ b` again intertwines `a` with `c`.
  have hfb : ∀ v, (f.toLinearMap ∘ₗ ρ b) (a v) =
      c.toLinearMap ((f.toLinearMap ∘ₗ ρ b) v) := by
    intro v
    change f (ρ b (a v)) = c (f (ρ b v))
    rw [← ha b v, hf]
  -- Both composites are factors of `f ∘ ρ b`, so `factor_unique` identifies them.
  have h₁ := factor_unique a c.toLinearMap hc (f.toLinearMap ∘ₗ ρ b) hfb
    (g₀ ∘ₗ localizedAction a ρ ha b)
    (fun z => by
      change g₀ (localizedAction a ρ ha b (localizedEnd a z)) =
        c (g₀ (localizedAction a ρ ha b z))
      rw [localizedAction_localizedEnd, hg₀a])
    (LinearMap.ext fun v => by
      change g₀ (localizedAction a ρ ha b (iota a v)) = f (ρ b v)
      rw [localizedAction_iota, hg₀ι])
  have h₂ := factor_unique a c.toLinearMap hc (f.toLinearMap ∘ₗ ρ b) hfb
    (σ b ∘ₗ g₀)
    (fun z => by
      change σ b (g₀ (localizedEnd a z)) = c (σ b (g₀ z))
      rw [hg₀a]
      exact (c.map_action b (g₀ z)).symm)
    (LinearMap.ext fun v => by
      change σ b (g₀ (iota a v)) = f (ρ b v)
      rw [hg₀ι, f.map_action])
  exact LinearMap.congr_fun (h₁.trans h₂.symm) z

/-- For fixed data, the scalar-linear factor bundled as a linear intertwiner of the
localized action is the unique compatible factorization through `iotaIntertwiner`. -/
theorem universalProperty_of (a : Module.End k V) (ρ : B →ₙₐ[k] Module.End k V)
    (ha : ∀ b z, a (ρ b z) = ρ b (a z)) (σ : B →ₙₐ[k] Module.End k W)
    (c : LinearIntertwiner σ σ) (hc : IsUnit c.toLinearMap) (f : LinearIntertwiner ρ σ)
    (hf : ∀ z, f (a z) = c (f z)) :
    ∃! g : LinearIntertwiner (localizedAction a ρ ha) σ,
      (∀ z, g (localizedEnd a z) = c (g z)) ∧
        g.comp (iotaIntertwiner a ρ ha) = f := by
  let G : LinearIntertwiner (localizedAction a ρ ha) σ :=
    ⟨factor a c.toLinearMap hc f.toLinearMap hf,
      factor_map_localizedAction a ρ ha σ c hc f hf⟩
  refine ⟨G, ⟨factor_intertwines a c.toLinearMap hc f.toLinearMap hf,
    LinearIntertwiner.ext fun v =>
      LinearMap.congr_fun (factor_comp_iota a c.toLinearMap hc f.toLinearMap hf) v⟩, ?_⟩
  rintro g ⟨hg, hgf⟩
  have hu := factor_unique a c.toLinearMap hc f.toLinearMap hf g.toLinearMap hg
    (LinearMap.ext fun v => congrArg (fun φ => φ v) hgf)
  exact LinearIntertwiner.ext fun z => LinearMap.congr_fun hu z

end

/-- The general ring statement. -/
theorem universalProperty : UniversalPropertyStatement.{u, v, w, x} :=
  fun _ _ _ _ _ _ _ _ a ρ ha _ _ _ σ c hc f hf => universalProperty_of a ρ ha σ c hc f hf

/-- The field specialization; `fieldLocalizedAction` is by definition `localizedAction`. -/
theorem fieldUniversalProperty : FieldUniversalPropertyStatement.{u, v, w, x} :=
  fun _ _ _ _ _ _ _ _ _ _ a ρ ha _ _ _ σ c hc f hf => universalProperty_of a ρ ha σ c hc f hf

/-- The published aggregate: the ring statement and its field specialization. -/
theorem universalPropertyStatements : UniversalPropertyStatements.{u, v, w, x} :=
  ⟨universalProperty, fieldUniversalProperty⟩

end Langlands.Renard.AlgebraActionLocalization
