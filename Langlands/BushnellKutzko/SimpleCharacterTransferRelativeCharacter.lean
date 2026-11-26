import Langlands.BushnellKutzko.SimpleCharacterTransferComparison

/-! # The relative character specified by transfer -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- A character factoring through the relative determinant is invariant under
conjugation by a centralizer unit whenever both elements lie in its domain. -/
theorem factorsThroughCentralizerDet_conj_eq {β : A} {H : Subgroup G}
    {θ : H →* ℂˣ} (hθ : factorsThroughCentralizerDet β θ) (hf : IsField (elementAlgebra β))
    {g : G} (hg : g ∈ centralizerUnitGroup β) {x : H} (hx : g * (x : G) * g⁻¹ ∈ H)
    (hxC : (x : G) ∈ centralizerUnitGroup β) : θ ⟨_, hx⟩ = θ x := by
  let E := elementAlgebra β
  let : Field E := hf.toField
  let ι := relativeEndUnits (F := F) (V := V) E
  have hr := relativeEndUnits_range_eq_centralizer β hf
  change ι.range = centralizerUnitGroup β at hr
  obtain ⟨u, hu⟩ := (hr.symm ▸ hg : g ∈ ι.range)
  obtain ⟨v, hv⟩ := (hr.symm ▸ hxC : (x : G) ∈ ι.range)
  have hval : ι (u * v * u⁻¹) = g * (x : G) * g⁻¹ := by rw [map_mul, map_mul, map_inv, hu, hv]
  have hleft : ι (u * v * u⁻¹) ∈ H := hval.symm ▸ hx
  have hright : ι v ∈ H := hv.symm ▸ x.2
  have hdet : LinearMap.det ((u * v * u⁻¹ : (Module.End E V)ˣ) : Module.End E V) =
      LinearMap.det (v : Module.End E V) := by
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, mul_comm (LinearMap.det (u : Module.End E V)),
      mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have h := factorsThroughCentralizerDet_apply_eq hθ hf (u * v * u⁻¹) v hleft hright hdet
  exact (congrArg θ (Subtype.ext hval)).symm.trans (h.trans (congrArg θ (Subtype.ext hv)))

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

set_option maxHeartbeats 600000 in
/-- The first character's determinant restriction defines a character on the
second relative unit subgroup at equal normalized depths. -/
theorem exists_relativeCharacter_of_equal_normalized_depth (L M : LatticeChain 𝒪[F] F V)
    (n : ℤ) (β : A) (tail : List A) (m₁ m₂ : ℕ) (hf : IsField (elementAlgebra β))
    (hL : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer)
    (hM : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ M.stabilizer)
    (hm : m₁ / (L.period / elementRamificationIndex F β) =
      m₂ / (M.period / elementRamificationIndex F β))
    (θ₁ : simpleHGroup L n β tail (m₁ + 1) →* ℂˣ) (hθ₁ : factorsThroughCentralizerDet β θ₁) :
    letI := hf.toField
    let E := elementAlgebra β
    let ι := relativeEndUnits (F := F) (V := V) E
    let H₁ := simpleHGroup L n β tail (m₁ + 1)
    let U₂ := relativeUnitFiltration M β (m₂ + 1)
    ∃ χU : U₂ →* ℂˣ, factorsThroughCentralizerDet β χU ∧
      ∀ (x y : (Module.End E V)ˣ) (hx : ι x ∈ H₁) (hy : ι y ∈ U₂),
        LinearMap.det (x : Module.End E V) = LinearMap.det (y : Module.End E V) →
          θ₁ ⟨_, hx⟩ = χU ⟨_, hy⟩ := by
  let E := elementAlgebra β
  let : Field E := hf.toField
  let := L.finiteDimensional
  let : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra β))
  let ι := relativeEndUnits (F := F) (V := V) E
  let H₁ := simpleHGroup L n β tail (m₁ + 1)
  let U₂ := relativeUnitFiltration M β (m₂ + 1)
  let R₁ := H₁.comap ι
  let R₂ := U₂.comap ι
  have hm' : m₁ / (L.period / subfieldRamificationIndex F E) =
      m₂ / (M.period / subfieldRamificationIndex F E) := by
    simpa only [elementRamificationIndex, hf, dite_true] using hm
  have hrange : ι.range = centralizerUnitGroup β := relativeEndUnits_range_eq_centralizer β hf
  have hiR (x : (Module.End E V)ˣ) : ι x ∈ centralizerUnitGroup β := hrange ▸ ⟨x, rfl⟩
  have hR₁ (x : (Module.End E V)ˣ) : x ∈ R₁ ↔ ι x ∈ L.unitFiltration (m₁ + 1) :=
    ⟨fun hx => simpleHGroup_le_unitFiltration L n β tail _ hx,
      fun hx => relativeUnitFiltration_le_simpleHGroup L n β tail _ ⟨hiR x, hx⟩⟩
  have hR₂ (x : (Module.End E V)ˣ) : x ∈ R₂ ↔ ι x ∈ M.unitFiltration (m₂ + 1) :=
    ⟨fun hx => hx.2, fun hx => ⟨hiR x, hx⟩⟩
  have hmap : R₂.map ι = U₂ := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hu
      obtain ⟨x, rfl⟩ := (hrange.symm ▸ hu.1 : u ∈ ι.range)
      exact ⟨x, hu, rfl⟩
  have hi : Function.Injective ι := by
    intro x y heq
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact congrArg (fun g : G => (g : A) v) heq
  let e₂ := (R₂.equivMapOfInjective ι hi).trans (MulEquiv.subgroupCongr hmap)
  let d₁ := (Units.map (LinearMap.det : Module.End E V →* E)).comp R₁.subtype
  let d₂ := (Units.map (LinearMap.det : Module.End E V →* E)).comp R₂.subtype
  have hd : d₂.range = d₁.range := by
    ext u
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨x, hx, heq⟩ := exists_relative_unit_in_inf_with_det L M hL hM m₁ m₂ hm' ((hR₂ y).mp y.2)
      exact ⟨⟨x, (hR₁ x).mpr hx.1⟩, Units.ext heq⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy, heq⟩ := exists_relative_unit_in_inf_with_det M L hM hL m₂ m₁ hm'.symm ((hR₁ x).mp x.2)
      exact ⟨⟨y, (hR₂ y).mpr hy.1⟩, Units.ext heq⟩
  obtain ⟨_, η, hη⟩ := hθ₁
  let η₂ : d₂.range →* ℂˣ := η.comp (MulEquiv.subgroupCongr hd).toMonoidHom
  let χU : U₂ →* ℂˣ := (η₂.comp d₂.rangeRestrict).comp e₂.symm.toMonoidHom
  have hχU (y : R₂) : χU (e₂ y) = η₂ (d₂.rangeRestrict y) := by simp [χU]
  refine ⟨χU, ⟨hf, η₂, hχU⟩, ?_⟩
  intro x y hx hy hdet
  rw [show χU ⟨ι y, hy⟩ = η₂ (d₂.rangeRestrict ⟨y, hy⟩) from hχU ⟨y, hy⟩, hη ⟨x, hx⟩]
  exact congrArg η (Subtype.ext (Units.ext hdet))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A character agreeing on the relative units with a determinant character
itself factors through the relative determinant. -/
theorem factorsThroughCentralizerDet_of_restriction (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (β : A) (tail : List A) (k : ℕ)
    (η : relativeUnitFiltration L β k →* ℂˣ)
    (θ : simpleHGroup L n β tail k →* ℂˣ)
    (hη : factorsThroughCentralizerDet β η)
    (hres : ∀ u : relativeUnitFiltration L β k,
      θ ⟨u, relativeUnitFiltration_le_simpleHGroup L n β tail k u.2⟩ = η u) :
    factorsThroughCentralizerDet β θ := by
  obtain ⟨hf, χ, hχ⟩ := hη
  let E := elementAlgebra β
  let : Field E := hf.toField
  let ι := relativeEndUnits (F := F) (V := V) E
  let U := relativeUnitFiltration L β k
  let H := simpleHGroup L n β tail k
  have hR : H.comap ι = U.comap ι := by
    ext x
    constructor
    · intro hx
      have hrange : ι.range = centralizerUnitGroup β := relativeEndUnits_range_eq_centralizer β hf
      exact ⟨hrange ▸ ⟨x, rfl⟩, simpleHGroup_le_unitFiltration L n β tail _ hx⟩
    · exact fun hx => relativeUnitFiltration_le_simpleHGroup L n β tail k hx
  let d₁ := (Units.map (LinearMap.det : Module.End E V →* E)).comp (H.comap ι).subtype
  let d₂ := (Units.map (LinearMap.det : Module.End E V →* E)).comp (U.comap ι).subtype
  have hRange : d₁.range = d₂.range := by
    dsimp only [d₁, d₂]
    rw [hR]
  refine ⟨hf, χ.comp (MulEquiv.subgroupCongr hRange).toMonoidHom, ?_⟩
  intro x
  let x' : U.comap ι := ⟨x, hR ▸ x.2⟩
  have h := (hres ⟨ι x', x'.2⟩).trans (hχ x')
  exact h.trans (congrArg χ (Subtype.ext rfl))

end Langlands.BushnellKutzko
