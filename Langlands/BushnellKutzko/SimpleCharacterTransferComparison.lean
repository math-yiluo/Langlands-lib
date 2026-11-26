import Langlands.BushnellKutzko.SimpleCharacterTransferMinimal
import Langlands.BushnellKutzko.ElementFieldInvariants

/-! # Comparing the relative restrictions of simple characters -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uG

/-- For an untwisted intersection comparison, the membership witnesses are
provided by the two projections of the intersection. -/
theorem characterAgreesOn_inf_iff {G : Type uG} [Group G] {H₁ H₂ : Subgroup G}
    (θ₁ : H₁ →* ℂˣ) (θ₂ : H₂ →* ℂˣ) :
    characterAgreesOn (H₁ ⊓ H₂) θ₁ θ₂ (fun _ => 1) ↔
      ∀ (x : G) (hx₁ : x ∈ H₁) (hx₂ : x ∈ H₂), θ₁ ⟨x, hx₁⟩ = θ₂ ⟨x, hx₂⟩ := by
  constructor
  · intro h x hx₁ hx₂
    obtain ⟨_, _, heq⟩ := h ⟨x, ⟨hx₁, hx₂⟩⟩
    exact Units.ext (by simpa only [mul_one] using heq)
  · intro h x
    exact ⟨x.2.1, x.2.2, by rw [h x x.2.1 x.2.2, mul_one]⟩

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- The relative units are exactly the units commuting with the generator. -/
theorem relativeEndUnits_range_eq_centralizer (β : A) (hf : IsField (elementAlgebra β)) :
    letI := hf.toField
    (relativeEndUnits (elementAlgebra β)).range = centralizerUnitGroup β := by
  let E := elementAlgebra β
  let : Field E := hf.toField
  let ι := relativeEndUnits (F := F) (V := V) E
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    change β * (ι x : A) = (ι x : A) * β
    ext v
    let b : E := ⟨β, Algebra.self_mem_adjoin_singleton F β⟩
    exact ((x : Module.End E V).map_smul b v).symm
  · intro hg
    change Commute β (g : A) at hg
    let x : Module.End E V :=
      { toFun := (g : A)
        map_add' := (g : A).map_add
        map_smul' := map_smul_elementAlgebra_of_commute hg }
    let y : Module.End E V :=
      { toFun := ((g⁻¹ : G) : A)
        map_add' := ((g⁻¹ : G) : A).map_add
        map_smul' := map_smul_elementAlgebra_of_commute hg.units_inv_right }
    have hxy : x * y = 1 := by
      ext v
      exact LinearMap.congr_fun (Units.mul_inv g) v
    have hyx : y * x = 1 := by
      ext v
      exact LinearMap.congr_fun (Units.inv_mul g) v
    exact ⟨⟨x, y, hxy, hyx⟩, Units.ext rfl⟩

/-- A character factoring through the relative determinant is constant on its
fibres on the pullback of its domain. -/
theorem factorsThroughCentralizerDet_apply_eq {β : A} {H : Subgroup G}
    {θ : H →* ℂˣ} (hθ : factorsThroughCentralizerDet β θ) (hf : IsField (elementAlgebra β)) :
    letI := hf.toField
    ∀ (x y : (Module.End (elementAlgebra β) V)ˣ)
      (hx : relativeEndUnits (elementAlgebra β) x ∈ H)
      (hy : relativeEndUnits (elementAlgebra β) y ∈ H),
      LinearMap.det (x : Module.End (elementAlgebra β) V) =
        LinearMap.det (y : Module.End (elementAlgebra β) V) →
        θ ⟨_, hx⟩ = θ ⟨_, hy⟩ := by
  let E := elementAlgebra β
  let : Field E := hf.toField
  intro x y hx hy hdet
  obtain ⟨_, η, hη⟩ := hθ
  let ι := relativeEndUnits (F := F) (V := V) E
  let U := H.comap ι
  let d := (Units.map (LinearMap.det : Module.End E V →* E)).comp U.subtype
  have hdet' : d.rangeRestrict (⟨x, hx⟩ : U) = d.rangeRestrict (⟨y, hy⟩ : U) :=
    Subtype.ext (Units.ext hdet)
  have h₁ : θ ⟨_, hx⟩ = η (d.rangeRestrict ⟨x, hx⟩) := hη ⟨x, hx⟩
  have h₂ : θ ⟨_, hy⟩ = η (d.rangeRestrict ⟨y, hy⟩) := hη ⟨y, hy⟩
  rw [h₁, h₂, hdet']

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Agreement on a common positive-depth simple-character domain determines
the relative restriction on the second chain. -/
theorem eq_on_relativeUnitFiltration_of_agreement (L M : LatticeChain 𝒪[F] F V)
    (n₁ n₂ : ℤ) (β : A) (tail₁ tail₂ : List A) (m₁ m₂ : ℕ) (hf : IsField (elementAlgebra β))
    (hL : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer)
    (hM : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ M.stabilizer)
    (hm : m₁ / (L.period / elementRamificationIndex F β) =
      m₂ / (M.period / elementRamificationIndex F β))
    {θ₁ : simpleHGroup L n₁ β tail₁ (m₁ + 1) →* ℂˣ}
    {θ₂ θ₂' : simpleHGroup M n₂ β tail₂ (m₂ + 1) →* ℂˣ}
    (hθ₂ : factorsThroughCentralizerDet β θ₂) (hθ₂' : factorsThroughCentralizerDet β θ₂')
    (h₁ : characterAgreesOn (simpleHGroup L n₁ β tail₁ (m₁ + 1) ⊓
      simpleHGroup M n₂ β tail₂ (m₂ + 1)) θ₁ θ₂ (fun _ => 1))
    (h₂ : characterAgreesOn (simpleHGroup L n₁ β tail₁ (m₁ + 1) ⊓
      simpleHGroup M n₂ β tail₂ (m₂ + 1)) θ₁ θ₂' (fun _ => 1)) :
    ∀ g (hg : g ∈ relativeUnitFiltration M β (m₂ + 1)),
      θ₂ ⟨g, relativeUnitFiltration_le_simpleHGroup M n₂ β tail₂ (m₂ + 1) hg⟩ =
        θ₂' ⟨g, relativeUnitFiltration_le_simpleHGroup M n₂ β tail₂ (m₂ + 1) hg⟩ := by
  let E := elementAlgebra β
  let : Field E := hf.toField
  let := L.finiteDimensional
  let : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra β))
  let ι := relativeEndUnits (F := F) (V := V) E
  have hrange : ι.range = centralizerUnitGroup β := relativeEndUnits_range_eq_centralizer β hf
  have hnorm : m₁ / (L.period / subfieldRamificationIndex F E) =
      m₂ / (M.period / subfieldRamificationIndex F E) := by
    simpa only [elementRamificationIndex, hf, dite_true] using hm
  intro g hg
  have hgC : g ∈ ι.range := hrange ▸ hg.1
  obtain ⟨y, rfl⟩ := hgC
  obtain ⟨x, hx, hdet⟩ := exists_relative_unit_in_inf_with_det L M hL hM m₁ m₂ hnorm hg.2
  have hxC : ι x ∈ centralizerUnitGroup β := hrange ▸ ⟨x, rfl⟩
  have hx₁ := relativeUnitFiltration_le_simpleHGroup L n₁ β tail₁ (m₁ + 1)
    (show ι x ∈ relativeUnitFiltration L β (m₁ + 1) from ⟨hxC, hx.1⟩)
  have hx₂ := relativeUnitFiltration_le_simpleHGroup M n₂ β tail₂ (m₂ + 1)
    (show ι x ∈ relativeUnitFiltration M β (m₂ + 1) from ⟨hxC, hx.2⟩)
  have hy₂ := relativeUnitFiltration_le_simpleHGroup M n₂ β tail₂ (m₂ + 1) hg
  calc θ₂ ⟨ι y, hy₂⟩ = θ₂ ⟨ι x, hx₂⟩ :=
           factorsThroughCentralizerDet_apply_eq hθ₂ hf y x hy₂ hx₂ hdet.symm
       _ = θ₁ ⟨ι x, hx₁⟩ := ((characterAgreesOn_inf_iff _ _).mp h₁ _ hx₁ hx₂).symm
       _ = θ₂' ⟨ι x, hx₂⟩ := (characterAgreesOn_inf_iff _ _).mp h₂ _ hx₁ hx₂
       _ = θ₂' ⟨ι y, hy₂⟩ := factorsThroughCentralizerDet_apply_eq hθ₂' hf x y hx₂ hy₂ hdet

/-- In the terminal case, at most one character on the second chain can agree
with the given character on the first chain at equal relative normalized depths. -/
theorem simpleCharacterTransfer_unique_nil (ψF : AddChar F ℂ)
    (L M : LatticeChain 𝒪[F] F V) (n₁ n₂ : ℤ) (β : A) (tail₁ : List A) (m₁ m₂ : ℕ)
    (hf : IsField (elementAlgebra β))
    (hL : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer)
    (hM : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ M.stabilizer)
    (hm : m₁ / (L.period / elementRamificationIndex F β) =
      m₂ / (M.period / elementRamificationIndex F β))
    {θ₁ : simpleHGroup L n₁ β tail₁ (m₁ + 1) →* ℂˣ}
    {θ₂ θ₂' : simpleHGroup M n₂ β [] (m₂ + 1) →* ℂˣ}
    (hmem : θ₂ ∈ simpleCharacters ψF M n₂ β [] m₂)
    (hmem' : θ₂' ∈ simpleCharacters ψF M n₂ β [] m₂)
    (h₁ : characterAgreesOn (simpleHGroup L n₁ β tail₁ (m₁ + 1) ⊓
      simpleHGroup M n₂ β [] (m₂ + 1)) θ₁ θ₂ (fun _ => 1))
    (h₂ : characterAgreesOn (simpleHGroup L n₁ β tail₁ (m₁ + 1) ⊓
      simpleHGroup M n₂ β [] (m₂ + 1)) θ₁ θ₂' (fun _ => 1)) : θ₂ = θ₂' := by
  have hmem₁ := show (∀ g : simpleHGroup M n₂ β [] (m₂ + 1),
      (g : G) ∈ M.unitFiltration (simpleHCutoff n₂).toNat →
      (θ₂ g : ℂ) = elementCharacter (traceCharacter ψF) β g) ∧
      factorsThroughCentralizerDet β θ₂ from hmem
  have hmem₂ := show (∀ g : simpleHGroup M n₂ β [] (m₂ + 1),
      (g : G) ∈ M.unitFiltration (simpleHCutoff n₂).toNat →
      (θ₂' g : ℂ) = elementCharacter (traceCharacter ψF) β g) ∧
      factorsThroughCentralizerDet β θ₂' from hmem'
  let H := simpleHGroup M n₂ β [] (m₂ + 1)
  let U := relativeUnitFiltration M β (m₂ + 1)
  let D := M.unitFiltration (max (m₂ + 1) (simpleHCutoff n₂).toNat)
  let K := (θ₂.eqLocus θ₂').map H.subtype
  have hH : H = U ⊔ D := simpleHGroup_nil_eq_sup M n₂ β (m₂ + 1) (by omega)
  have hU : U ≤ K := by
    intro g hg
    refine ⟨⟨g, relativeUnitFiltration_le_simpleHGroup M n₂ β [] (m₂ + 1) hg⟩, ?_, rfl⟩
    exact eq_on_relativeUnitFiltration_of_agreement L M n₁ n₂ β tail₁ [] m₁ m₂ hf hL hM hm
      hmem₁.2 hmem₂.2 h₁ h₂ g hg
  have hHD : D ≤ H := hH.symm ▸ le_sup_right
  have hD : D ≤ K := by
    intro g hg
    refine ⟨⟨g, hHD hg⟩, ?_, rfl⟩
    have hcut := M.unitFiltration_antitone (Nat.le_max_right (m₂ + 1) (simpleHCutoff n₂).toNat) hg
    exact Units.ext ((hmem₁.1 ⟨g, hHD hg⟩ hcut).trans (hmem₂.1 ⟨g, hHD hg⟩ hcut).symm)
  have hK : H ≤ K := hH.symm ▸ sup_le hU hD
  apply DFunLike.ext
  intro g
  obtain ⟨x, hx, hval⟩ := hK g.2
  have h : x = g := Subtype.ext hval
  subst x
  exact hx

end Langlands.BushnellKutzko
