import Langlands.ClassFieldTheory.Local.TotalUnramifiedCompositumProof

/-! Actual restriction and arithmetic transport for the prime-break comparison. -/

noncomputable section

namespace Langlands.LocalClassField

open IntermediateField Langlands.Weil.Local

universe u v

theorem primeBreakResidueMap_surjective_of_total
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (h : E.canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier E.Carrier * F.canonicalTopologicalData.ramificationIndex) :
    Function.Surjective (PadicField.TopologicalData.relativeResidueMap
      F.canonicalTopologicalData E.canonicalTopologicalData) := by
  let f := IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier
  have hef := PadicField.ramificationIndex_mul_extensionResidueDegree F E f
  have ha : extensionAlgebra F E f = (inferInstance : Algebra F.Carrier E.Carrier) :=
    toAlgebra_algebraMap
  unfold extensionDegree at hef
  rw [ha, ← h] at hef
  have hr : extensionResidueDegree F E f = 1 :=
    Nat.eq_of_mul_eq_mul_left E.canonicalTopologicalData.ramificationIndex_pos
      (hef.trans (mul_one _).symm)
  let := E.canonicalTopologicalData.finite_residueField
  apply ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨(PadicField.TopologicalData.relativeResidueMap
      F.canonicalTopologicalData E.canonicalTopologicalData).injective, ?_⟩).2
  have hc := extensionResidueCardinality F E f
  rw [hr, pow_one] at hc
  exact hc.symm

section Restriction

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
  (E K M : IntermediateField k Ω) (hE : E ≤ M) (hK : K ≤ M)

def primeBreakRestriction [Normal k E] :
    letI : Algebra E M := (inclusion hE).toAlgebra
    letI : Algebra K M := (inclusion hK).toAlgebra
    letI : IsScalarTower k E M := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq' rfl
    Gal(M/K) →* Gal(E/k) := by
  let : Algebra E M := (inclusion hE).toAlgebra
  let : Algebra K M := (inclusion hK).toAlgebra
  let : IsScalarTower k E M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq' rfl
  exact (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom k)

theorem primeBreakRestriction_commutes [Normal k E] :
    letI : Algebra E M := (inclusion hE).toAlgebra
    letI : Algebra K M := (inclusion hK).toAlgebra
    ∀ (σ : Gal(M/K)) (z : E),
      inclusion hE (primeBreakRestriction E K M hE hK σ z) = σ (inclusion hE z) := by
  let : Algebra E M := (inclusion hE).toAlgebra
  let : Algebra K M := (inclusion hK).toAlgebra
  let : IsScalarTower k E M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq' rfl
  intro σ z
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars k) E z

theorem primeBreakRestriction_injective [Normal k E] (hM : M = E ⊔ K) :
    Function.Injective (primeBreakRestriction E K M hE hK) := by
  let : Algebra E M := (inclusion hE).toAlgebra
  let : Algebra K M := (inclusion hK).toAlgebra
  let : IsScalarTower k E M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq' rfl
  apply (injective_iff_map_eq_one _).mpr
  intro σ hσ
  have hs : E.restrict hE ⊔ K.restrict hK = ⊤ := by
    rw [← lift_inj, lift_sup, lift_top, lift_restrict, lift_restrict, hM]
  have hfix : σ.restrictScalars k ∈ (E.restrict hE ⊔ K.restrict hK).fixingSubgroup := by
    rw [fixingSubgroup_sup]
    constructor
    · intro x
      let z : E := ⟨x.val.val, (mem_restrict hE x.val).mp x.property⟩
      have hz := primeBreakRestriction_commutes E K M hE hK σ z
      rw [hσ] at hz
      exact hz.symm
    · intro x
      exact σ.commutes (⟨x.val.val, (mem_restrict hK x.val).mp x.property⟩ : K)
  rw [hs, fixingSubgroup_top] at hfix
  have he := Subgroup.mem_bot.mp hfix
  exact AlgEquiv.restrictScalars_injective k he

theorem primeBreakRestriction_displacement [Normal k E]
    (νE : E → ℤ) (νM : M → ℤ)
    (hord : ∀ z : E, νM (inclusion hE z) = νE z) :
    letI : Algebra K M := (inclusion hK).toAlgebra
    ∀ (σ : Gal(M/K)) (π : E) (n : ℤ),
      (σ (inclusion hE π) - inclusion hE π = 0 ∨
        n ≤ νM (σ (inclusion hE π) - inclusion hE π)) ↔
      (primeBreakRestriction E K M hE hK σ π - π = 0 ∨
        n ≤ νE (primeBreakRestriction E K M hE hK σ π - π)) := by
  let : Algebra K M := (inclusion hK).toAlgebra
  intro σ π n
  have hd : inclusion hE (primeBreakRestriction E K M hE hK σ π - π) =
      σ (inclusion hE π) - inclusion hE π := by
    rw [map_sub, primeBreakRestriction_commutes]
  rw [← hd, hord, map_eq_zero]

end Restriction

theorem primeBreakCompositumData
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E K' M : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier E.field]
    (htot : (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier E.field * F.canonicalTopologicalData.ramificationIndex)
    (hunr : (K'.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex)
    (hM : M.field = E.field ⊔ K'.field)
    (hE : E.field ≤ M.field) (hK : K'.field ≤ M.field) :
    letI := (E.asPadicField (p := p)).algebra
    letI := (K'.asPadicField (p := p)).algebra
    letI := (M.asPadicField (p := p)).algebra
    letI : Algebra E.field M.field := (inclusion hE).toAlgebra
    letI : Algebra K'.field M.field := (inclusion hK).toAlgebra
    letI : IsScalarTower (Padic p) E.field M.field :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (Padic p) K'.field M.field :=
      IsScalarTower.of_algebraMap_eq' rfl
    Function.Surjective (PadicField.TopologicalData.relativeResidueMap
      (K'.asPadicField (p := p)).canonicalTopologicalData
      (M.asPadicField (p := p)).canonicalTopologicalData) ∧
    ∀ z : E.field,
      (M.asPadicField (p := p)).canonicalTopologicalData.ord (inclusion hE z) =
        (E.asPadicField (p := p)).canonicalTopologicalData.ord z := by
  obtain ⟨_, M₀, hM₀, hE₀, hK₀, h₀⟩ := totalUnramifiedCompositum p F E K' htot hunr
  have heq : M₀ = M := Subtype.ext (hM₀.trans hM.symm)
  subst M₀
  exact ⟨h₀.2.2.2.1.2, h₀.2.2.2.2.1⟩

end Langlands.LocalClassField
