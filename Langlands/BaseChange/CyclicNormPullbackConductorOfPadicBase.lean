import Langlands.BaseChange.PadicNormPullbackConductor
import Langlands.LocalField.SuppliedPadicExtension

/-! # The cyclic norm conductor formula from p-adic data on the base -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis LocalClassField LocalField
open scoped BigOperators

universe u v

/-- Only the base field needs to be presented as p-adic. The upper field uses
its supplied local-field and relative module topologies. -/
def CyclicNormPullbackConductorOfPadicBaseStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
      [IsNonarchimedeanLocalField E] [Algebra F.Carrier E] [IsModuleTopology F.Carrier E]
      (σ : E ≃ₐ[F.Carrier] E) (l : ℕ), IsCyclicAlgebra σ l →
      ∀ (χ : Quasicharacter F.Carrier) (η : Quasicharacter E),
        η.toMonoidHom = χ.toMonoidHom.comp (Units.map (Algebra.norm F.Carrier : E →* F.Carrier)) →
        ∀ f d : ℕ, IsResidueDegree F.Carrier E f → IsDifferentExponent F.Carrier E d →
        ∀ X : Finset (F.Carrierˣ →* ℂˣ), (∀ κ, κ ∈ X ↔ IsNormTrivial E κ) →
        ∃ a : (F.Carrierˣ →* ℂˣ) → ℕ,
          (∀ κ ∈ X, ∃ χκ : Quasicharacter F.Carrier,
            χκ.toMonoidHom = κ * χ.toMonoidHom ∧
            (LocalFieldData.ofInstances F.Carrier).multiplicativeConductor χκ = a κ) ∧
          ∑ κ ∈ X, a κ = f * ((LocalFieldData.ofInstances E).multiplicativeConductor η + d)

/-- Equip the upper field with the compatible p-adic structure and apply the
norm-pullback conductor theorem on the original field carriers. -/
theorem cyclicNormPullbackConductorOfPadicBase :
    CyclicNormPullbackConductorOfPadicBaseStatement.{u, v} := by
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro E _ _ _ _ _ _ σ l hcyc χ η hη f d hf hd X hX
  let : FiniteDimensional F.Carrier E := hcyc.1
  let : IsGalois F.Carrier E := hcyc.isGalois
  let : IsCyclic (E ≃ₐ[F.Carrier] E) := by
    refine isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨σ, ?_⟩
    rw [IsGalois.card_aut_eq_finrank, hcyc.2.1, hcyc.2.2.2.1]
  let : IsAbelianGalois F.Carrier E := IsAbelianGalois.of_isCyclic F.Carrier E
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F.Carrier)
  let : IsScalarTower (Padic p) F.Carrier E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F.Carrier E
  let P := PadicField.ofField (p := p) E
  have hcont : Continuous (algebraMap F.Carrier E) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F.Carrier E)
  let S : P.TopologicalData := suppliedPadicExtension T E hcont
  let : Algebra F.Carrier P.Carrier := (inferInstance : Algebra F.Carrier E)
  let : IsScalarTower (Padic p) F.Carrier P.Carrier :=
    (inferInstance : IsScalarTower (Padic p) F.Carrier E)
  let : IsAbelianGalois F.Carrier P.Carrier := (inferInstance : IsAbelianGalois F.Carrier E)
  let : TopologicalSpace P.Carrier := S.topology
  have hcomp : η = χ.comp (localNorm T S) :=
    ContinuousMonoidHom.ext fun a => DFunLike.congr_fun hη a
  subst η
  exact padicNormPullbackConductor p F P T S χ f d hf hd X hX

end Langlands.BaseChange
