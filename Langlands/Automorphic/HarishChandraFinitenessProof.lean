import Langlands.Automorphic.LeviSliceFiniteness
import Langlands.Automorphic.TwoBlockConstantTermAutomorphic
import Langlands.Automorphic.TwoBlockConstantTermCenterTransfer
import Langlands.Global.AdeleQuotientCompactProof

/-! # Adelic Harish-Chandra finiteness by rank induction -/

noncomputable section
universe u v w
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F]

local instance rankInductionRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance rankInductionContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance rankInductionFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance rankInductionFormGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _

private abbrev FinitenessAtRank (n : ℕ) : Prop :=
  ∀ (J : Ideal (EnvelopingCenter F n)),
    Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ) →
    ∀ (L : OpenSubgroup (FiniteAdelicGL F n)) (m : ℕ)
      (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)),
        FiniteDimensional ℂ (annihilatedFormMultiplicitySpace F n J L.toSubgroup σ)

private def HasUniformSliceLifts (n : ℕ) {m : ℕ} {V : Type v} {Y : Type w}
    (s : V → Y → (Fin m → ℂ) →ₗ[ℂ] (AdelicGL F n → ℂ)) : Prop :=
  ∃ (J : Ideal (EnvelopingCenter F n)) (L : OpenSubgroup (FiniteAdelicGL F n))
    (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)),
      Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ) ∧
        ∀ v y, ∃ ψ : annihilatedFormMultiplicitySpace F n J L.toSubgroup σ,
          ∀ x g, automorphicFormValues F n (ψ.val x) g = s v y x g

private theorem finite_slice_bound (n : ℕ) {m : ℕ} {V : Type v} {Y : Type w}
    (s : V → Y → (Fin m → ℂ) →ₗ[ℂ] (AdelicGL F n → ℂ))
    (h : HasUniformSliceLifts F n s) (ih : FinitenessAtRank F n) :
    ∃ A : Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] (AdelicGL F n → ℂ)),
      Module.Finite ℂ A ∧ ∀ v y, s v y ∈ A := by
  obtain ⟨J, L, σ, hJ, hs⟩ := h
  let E := annihilatedFormMultiplicitySpace F n J L.toSubgroup σ
  let e : ((Fin m → ℂ) →ₗ[ℂ] AutomorphicForms F n) →ₗ[ℂ]
      ((Fin m → ℂ) →ₗ[ℂ] (AdelicGL F n → ℂ)) :=
    LinearMap.llcomp ℂ (Fin m → ℂ) (AutomorphicForms F n) (AdelicGL F n → ℂ)
      (automorphicFormValues F n)
  have : Module.Finite ℂ E := ih J hJ L m σ
  refine ⟨E.map e, Module.Finite.map _ _, fun v y => ?_⟩
  obtain ⟨ψ, hψ⟩ := hs v y
  exact ⟨ψ.val, ψ.property, LinearMap.ext fun x => funext (hψ x)⟩

variable [CompactSpace (AdeleQuotient F)]

private def HasUniformConstantTermSliceLifts : Prop :=
  ∀ (n : ℕ) (J : Ideal (EnvelopingCenter F n)),
    Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ) →
    ∀ (L : OpenSubgroup (FiniteAdelicGL F n)) (m : ℕ)
      (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ))
      (p : MaximalBlockCut n) (d : FiniteAdelicGL F n),
      let V := annihilatedFormMultiplicitySpace F n J L.toSubgroup σ
      HasUniformSliceLifts F p.val.1
        (fun (φ : V) y => firstFunctionSlice y ((blockConstantTermAt F n p.property.1 d).comp φ.val)) ∧
      HasUniformSliceLifts F p.val.2
        (fun (φ : V) x => secondFunctionSlice x ((blockConstantTermAt F n p.property.1 d).comp φ.val))

private theorem uniformConstantTermSliceLifts : HasUniformConstantTermSliceLifts F := by
  intro n J hJ L m σ p d
  obtain ⟨I₁, hI₁, h₁⟩ := exists_firstBlock_cofinite_center_ideal F p.property.1 J hJ
  obtain ⟨I₂, hI₂, h₂⟩ := exists_secondBlock_cofinite_center_ideal F p.property.1 J hJ
  refine ⟨⟨I₁, firstBlockConstantTermLevel F p.property.1 L d,
    σ.comp (firstBlockInfiniteCompact F p.property.1), hI₁, ?_⟩,
    ⟨I₂, secondBlockConstantTermLevel F p.property.1 L d,
    σ.comp (secondBlockInfiniteCompact F p.property.1), hI₂, ?_⟩⟩
  · intro φ y
    let ψ := firstBlockConstantTermMultiplicityLift F p.property.1 J L σ I₁ hI₁ h₁ d φ y
    exact ⟨ψ.val, fun v x => ψ.property v x⟩
  · intro φ x
    let ψ := secondBlockConstantTermMultiplicityLift F p.property.1 J L σ I₂ hI₂ h₂ d φ x
    exact ⟨ψ.val, fun v y => ψ.property v y⟩

set_option maxHeartbeats 600000 in
private theorem finitenessAtRank (n : ℕ) : FinitenessAtRank F n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J hJ L m σ
    apply finiteDimensional_annihilatedFormMultiplicitySpace_of_slices F n J L σ hJ
    intro p d
    have h₁ : p.val.1 < n := by have := p.property.1; have := p.property.2.2; omega
    have h₂ : p.val.2 < n := by have := p.property.1; have := p.property.2.1; omega
    obtain ⟨ha, hb⟩ := uniformConstantTermSliceLifts F n J hJ L m σ p d
    obtain ⟨A, hA, hsa⟩ := finite_slice_bound F p.val.1 _ ha (ih p.val.1 h₁)
    obtain ⟨B, hB, hsb⟩ := finite_slice_bound F p.val.2 _ hb (ih p.val.2 h₂)
    exact ⟨A, B, hA, hB, fun φ => (mem_separateSliceSubmodule A B _).mpr ⟨hsa φ, hsb φ⟩⟩

omit [CompactSpace (AdeleQuotient F)] in
/-- Harish-Chandra finiteness for actual automorphic forms on the adelic general linear group. -/
theorem harishChandraFiniteness : HarishChandraFinitenessStatement.{u} := by
  intro K _ _ n
  let : CompactSpace (AdeleQuotient K) := compactSpace_adeleQuotient K
  exact finitenessAtRank K n

end Langlands.Automorphic
