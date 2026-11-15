import Langlands.Geometry.Building.UnramifiedFiniteGaloisLevel
import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.GroupScheme.TraceCocycleDescent
import Langlands.GroupScheme.GaloisStableSubringTrace

/-! # Fixed points in stable cosets over `F^ur`

Valuations of integral elements of finite subextensions of `F^ur`, compatibility of a finite
Galois level with the Galois action, and the coset descent lemma
`exists_fixed_mul_of_unitSquare_scaling`: a cocycle of `Aut(F^ur/F)` with values in a stable
subgroup `B` with injective additive semilinear coordinates, whose image is stable under
multiplication by squares of units of valuation one, is a coboundary. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open Langlands.LocalGalois.Separable Langlands.GroupScheme
open scoped ValuativeRel

namespace Langlands.Geometry.Building.MaximalUnramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem valuation_inclusion_le_one {E : IntermediateField F (SeparableClosure F)}
    (hE : E ≤ inertiaFixedField F) (x : LocalUnramified.integers F E) :
    valuation F (IntermediateField.inclusion hE (x : E)) ≤ 1 := by
  have h1 : IsIntegral 𝒪[F] (x : E) := x.property
  have h2 : IsIntegral 𝒪[F] (IntermediateField.inclusion hE (x : E)) :=
    h1.map ((IntermediateField.inclusion hE).restrictScalars 𝒪[F])
  have h3 := (LocalUnramified.mem_integers_iff F (inertiaFixedField F) _).mp h2
  rw [← fixedFieldIntegers_eq] at h3
  exact (mem_valuationSubring_iff F _).mpr h3

/-- The image of a unit of the integer ring of `E ≤ F^ur` has valuation one in `F^ur`. -/
theorem valuation_inclusion_eq_one_of_isUnit {E : IntermediateField F (SeparableClosure F)}
    (hE : E ≤ inertiaFixedField F) {x : LocalUnramified.integers F E} (hx : IsUnit x) :
    valuation F (IntermediateField.inclusion hE (x : E)) = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 := valuation_inclusion_le_one hE (u : LocalUnramified.integers F E)
  have h2 := valuation_inclusion_le_one hE ((u⁻¹ : (LocalUnramified.integers F E)ˣ) :
    LocalUnramified.integers F E)
  have hmul : valuation F (IntermediateField.inclusion hE ((u : LocalUnramified.integers F E) : E)) *
      valuation F (IntermediateField.inclusion hE
        (((u⁻¹ : (LocalUnramified.integers F E)ˣ) : LocalUnramified.integers F E) : E)) = 1 := by
    rw [← map_mul, ← map_mul]
    have : ((u : LocalUnramified.integers F E) : E) *
        (((u⁻¹ : (LocalUnramified.integers F E)ˣ) : LocalUnramified.integers F E) : E) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    rw [this, map_one, map_one]
  by_contra hne
  have hlt := lt_of_le_of_ne h1 hne
  have : valuation F (IntermediateField.inclusion hE ((u : LocalUnramified.integers F E) : E)) *
      valuation F (IntermediateField.inclusion hE
        (((u⁻¹ : (LocalUnramified.integers F E)ˣ) : LocalUnramified.integers F E) : E)) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [hmul] at this
  exact lt_irrefl _ this

/-- On the integer ring of a Galois level `E`, the Galois action of `res σ` matches `σ` on
`F^ur`. -/
theorem GaloisLevel.inclusion_galoisAction {E₀ : IntermediateField F (inertiaFixedField F)}
    (L : GaloisLevel F E₀) (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (x : LocalUnramified.integers F L.E) :
    IntermediateField.inclusion L.le_inertiaFixedField
        ((LocalUnramified.galoisAction F L.E (L.res σ) x : LocalUnramified.integers F L.E) :
          L.E) =
      σ (IntermediateField.inclusion L.le_inertiaFixedField (x : L.E)) := by
  apply Subtype.ext
  rw [LocalUnramified.coe_galoisAction_apply]
  exact L.res_apply σ (IntermediateField.inclusion L.le_inertiaFixedField (x : L.E))
    (x : L.E).property

/-- An element of `F^ur` coming from a Galois level `E` is fixed by the kernel of the
restriction to `E`. -/
theorem GaloisLevel.inclusion_fixed {E₀ : IntermediateField F (inertiaFixedField F)}
    (L : GaloisLevel F E₀) (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hσ : L.res σ = 1) (x : L.E) :
    σ (IntermediateField.inclusion L.le_inertiaFixedField x) =
      IntermediateField.inclusion L.le_inertiaFixedField x := by
  apply Subtype.ext
  have h := L.res_apply σ (IntermediateField.inclusion L.le_inertiaFixedField x) x.property
  rw [hσ] at h
  exact h.symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Fixed points in stable cosets over `F^ur`.** Let `Aut(F^ur/F)` act on a group `P`, let
`B ≤ P` be a stable subgroup with an additive, injective, semilinear coordinate map
`e : B → (F^ur)^m`, and suppose `e(B)` is stable under multiplication by `c²` for every unit `c`
of `F^ur` of valuation one. If `w₀ ∈ P` is fixed by the automorphisms fixing a finite
subextension `E₀` and `w₀⁻¹ σ(w₀) ∈ B` for every `σ`, then some `w₀ b` with `b ∈ B` is fixed by
every `σ`. -/
theorem exists_fixed_mul_of_unitSquare_scaling {P : Type*} [Group P]
    (act : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →* MulAut P)
    (B : Subgroup P) (hB : ∀ σ, ∀ x ∈ B, act σ x ∈ B)
    {m : ℕ} (e : P → Fin m → inertiaFixedField F)
    (he_mul : ∀ x ∈ B, ∀ y ∈ B, e (x * y) = e x + e y)
    (he_inj : ∀ x ∈ B, e x = 0 → x = 1)
    (he_act : ∀ σ, ∀ x ∈ B, e (act σ x) = fun i => σ (e x i))
    (hsq : ∀ c : (inertiaFixedField F)ˣ, valuation F (c : inertiaFixedField F) = 1 →
      ∀ x ∈ B, ∃ y ∈ B, e y = (c : inertiaFixedField F) ^ 2 • e x)
    (E₀ : IntermediateField F (inertiaFixedField F)) [FiniteDimensional F E₀]
    (w₀ : P) (hw₀ : ∀ σ ∈ E₀.fixingSubgroup, act σ w₀ = w₀)
    (hw₀B : ∀ σ, w₀⁻¹ * act σ w₀ ∈ B) :
    ∃ b ∈ B, ∀ σ, act σ (w₀ * b) = w₀ * b := by
  classical
  obtain ⟨L⟩ := nonempty_galoisLevel F E₀
  let ι : LocalUnramified.integers F L.E →+* inertiaFixedField F :=
    (IntermediateField.inclusion L.le_inertiaFixedField).toRingHom.comp
      (LocalUnramified.integers F L.E).val.toRingHom
  have hι : ∀ x, ι x = IntermediateField.inclusion L.le_inertiaFixedField
      (x : L.E) := fun _ => rfl
  have he1 : e 1 = 0 := by
    have h := he_mul 1 B.one_mem 1 B.one_mem
    rw [mul_one] at h
    simpa using h
  have heinv : ∀ x ∈ B, e x⁻¹ = -e x := by
    intro x hx
    have h := he_mul x hx x⁻¹ (B.inv_mem hx)
    rw [mul_inv_cancel, he1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  let Pring : Subring (LocalUnramified.integers F L.E) :=
    { carrier := {l | ∀ x ∈ B, ∃ y ∈ B, e y = ι l • e x}
      mul_mem' := by
        intro a b ha hb x hx
        obtain ⟨y₁, hy₁, h₁⟩ := hb x hx
        obtain ⟨y₂, hy₂, h₂⟩ := ha y₁ hy₁
        exact ⟨y₂, hy₂, by rw [h₂, h₁, map_mul, mul_smul]⟩
      one_mem' := fun x hx => ⟨x, hx, by rw [map_one, one_smul]⟩
      add_mem' := by
        intro a b ha hb x hx
        obtain ⟨y₁, hy₁, h₁⟩ := ha x hx
        obtain ⟨y₂, hy₂, h₂⟩ := hb x hx
        exact ⟨y₁ * y₂, B.mul_mem hy₁ hy₂, by rw [he_mul _ hy₁ _ hy₂, h₁, h₂, map_add, add_smul]⟩
      zero_mem' := fun x hx => ⟨1, B.one_mem, by rw [he1, map_zero, zero_smul]⟩
      neg_mem' := by
        intro a ha x hx
        obtain ⟨y, hy, h⟩ := ha x hx
        exact ⟨y⁻¹, B.inv_mem hy, by rw [heinv y hy, h, map_neg, neg_smul]⟩ }
  have hmemP : ∀ l, l ∈ Pring ↔ ∀ x ∈ B, ∃ y ∈ B, e y = ι l • e x := fun _ => Iff.rfl
  have hιgal : ∀ σ x, ι (LocalUnramified.galoisAction F L.E (L.res σ) x) = σ (ι x) :=
    fun σ x => L.inclusion_galoisAction σ x
  have hP : ∀ (g : L.E ≃ₐ[F] L.E) (x : LocalUnramified.integers F L.E), x ∈ Pring →
      LocalUnramified.galoisAction F L.E g x ∈ Pring := by
    intro g l hl
    obtain ⟨σ, rfl⟩ := L.res_surjective g
    rw [hmemP] at hl ⊢
    intro x hx
    obtain ⟨y, hy, h⟩ := hl (act σ⁻¹ x) (hB _ _ hx)
    refine ⟨act σ y, hB _ _ hy, ?_⟩
    rw [he_act σ y hy, h, hιgal]
    have hx' : e (act σ (act σ⁻¹ x)) = fun i => σ (e (act σ⁻¹ x) i) := he_act σ _ (hB _ _ hx)
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at hx'
    rw [hx']
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  have hsqP : ∀ x : LocalUnramified.integers F L.E, IsUnit x → x ^ 2 ∈ Pring := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    let c : (inertiaFixedField F)ˣ := Units.map ι u
    have hc : valuation F (c : inertiaFixedField F) = 1 :=
      valuation_inclusion_eq_one_of_isUnit L.le_inertiaFixedField u.isUnit
    rw [hmemP]
    intro y hy
    obtain ⟨z, hz, h⟩ := hsq c hc y hy
    exact ⟨z, hz, by rw [h, map_pow]; rfl⟩
  obtain ⟨θ, hθP, hθsum⟩ := LocalUnramified.exists_trace_eq_one_of_sq_mem F L.E
    L.le_inertiaFixedField Pring hP hsqP
  let s := Function.surjInv L.res_surjective
  have hs : ∀ γ, L.res (s γ) = γ := Function.surjInv_eq L.res_surjective
  refine TraceCocycleDescent.exists_fixed_mul_of_trace_eq_one
    (L := inertiaFixedField F) (W := Fin m → inertiaFixedField F) ?_ act L.res s hs B hB e
    he_mul he_inj (fun σ x hx => he_act σ x hx) (ι θ) ?_ ?_ ?_ w₀ ?_ hw₀B
  · intro σ c w
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, AlgEquiv.smul_def, map_mul]
  · intro k hk
    exact L.inclusion_fixed k hk _
  · have h := congrArg ι hθsum
    rw [map_sum, map_one] at h
    rw [← h]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [AlgEquiv.smul_def, ← hιgal, hs]
  · intro σ x hx
    have hmem := hP (L.res σ) θ hθP
    rw [hmemP] at hmem
    obtain ⟨y, hy, h⟩ := hmem x hx
    exact ⟨y, hy, by rw [h, hιgal]; rfl⟩
  · intro k hk
    exact hw₀ k (L.ker_le_fixingSubgroup k hk)

end Langlands.Geometry.Building.MaximalUnramified
