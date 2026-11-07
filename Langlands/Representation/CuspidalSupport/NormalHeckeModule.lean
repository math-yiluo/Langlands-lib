import Langlands.Representation.CuspidalSupport.NormalHeckeTwist
import Langlands.Algebra.RankOneGradedAlgebra
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Module.CharacterModule

/-!
# The right action of `End(ind_H^G ρ)` on `Hom(ind_H^G ρ, B)`

For a smooth representation `B` of `G`, the endomorphisms of `I = ind_H^G ρ` act on the
maps `I → B` by `α · φ = α ≫ φ` ("first `α`, then `φ`"); `homAction` records this as an
anti-multiplicative linear map `End I → End_ℂ(Hom(I, B))`. If every nonzero map generates
`Hom(I, B)` and the space is finite-dimensional, this action is onto (Burnside,
`surjective_homAction`).

For a character `ω` trivial on `H` and a unit `v` with `α v = ω(g) (v α)` for every `α`
homogeneous of degree `p g`, the map `φ ↦ v ≫ Φ(φ)` is an equivariant bijection
`Hom(I, B ⊗ ω) ≃ Hom(I, B)` (`twistModuleEquiv`, `twistModuleEquiv_comp`). Conversely an
equivariant bijection forces `ω(g) = 1` whenever some element of degree `p g` acts as the
identity (`eq_one_of_homEquiv`).

The module also records the algebraic inputs: commutation scalars of a homogeneous element
form a character of the support (`exists_commutation_hom`), and characters with values in
`ℂˣ` extend from subgroups and separate points from subgroups
(`exists_addMonoidHom_extend`, `exists_addMonoidHom_ne_zero`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.RankOneGraded.IsRankOneGrading

variable {ι k R : Type*} [AddCommGroup ι] [DecidableEq ι] [Field k] [Ring R] [Algebra k R]
variable {𝒜 : ι → Submodule k R} [GradedAlgebra 𝒜] (h𝒜 : IsRankOneGrading 𝒜) [Nontrivial R]
include h𝒜

/-- Commuting a nonzero homogeneous element `v` past the pieces of the grading: on the piece
of each degree `a` of the support, `x v = β(a) (v x)` for a scalar `β(a)`, and `β` is a
character of the support. -/
theorem exists_commutation_hom {j : ι} {v : R} (hv : v ∈ 𝒜 j) (hv0 : v ≠ 0) :
    ∃ β : h𝒜.support →+ Additive kˣ, ∀ a : h𝒜.support, ∀ x ∈ 𝒜 (a : ι),
      x * v = ((Additive.toMul (β a) : kˣ) : k) • (v * x) := by
  have hsc : ∀ a : h𝒜.support, ∃ c : kˣ, ∀ x ∈ 𝒜 (a : ι), x * v = (c : k) • (v * x) := by
    intro a
    obtain ⟨x₀, hx₀, hx₀0⟩ := (h𝒜.mem_support_iff).mp a.2
    have h1 : v * x₀ ∈ 𝒜 ((a : ι) + j) := by
      rw [add_comm]
      exact SetLike.mul_mem_graded hv hx₀
    have h2 : x₀ * v ∈ 𝒜 ((a : ι) + j) := SetLike.mul_mem_graded hx₀ hv
    obtain ⟨c, hc⟩ := h𝒜.exists_smul_eq h1 (h𝒜.mul_ne_zero hv hv0 hx₀0) h2
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact h𝒜.mul_ne_zero hx₀ hx₀0 hv0 hc.symm
    refine ⟨Units.mk0 c hc0, fun x hx => ?_⟩
    obtain ⟨d, rfl⟩ := h𝒜.exists_smul_eq hx₀ hx₀0 hx
    rw [Units.val_mk0, smul_mul_assoc, ← hc, mul_smul_comm, smul_comm]
  choose c hc using hsc
  have hmul : ∀ a b : h𝒜.support, c (a + b) = c a * c b := by
    intro a b
    obtain ⟨x, hx, hx0⟩ := (h𝒜.mem_support_iff).mp a.2
    obtain ⟨y, hy, hy0⟩ := (h𝒜.mem_support_iff).mp b.2
    have hxy : x * y ∈ 𝒜 ((a + b : h𝒜.support) : ι) := SetLike.mul_mem_graded hx hy
    have h0 : v * (x * y) ≠ 0 := h𝒜.mul_ne_zero hv hv0 (h𝒜.mul_ne_zero hx hx0 hy0)
    have h2 : x * y * v = ((c a * c b : kˣ) : k) • (v * (x * y)) := by
      rw [mul_assoc, hc b y hy, mul_smul_comm, ← mul_assoc, hc a x hx, smul_mul_assoc,
        smul_smul, mul_assoc, Units.val_mul, mul_comm (c a : k)]
    rw [hc (a + b) (x * y) hxy] at h2
    exact Units.ext (smul_left_injective k h0 h2)
  exact ⟨AddMonoidHom.mk' (fun a => Additive.ofMul (c a)) fun a b => by
    rw [hmul]
    rfl, fun a x hx => hc a x hx⟩

end Langlands.RankOneGraded.IsRankOneGrading

namespace Langlands.CuspidalSupport.NormalHecke

section Units

/-- The group `ℂˣ` is divisible, hence an injective `ℤ`-module (Baer). -/
theorem baer_additive_units : Module.Baer ℤ (Additive ℂˣ) := by
  let : DivisibleBy (Additive ℂˣ) ℤ := divisibleByOfSMulRightSurj _ _ fun {n} hn z =>
    ⟨Additive.ofMul (Units.mk0 (Complex.exp (Complex.log ((Additive.toMul z : ℂˣ) : ℂ) / n))
      (Complex.exp_ne_zero _)), by
      apply Additive.toMul.injective
      apply Units.ext
      rw [toMul_zsmul, toMul_ofMul, Units.val_zpow_eq_zpow_val, Units.val_mk0,
        ← Complex.exp_int_mul, mul_div_cancel₀ _ (Int.cast_ne_zero.mpr hn),
        Complex.exp_log (Units.ne_zero _)]⟩
  exact Module.Baer.of_divisible _

/-- A character of a subgroup with values in `ℂˣ` extends to the whole group. -/
theorem exists_addMonoidHom_extend {ι : Type*} [AddCommGroup ι] (S : AddSubgroup ι)
    (β : S →+ Additive ℂˣ) : ∃ χ : ι →+ Additive ℂˣ, ∀ s : S, χ s = β s := by
  obtain ⟨χ, hχ⟩ := baer_additive_units.extension_property_addMonoidHom S.subtype
    Subtype.val_injective β
  exact ⟨χ, fun s => DFunLike.congr_fun hχ s⟩

/-- The character `q ↦ exp(2π i q)` of `ℚ / ℤ`. -/
def addCircleToUnits : AddCircle (1 : ℚ) →+ Additive ℂˣ :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ))
    (AddMonoidHom.mk' (fun q : ℚ => Additive.ofMul (Units.mk0
      (Complex.exp (2 * Real.pi * Complex.I * (q : ℂ))) (Complex.exp_ne_zero _))) fun a b => by
        apply Additive.toMul.injective
        apply Units.ext
        simp only [toMul_add, toMul_ofMul, Units.val_mul, Units.val_mk0, Rat.cast_add, mul_add,
          Complex.exp_add])
    (by
      rintro _ ⟨n, rfl⟩
      apply Additive.toMul.injective
      apply Units.ext
      simp only [AddMonoidHom.mk'_apply, zsmul_eq_mul, mul_one, Rat.cast_intCast, toMul_ofMul,
        Units.val_mk0, toMul_zero, Units.val_one]
      rw [mul_comm]
      exact Complex.exp_int_mul_two_pi_mul_I n)

theorem addCircleToUnits_ne_zero {y : AddCircle (1 : ℚ)} (hy : y ≠ 0) :
    addCircleToUnits y ≠ 0 := by
  induction y using QuotientAddGroup.induction_on with
  | H q =>
    intro h
    apply hy
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)) = 1 := by
      have := congrArg (fun z : Additive ℂˣ => ((Additive.toMul z : ℂˣ) : ℂ)) h
      simpa [addCircleToUnits] using this
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    have hq : (q : ℂ) = n := by
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      apply mul_left_cancel₀ h2
      rw [hn]
      ring
    have hq' : q = n := by exact_mod_cast hq
    rw [QuotientAddGroup.eq_zero_iff, hq']
    exact ⟨n, by simp⟩

/-- A point outside a subgroup is separated from it by a `ℂˣ`-valued character. -/
theorem exists_addMonoidHom_ne_zero {ι : Type*} [AddCommGroup ι] (S : AddSubgroup ι) {i : ι}
    (hi : i ∉ S) : ∃ χ : ι →+ Additive ℂˣ, (∀ s ∈ S, χ s = 0) ∧ χ i ≠ 0 := by
  have hne : (QuotientAddGroup.mk i : ι ⧸ S) ≠ 0 := by
    rwa [ne_eq, QuotientAddGroup.eq_zero_iff]
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  refine ⟨(addCircleToUnits.comp c).comp (QuotientAddGroup.mk' S), fun s hs => ?_,
    addCircleToUnits_ne_zero hc⟩
  change addCircleToUnits (c (QuotientAddGroup.mk s)) = 0
  rw [(QuotientAddGroup.eq_zero_iff s).mpr hs, map_zero, map_zero]

end Units

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (ρ : SmoothRep.{0, uG, uV} ℂ H) (hH : IsOpen (H : Set G))

section Action

variable (B : SmoothRep.{0, uG, max uG uV} ℂ G)

/-- The right action of `End(ind_H^G ρ)` on the maps `ind_H^G ρ → B`: `α` acts by
`φ ↦ α ≫ φ`. -/
def homAction : End (inducedRep H ρ) →ₗ[ℂ] Module.End ℂ (inducedRep H ρ ⟶ B) where
  toFun α := Linear.leftComp ℂ B α
  map_add' α β := LinearMap.ext fun φ => by
    rw [LinearMap.add_apply, Linear.leftComp_apply, Linear.leftComp_apply,
      Linear.leftComp_apply]
    exact Preadditive.add_comp _ _ _ α β φ
  map_smul' c α := LinearMap.ext fun φ => by
    rw [RingHom.id_apply, LinearMap.smul_apply, Linear.leftComp_apply, Linear.leftComp_apply]
    exact Linear.smul_comp _ _ _ c α φ

theorem homAction_apply (α : End (inducedRep H ρ)) (φ : inducedRep H ρ ⟶ B) :
    homAction H ρ B α φ = α ≫ φ :=
  rfl

theorem homAction_one : homAction H ρ B 1 = 1 :=
  LinearMap.ext fun φ => Category.id_comp φ

theorem homAction_mul (α β : End (inducedRep H ρ)) :
    homAction H ρ B (α * β) = homAction H ρ B β * homAction H ρ B α :=
  LinearMap.ext fun φ => Category.assoc β α φ

theorem isMulOrAntiMul_homAction : RankOneGraded.IsMulOrAntiMul (homAction H ρ B) :=
  Or.inr (homAction_mul H ρ B)

/-- **Burnside**: if `Hom(I, B)` is finite-dimensional and nonzero, and every nonzero map
generates it under the action of `End I`, then every linear endomorphism of `Hom(I, B)` is
the action of an endomorphism of `I`. -/
theorem surjective_homAction [FiniteDimensional ℂ (inducedRep H ρ ⟶ B)]
    [Nontrivial (inducedRep H ρ ⟶ B)]
    (hcyc : ∀ φ : inducedRep H ρ ⟶ B, φ ≠ 0 → ∀ ψ : inducedRep H ρ ⟶ B,
      ∃ α : End (inducedRep H ρ), α ≫ φ = ψ) :
    Function.Surjective (homAction H ρ B) := by
  intro f
  let : IsScalarTower ℂ (End (inducedRep H ρ))ᵐᵒᵖ (inducedRep H ρ ⟶ B) :=
    ⟨fun c a φ => Linear.smul_comp _ _ _ c a.unop φ⟩
  have : IsSimpleModule (End (inducedRep H ρ))ᵐᵒᵖ (inducedRep H ρ ⟶ B) :=
    isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, fun φ hφ ψ => by
      obtain ⟨α, hα⟩ := hcyc φ hφ ψ
      exact ⟨MulOpposite.op α, hα⟩⟩
  obtain ⟨a, ha⟩ := RankOneGraded.exists_forall_eq_smul_of_isSimpleModule
    (A := (End (inducedRep H ρ))ᵐᵒᵖ) f
  exact ⟨a.unop, LinearMap.ext fun φ => (ha φ).symm⟩

end Action

section Twist

variable {ι : Type*} [AddCommGroup ι] {p : G → ι}
variable {H} (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G)) (hωH : H ≤ ω.ker)
variable (B : SmoothRep.{0, uG, max uG uV} ℂ G)

omit [AddCommGroup ι] in
/-- An element of the piece of a degree that `p` does not take is zero. -/
theorem eq_zero_of_mem_component {a : ι} {α : End (inducedRep H ρ)}
    (hα : α ∈ component H ρ hH p a) (ha : ∀ g, p g ≠ a) : α = 0 :=
  end_ext H ρ hH fun g w => (congrArg (fun T : Module.End ℂ ρ => T w) (hα g (ha g))).trans rfl

/-- The equivariant bijection `φ ↦ v ≫ Φ(φ)`, for a unit `v` of `End(ind_H^G ρ)`. -/
def twistModuleEquiv (v : (End (inducedRep H ρ))ˣ) :
    (inducedRep H ρ ⟶ B.twist ω hω) ≃ₗ[ℂ] (inducedRep H ρ ⟶ B) where
  toFun φ := (v : End (inducedRep H ρ)) ≫ twistHomEquiv ρ hH ω hω hωH B φ
  map_add' φ ψ := by rw [map_add, Preadditive.comp_add]
  map_smul' c φ := by rw [map_smul, Linear.comp_smul, RingHom.id_apply]
  invFun ψ := (twistHomEquiv ρ hH ω hω hωH B).symm
    (((v⁻¹ : (End (inducedRep H ρ))ˣ) : End (inducedRep H ρ)) ≫ ψ)
  left_inv φ := by
    dsimp only
    rw [← Category.assoc, ← End.mul_def, Units.mul_inv, End.one_def, Category.id_comp,
      LinearEquiv.symm_apply_apply]
  right_inv ψ := by
    dsimp only
    rw [LinearEquiv.apply_symm_apply, ← Category.assoc, ← End.mul_def, Units.inv_mul,
      End.one_def, Category.id_comp]

theorem twistModuleEquiv_apply (v : (End (inducedRep H ρ))ˣ)
    (φ : inducedRep H ρ ⟶ B.twist ω hω) :
    twistModuleEquiv ρ hH ω hω hωH B v φ =
      (v : End (inducedRep H ρ)) ≫ twistHomEquiv ρ hH ω hω hωH B φ :=
  rfl

include hωH in
/-- An equivariant bijection `Hom(I, B ⊗ ω) ≃ Hom(I, B)` forces `ω(g) = 1` when some element
of degree `p g` acts as the identity on `Hom(I, B) ≠ 0`. -/
theorem eq_one_of_homEquiv (hp : IsDegree H p) [Nontrivial (inducedRep H ρ ⟶ B)]
    (Ψ : (inducedRep H ρ ⟶ B.twist ω hω) ≃ₗ[ℂ] (inducedRep H ρ ⟶ B))
    (hΨ : ∀ (α : End (inducedRep H ρ)) φ, Ψ (α ≫ φ) = α ≫ Ψ φ)
    {u : End (inducedRep H ρ)} {g : G} (hu : u ∈ component H ρ hH p (p g))
    (hu1 : ∀ φ : inducedRep H ρ ⟶ B, u ≫ φ = φ) : ω g = 1 := by
  obtain ⟨ψ, hψ⟩ := exists_ne (0 : inducedRep H ρ ⟶ B)
  set φ := Ψ.symm ψ with hφ
  have huφ : u ≫ φ = φ := Ψ.injective (by rw [hΨ, hφ, LinearEquiv.apply_symm_apply, hu1])
  have hΦ0 : twistHomEquiv ρ hH ω hω hωH B φ ≠ 0 := by
    rw [ne_eq, LinearEquiv.map_eq_zero_iff, hφ, LinearEquiv.map_eq_zero_iff]
    exact hψ
  have h := twistHomEquiv_comp hH hωH hp hu rfl φ
  rw [huφ, hu1] at h
  have h1 : (1 - (ω g : ℂ)⁻¹) • twistHomEquiv ρ hH ω hω hωH B φ = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  have h2 : (ω g : ℂ)⁻¹ = 1 := (sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hΦ0)).symm
  exact Units.ext (inv_eq_one.mp h2)

variable [hN : H.Normal] [ρ.representation.IsIrreducible]

/-- If `α v = ω(g) (v α)` for every `α` homogeneous of degree `p g`, then `φ ↦ v ≫ Φ(φ)`
commutes with the action of `End(ind_H^G ρ)`. -/
theorem twistModuleEquiv_comp (hp : IsDegree H p) (v : (End (inducedRep H ρ))ˣ)
    (hconj : ∀ (g : G) (α : End (inducedRep H ρ)), α ∈ component H ρ hH p (p g) →
      α * v = (ω g : ℂ) • ((v : End (inducedRep H ρ)) * α))
    (α : End (inducedRep H ρ)) (φ : inducedRep H ρ ⟶ B.twist ω hω) :
    twistModuleEquiv ρ hH ω hω hωH B v (α ≫ φ) = α ≫ twistModuleEquiv ρ hH ω hω hωH B v φ := by
  let S : Submodule ℂ (End (inducedRep H ρ)) :=
    { carrier := {α | ∀ φ, twistModuleEquiv ρ hH ω hω hωH B v (α ≫ φ) =
        α ≫ twistModuleEquiv ρ hH ω hω hωH B v φ}
      add_mem' := fun {α β} hα hβ φ => by
        rw [Preadditive.add_comp, map_add, hα, hβ, Preadditive.add_comp]
      zero_mem' := fun φ => by rw [Limits.zero_comp, map_zero, Limits.zero_comp]
      smul_mem' := fun c α hα φ => by
        rw [Linear.smul_comp, map_smul, hα, Linear.smul_comp] }
  have hS : ∀ a, component H ρ hH p a ≤ S := by
    intro a α hα φ
    by_cases ha : ∃ g, p g = a
    · obtain ⟨g, rfl⟩ := ha
      have hω0 : (ω g : ℂ) ≠ 0 := Units.ne_zero _
      rw [twistModuleEquiv_apply, twistModuleEquiv_apply,
        twistHomEquiv_comp hH hωH hp hα rfl φ, Linear.comp_smul, ← Category.assoc,
        ← End.mul_def, hconj g α hα, Linear.smul_comp, smul_smul, inv_mul_cancel₀ hω0,
        one_smul, End.mul_def, Category.assoc]
    · push Not at ha
      rw [eq_zero_of_mem_component ρ hH hα ha, Limits.zero_comp, map_zero, Limits.zero_comp]
  have htop : S = ⊤ := top_unique ((iSup_component ρ hH hp).symm.le.trans (iSup_le hS))
  have hα : α ∈ S := htop ▸ Submodule.mem_top
  exact hα φ

end Twist

end Langlands.CuspidalSupport.NormalHecke
