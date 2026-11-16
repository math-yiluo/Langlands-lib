/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U005.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U007.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U010.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U016.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U066.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U068.Proofs
import Mathlib.Tactic.FieldSimp

/-!
# NYLL M118.005: multiplicativity of the Herbrand quotient

Modified by Worker 749, 16 November 2026: prove the published target
`herbrandQuotient_exact_multiplicativeStatement` (M118.005) by the source
proof of `herbrandQuotient_exact_multiplicative` in
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type and
begin the proof with `show` stating it unfolded. The source proof applies
M117.021 `herbrand_exact_cardinality_identity` of
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`,
whose proof is not in the Library; the port proves it, with its source
statement, as the private theorem `herbrand_exact_cardinality_identity_aux`,
by a new exact-hexagon proof written for this port (not the source proof),
with private helper declarations, in a section with the source variable line
`variable {G A B C : Type}` of `Cardinality.lean`. These use the published
M113.005, M113.007, M113.010, M113.016, M113.066 and M113.068 proofs, which
the module imports. Replace the source imports by the published statement
module, these published proof modules and `Mathlib.Tactic.FieldSimp` (for
the source proof's `field_simp`, which the published modules do not bring
into scope), and omit the source universe and
variable lines (the theorem binds its own) and the rest of the source file.
See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

section Hexagon

variable {G A B C : Type}

/-! ### Cardinality of a cyclic exact sequence of six finite groups -/

/-- The homomorphism `X →* Y` induced by `ψ : P →* Y` along a surjection
`p : P →* X` whose kernel lies in the kernel of `ψ`. -/
private def hexagonLift {P X Y : Type} [Group P] [Group X] [Group Y] (p : P →* X)
    (hp : Function.Surjective p) (ψ : P →* Y) (h : p.ker ≤ ψ.ker) : X →* Y :=
  (QuotientGroup.lift p.ker ψ h).comp
    (QuotientGroup.quotientKerEquivOfSurjective p hp).symm.toMonoidHom

private theorem hexagonLift_apply {P X Y : Type} [Group P] [Group X] [Group Y]
    (p : P →* X) (hp : Function.Surjective p) (ψ : P →* Y) (h : p.ker ≤ ψ.ker) (x : P) :
    hexagonLift p hp ψ h (p x) = ψ x := by
  have hx : (QuotientGroup.quotientKerEquivOfSurjective p hp).symm (p x) =
      (x : P ⧸ p.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show QuotientGroup.lift p.ker ψ h
      ((QuotientGroup.quotientKerEquivOfSurjective p hp).symm (p x)) = ψ x
  rw [hx]
  rfl

/-- The `→` half of an exactness criterion at `p' y`, applied to `y ∈ ker p'`,
shows that `ψ'` descends along `p'`. -/
private theorem hexagon_ker_le_ker {P P' Y Z : Type} [Group P] [Group P'] [Group Y]
    [Group Z] (ψ : P →* Y) (p' : P' →* Y) (ψ' : P' →* Z)
    (H : ∀ y : P', (∃ z : P, ψ z = p' y) ↔ ψ' y = 1) : p'.ker ≤ ψ'.ker := by
  intro y hy
  rw [MonoidHom.mem_ker] at hy ⊢
  exact (H y).1 ⟨1, by rw [map_one, hy]⟩

/-- Element-level exactness criterion for two consecutive induced maps. -/
private theorem range_hexagonLift_eq_ker {P P' X Y Z : Type} [Group P] [Group P']
    [Group X] [Group Y] [Group Z]
    (p : P →* X) (hp : Function.Surjective p) (ψ : P →* Y) (h : p.ker ≤ ψ.ker)
    (p' : P' →* Y) (hp' : Function.Surjective p') (ψ' : P' →* Z) (h' : p'.ker ≤ ψ'.ker)
    (H : ∀ y : P', (∃ z : P, ψ z = p' y) ↔ ψ' y = 1) :
    (hexagonLift p hp ψ h).range = (hexagonLift p' hp' ψ' h').ker := by
  ext x
  obtain ⟨y, rfl⟩ := hp' x
  rw [MonoidHom.mem_range, MonoidHom.mem_ker, hexagonLift_apply, ← H]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := hp w
    exact ⟨z, by rwa [hexagonLift_apply] at hw⟩
  · rintro ⟨z, hz⟩
    exact ⟨p z, by rw [hexagonLift_apply, hz]⟩

/-- In a cyclic exact sequence of six finite groups, the products of the
cardinalities of alternate terms agree. -/
private theorem card_hexagon {X₁ X₂ X₃ X₄ X₅ X₆ : Type} [Group X₁] [Group X₂] [Group X₃]
    [Group X₄] [Group X₅] [Group X₆] [Finite X₁] [Finite X₂] [Finite X₃] [Finite X₄]
    [Finite X₅] [Finite X₆]
    (f₁ : X₁ →* X₂) (f₂ : X₂ →* X₃) (f₃ : X₃ →* X₄) (f₄ : X₄ →* X₅) (f₅ : X₅ →* X₆)
    (f₆ : X₆ →* X₁)
    (h₁ : f₁.range = f₂.ker) (h₂ : f₂.range = f₃.ker) (h₃ : f₃.range = f₄.ker)
    (h₄ : f₄.range = f₅.ker) (h₅ : f₅.range = f₆.ker) (h₆ : f₆.range = f₁.ker) :
    Nat.card X₂ * Nat.card X₄ * Nat.card X₆ =
      Nat.card X₁ * Nat.card X₃ * Nat.card X₅ := by
  have e₁ := monoidHom_card_eq_card_range_mul_card_range_of_exact f₆ f₁ h₆
  have e₂ := monoidHom_card_eq_card_range_mul_card_range_of_exact f₁ f₂ h₁
  have e₃ := monoidHom_card_eq_card_range_mul_card_range_of_exact f₂ f₃ h₂
  have e₄ := monoidHom_card_eq_card_range_mul_card_range_of_exact f₃ f₄ h₃
  have e₅ := monoidHom_card_eq_card_range_mul_card_range_of_exact f₄ f₅ h₄
  have e₆ := monoidHom_card_eq_card_range_mul_card_range_of_exact f₅ f₆ h₅
  rw [e₁, e₂, e₃, e₄, e₅, e₆]
  ac_rfl

/-- The hexagon cardinality identity for six maps `Xₖ → Xₖ₊₁` (indices mod 6),
each induced by `ψₖ : Pₖ →* Xₖ₊₁` along a surjection `pₖ : Pₖ →* Xₖ`, from an
element-level exactness criterion at each term. -/
private theorem card_hexagon_of_exact_iff
    {P₁ P₂ P₃ P₄ P₅ P₆ X₁ X₂ X₃ X₄ X₅ X₆ : Type}
    [Group P₁] [Group P₂] [Group P₃] [Group P₄] [Group P₅] [Group P₆]
    [Group X₁] [Group X₂] [Group X₃] [Group X₄] [Group X₅] [Group X₆]
    [Finite X₁] [Finite X₂] [Finite X₃] [Finite X₄] [Finite X₅] [Finite X₆]
    (p₁ : P₁ →* X₁) (p₂ : P₂ →* X₂) (p₃ : P₃ →* X₃) (p₄ : P₄ →* X₄) (p₅ : P₅ →* X₅)
    (p₆ : P₆ →* X₆)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂)
    (hp₃ : Function.Surjective p₃) (hp₄ : Function.Surjective p₄)
    (hp₅ : Function.Surjective p₅) (hp₆ : Function.Surjective p₆)
    (ψ₁ : P₁ →* X₂) (ψ₂ : P₂ →* X₃) (ψ₃ : P₃ →* X₄) (ψ₄ : P₄ →* X₅) (ψ₅ : P₅ →* X₆)
    (ψ₆ : P₆ →* X₁)
    (H₁ : ∀ y : P₂, (∃ z : P₁, ψ₁ z = p₂ y) ↔ ψ₂ y = 1)
    (H₂ : ∀ y : P₃, (∃ z : P₂, ψ₂ z = p₃ y) ↔ ψ₃ y = 1)
    (H₃ : ∀ y : P₄, (∃ z : P₃, ψ₃ z = p₄ y) ↔ ψ₄ y = 1)
    (H₄ : ∀ y : P₅, (∃ z : P₄, ψ₄ z = p₅ y) ↔ ψ₅ y = 1)
    (H₅ : ∀ y : P₆, (∃ z : P₅, ψ₅ z = p₆ y) ↔ ψ₆ y = 1)
    (H₆ : ∀ y : P₁, (∃ z : P₆, ψ₆ z = p₁ y) ↔ ψ₁ y = 1) :
    Nat.card X₂ * Nat.card X₄ * Nat.card X₆ =
      Nat.card X₁ * Nat.card X₃ * Nat.card X₅ := by
  have k₁ := hexagon_ker_le_ker ψ₆ p₁ ψ₁ H₆
  have k₂ := hexagon_ker_le_ker ψ₁ p₂ ψ₂ H₁
  have k₃ := hexagon_ker_le_ker ψ₂ p₃ ψ₃ H₂
  have k₄ := hexagon_ker_le_ker ψ₃ p₄ ψ₄ H₃
  have k₅ := hexagon_ker_le_ker ψ₄ p₅ ψ₅ H₄
  have k₆ := hexagon_ker_le_ker ψ₅ p₆ ψ₆ H₅
  exact card_hexagon
    (hexagonLift p₁ hp₁ ψ₁ k₁) (hexagonLift p₂ hp₂ ψ₂ k₂) (hexagonLift p₃ hp₃ ψ₃ k₃)
    (hexagonLift p₄ hp₄ ψ₄ k₄) (hexagonLift p₅ hp₅ ψ₅ k₅) (hexagonLift p₆ hp₆ ψ₆ k₆)
    (range_hexagonLift_eq_ker p₁ hp₁ ψ₁ k₁ p₂ hp₂ ψ₂ k₂ H₁)
    (range_hexagonLift_eq_ker p₂ hp₂ ψ₂ k₂ p₃ hp₃ ψ₃ k₃ H₂)
    (range_hexagonLift_eq_ker p₃ hp₃ ψ₃ k₃ p₄ hp₄ ψ₄ k₄ H₃)
    (range_hexagonLift_eq_ker p₄ hp₄ ψ₄ k₄ p₅ hp₅ ψ₅ k₅ H₄)
    (range_hexagonLift_eq_ker p₅ hp₅ ψ₅ k₅ p₆ hp₆ ψ₆ k₆ H₅)
    (range_hexagonLift_eq_ker p₆ hp₆ ψ₆ k₆ p₁ hp₁ ψ₁ k₁ H₆)

/-! ### Quotients `Z / R` and auxiliary homomorphisms -/

/-- The projection `Z → Z / R` for subgroups `Z` and `R` of a commutative group. -/
private def hexagonMk {X : Type} [CommGroup X] (Z R : Subgroup X) :
    Z →* Z ⧸ R.subgroupOf Z :=
  QuotientGroup.mk' _

private theorem hexagonMk_eq_iff {X : Type} [CommGroup X] (Z R : Subgroup X) (x y : Z) :
    hexagonMk Z R x = hexagonMk Z R y ↔ (x : X)⁻¹ * y ∈ R := by
  show (x : Z ⧸ R.subgroupOf Z) = y ↔ _
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

private theorem hexagonMk_eq_one_iff {X : Type} [CommGroup X] (Z R : Subgroup X) (x : Z) :
    hexagonMk Z R x = 1 ↔ (x : X) ∈ R := by
  show (x : Z ⧸ R.subgroupOf Z) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

private theorem hexagonMk_surjective {X : Type} [CommGroup X] (Z R : Subgroup X) :
    Function.Surjective (hexagonMk Z R) :=
  QuotientGroup.mk'_surjective _

/-- A homomorphism mapping `S` into `T` restricts to `S →* T`. -/
private theorem exists_hexagon_restrict {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (S : Subgroup X) (T : Subgroup Y) (h : ∀ x ∈ S, f x ∈ T) :
    ∃ g : S →* T, ∀ x : S, (g x : Y) = f x :=
  ⟨(f.comp S.subtype).codRestrict T (fun x => h x x.2), fun _ => rfl⟩

/-- A surjective homomorphism restricts to a surjection from the preimage of `T`
onto `T`. -/
private theorem exists_hexagon_comap {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (T : Subgroup Y) :
    ∃ g : T.comap f →* T, (∀ x : T.comap f, (g x : Y) = f x) ∧ Function.Surjective g :=
  ⟨f.subgroupComap T, fun _ => rfl, f.subgroupComap_surjective T hf⟩

/-- A homomorphism `φ` with values in the range of an injective `i` factors
through `i`, with values in any subgroup `K` containing the preimages. -/
private theorem exists_hexagon_lift_of_range {P X Y : Type} [Group P] [Group X] [Group Y]
    (i : X →* Y) (hinj : Function.Injective i) (φ : P →* Y) (h : ∀ x, φ x ∈ i.range)
    (K : Subgroup X) (hK : ∀ x a, i a = φ x → a ∈ K) :
    ∃ f : P →* K, ∀ x : P, i (f x) = φ x := by
  let f₀ : P →* X :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (φ.codRestrict i.range h)
  have hf₀ : ∀ x, i (f₀ x) = φ x := by
    intro x
    show i ((MonoidHom.ofInjective hinj).symm (φ.codRestrict i.range h x)) = φ x
    rw [← MonoidHom.ofInjective_apply hinj, MulEquiv.apply_symm_apply]
    rfl
  exact ⟨f₀.codRestrict K (fun x => hK x _ (hf₀ x)), hf₀⟩

/-! ### Exactness of the hexagon

Each of the three lemmas below is stated for endomorphisms `u` and `v` of `A`,
`B` and `C` commuting with `i` and `j`; the hexagon uses them for
`(u, v) = (N_G, σ - 1)` and for `(u, v) = (σ - 1, N_G)`. -/

section Exactness

variable [CommGroup A] [CommGroup B] [CommGroup C]

/-- Exactness at the middle of `ker v_A / im u_A → ker v_B / im u_B →
ker v_C / im u_C`. -/
private theorem hexagon_exact_middle (i : A →* B) (j : B →* C)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b) (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (vA : A →* A) (uB vB : B →* B) (uC : C →* C)
    (hiv : ∀ a : A, i (vA a) = vB (i a)) (hju : ∀ b : B, j (uB b) = uC (j b))
    (hvu : ∀ b : B, vB (uB b) = 1)
    (ZA : Subgroup A) (hZA : ∀ a : A, a ∈ ZA ↔ vA a = 1) (y : B) (hy : vB y = 1) :
    (∃ z : ZA, (i z)⁻¹ * y ∈ uB.range) ↔ j y ∈ uC.range := by
  constructor
  · rintro ⟨z, b, hb⟩
    refine MonoidHom.mem_range.2 ⟨j b, ?_⟩
    rw [← hju, hb, map_mul, map_inv, (hker (i z)).2 ⟨z, rfl⟩, inv_one, one_mul]
  · rintro ⟨c, hc⟩
    obtain ⟨b, rfl⟩ := hsurj c
    obtain ⟨a, ha⟩ := (hker (y * (uB b)⁻¹)).1
      (by rw [map_mul, map_inv, hju, hc, mul_inv_cancel])
    refine ⟨⟨a, (hZA a).2 (hinj ?_)⟩, MonoidHom.mem_range.2 ⟨b, ?_⟩⟩
    · rw [hiv, ha, map_mul, map_inv, hy, hvu, inv_one, mul_one, map_one]
    · show uB b = (i a)⁻¹ * y
      rw [ha, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]

/-- Exactness at `ker v_C / im u_C` of `ker v_B / im u_B → ker v_C / im u_C →
ker u_A / im v_A`, the second map sending the class of `j y` to the class of
the element `d` with `i d = v_B y`. -/
private theorem hexagon_exact_connecting (i : A →* B) (j : B →* C)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b) (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (vA : A →* A) (uB vB : B →* B) (uC : C →* C)
    (hiv : ∀ a : A, i (vA a) = vB (i a)) (hju : ∀ b : B, j (uB b) = uC (j b))
    (hvu : ∀ b : B, vB (uB b) = 1)
    (ZB : Subgroup B) (hZB : ∀ b : B, b ∈ ZB ↔ vB b = 1) (y : B) (d : A)
    (hd : i d = vB y) :
    (∃ z : ZB, (j z)⁻¹ * j y ∈ uC.range) ↔ d ∈ vA.range := by
  constructor
  · rintro ⟨z, c, hc⟩
    obtain ⟨b, rfl⟩ := hsurj c
    obtain ⟨a, ha⟩ := (hker (((z : B) * uB b)⁻¹ * y)).1
      (by rw [map_mul, map_inv, map_mul, hju, hc, mul_inv_cancel_left, inv_mul_cancel])
    refine MonoidHom.mem_range.2 ⟨a, hinj ?_⟩
    rw [hiv, hd, ha, map_mul, map_inv, map_mul, (hZB z).1 z.2, hvu, one_mul, inv_one,
      one_mul]
  · rintro ⟨a, rfl⟩
    refine ⟨⟨y * (i a)⁻¹, (hZB _).2 ?_⟩, MonoidHom.mem_range.2 ⟨1, ?_⟩⟩
    · rw [map_mul, map_inv, ← hiv, hd, mul_inv_cancel]
    · show uC 1 = (j (y * (i a)⁻¹))⁻¹ * j y
      rw [map_one, map_mul, map_inv, (hker (i a)).2 ⟨a, rfl⟩, inv_one, mul_one,
        inv_mul_cancel]

/-- Exactness at `ker u_A / im v_A` of `ker v_C / im u_C → ker u_A / im v_A →
ker u_B / im v_B`, where `δ z` is the element with `i (δ z) = v_B z` for `z` in
the preimage `P` of `ker v_C`. -/
private theorem hexagon_exact_after_connecting (i : A →* B) (j : B →* C)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b) (hinj : Function.Injective i)
    (vA : A →* A) (vB : B →* B) (vC : C →* C)
    (hiv : ∀ a : A, i (vA a) = vB (i a)) (hjv : ∀ b : B, j (vB b) = vC (j b))
    (P : Subgroup B) (hP : ∀ b : B, b ∈ P ↔ vC (j b) = 1) (δ : P → A)
    (hδ : ∀ z : P, i (δ z) = vB z) (y : A) :
    (∃ z : P, (δ z)⁻¹ * y ∈ vA.range) ↔ i y ∈ vB.range := by
  constructor
  · rintro ⟨z, a, ha⟩
    refine MonoidHom.mem_range.2 ⟨z * i a, ?_⟩
    rw [map_mul, ← hiv, ha, map_mul, map_inv, hδ, mul_inv_cancel_left]
  · rintro ⟨b, hb⟩
    have hbP : b ∈ P := (hP b).2 (by rw [← hjv, hb, (hker (i y)).2 ⟨y, rfl⟩])
    have hδb : δ ⟨b, hbP⟩ = y := hinj (by rw [hδ]; exact hb)
    exact ⟨⟨b, hbP⟩, MonoidHom.mem_range.2 ⟨1, by rw [hδb, map_one, inv_mul_cancel]⟩⟩

end Exactness

/-- For a generator `σ`, the fixed subgroup is the kernel of `σ - 1`. -/
private theorem mem_fixedSubgroup_iff_hexagon [Group G] {X : Type} [CommGroup X]
    [MulDistribMulAction G X] {σ : G} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (x : X) :
    x ∈ fixedSubgroup G X ↔ sigmaMinusOneHom (G := G) (A := X) σ x = 1 := by
  constructor
  · intro hx
    have hx' : ∀ g : G, g • x = x := hx
    show σ • x * x⁻¹ = 1
    rw [hx' σ, mul_inv_cancel]
  · intro hx
    exact fixed_of_forall_mem_zpowers_of_sigmaMinusOne_eq_one (G := G) (A := X) (σ := σ)
      hgen hx

/-- The source theorem M117.021 `herbrand_exact_cardinality_identity`, with its
source statement, proved by the exact hexagon under a private name. -/
private theorem herbrand_exact_cardinality_identity_aux
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    Nat.card (HerbrandH0 G B) *
        Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (HerbrandHMinusOne G C σ) =
      Nat.card (HerbrandH0 G A) *
        Nat.card (HerbrandH0 G C) *
        Nat.card (HerbrandHMinusOne G B σ) := by
  -- The norm `N_G` and `σ - 1` commute with `i` and `j` and compose to `1`.
  have hiN : ∀ a : A, i (tateNormHom (G := G) (A := A) a) =
      tateNormHom (G := G) (A := B) (i a) :=
    fun a => map_tateNorm (G := G) i hi a
  have hjN : ∀ b : B, j (tateNormHom (G := G) (A := B) b) =
      tateNormHom (G := G) (A := C) (j b) :=
    fun b => map_tateNorm (G := G) j hj b
  have hiS : ∀ a : A, i (sigmaMinusOneHom (G := G) (A := A) σ a) =
      sigmaMinusOneHom (G := G) (A := B) σ (i a) :=
    fun a => map_sigmaMinusOne (G := G) i hi σ a
  have hjS : ∀ b : B, j (sigmaMinusOneHom (G := G) (A := B) σ b) =
      sigmaMinusOneHom (G := G) (A := C) σ (j b) :=
    fun b => map_sigmaMinusOne (G := G) j hj σ b
  have hFA := mem_fixedSubgroup_iff_hexagon (G := G) (X := A) hgen
  have hFB := mem_fixedSubgroup_iff_hexagon (G := G) (X := B) hgen
  have hFC := mem_fixedSubgroup_iff_hexagon (G := G) (X := C) hgen
  have hKA : ∀ a : A, a ∈ normKernelSubgroup G A ↔ tateNormHom (G := G) (A := A) a = 1 :=
    fun _ => MonoidHom.mem_ker
  have hKB : ∀ b : B, b ∈ normKernelSubgroup G B ↔ tateNormHom (G := G) (A := B) b = 1 :=
    fun _ => MonoidHom.mem_ker
  have hKC : ∀ c : C, c ∈ normKernelSubgroup G C ↔ tateNormHom (G := G) (A := C) c = 1 :=
    fun _ => MonoidHom.mem_ker
  have hSN : ∀ b : B, sigmaMinusOneHom (G := G) (A := B) σ
      (tateNormHom (G := G) (A := B) b) = 1 :=
    fun b => (hFB _).1 (show ∀ g : G, g • tateNorm G B b = tateNorm G B b from
      fun g => smul_tateNorm_eq (G := G) (A := B) g b)
  have hNS : ∀ b : B, tateNormHom (G := G) (A := B)
      (sigmaMinusOneHom (G := G) (A := B) σ b) = 1 :=
    fun b => tateNorm_sigmaMinusOne_eq_one (G := G) (A := B) σ b
  -- The six quotient groups are finite.
  have : Finite (fixedSubgroup G A ⧸
      (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)) := ‹Finite (HerbrandH0 G A)›
  have : Finite (fixedSubgroup G B ⧸
      (tateNormSubgroup G B).subgroupOf (fixedSubgroup G B)) := ‹Finite (HerbrandH0 G B)›
  have : Finite (fixedSubgroup G C ⧸
      (tateNormSubgroup G C).subgroupOf (fixedSubgroup G C)) := ‹Finite (HerbrandH0 G C)›
  have : Finite (normKernelSubgroup G A ⧸
      (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)) :=
    ‹Finite (HerbrandHMinusOne G A σ)›
  have : Finite (normKernelSubgroup G B ⧸
      (augmentationSubgroup G B σ).subgroupOf (normKernelSubgroup G B)) :=
    ‹Finite (HerbrandHMinusOne G B σ)›
  have : Finite (normKernelSubgroup G C ⧸
      (augmentationSubgroup G C σ).subgroupOf (normKernelSubgroup G C)) :=
    ‹Finite (HerbrandHMinusOne G C σ)›
  -- Restrictions of `i` and `j`.
  obtain ⟨iF, hiF⟩ := exists_hexagon_restrict i (fixedSubgroup G A) (fixedSubgroup G B)
    (fun a ha => (hFB _).2 (by rw [← hiS, (hFA a).1 ha, map_one]))
  obtain ⟨jF, hjF⟩ := exists_hexagon_restrict j (fixedSubgroup G B) (fixedSubgroup G C)
    (fun b hb => (hFC _).2 (by rw [← hjS, (hFB b).1 hb, map_one]))
  obtain ⟨iK, hiK⟩ := exists_hexagon_restrict i (normKernelSubgroup G A)
    (normKernelSubgroup G B) (fun a ha => (hKB _).2 (by rw [← hiN, (hKA a).1 ha, map_one]))
  obtain ⟨jK, hjK⟩ := exists_hexagon_restrict j (normKernelSubgroup G B)
    (normKernelSubgroup G C) (fun b hb => (hKC _).2 (by rw [← hjN, (hKB b).1 hb, map_one]))
  obtain ⟨jP₃, hjP₃, hsP₃⟩ := exists_hexagon_comap j hsurj (fixedSubgroup G C)
  obtain ⟨jP₆, hjP₆, hsP₆⟩ := exists_hexagon_comap j hsurj (normKernelSubgroup G C)
  have hP₃ : ∀ b : B, b ∈ (fixedSubgroup G C).comap j ↔
      sigmaMinusOneHom (G := G) (A := C) σ (j b) = 1 :=
    fun b => Subgroup.mem_comap.trans (hFC (j b))
  have hP₆ : ∀ b : B, b ∈ (normKernelSubgroup G C).comap j ↔
      tateNormHom (G := G) (A := C) (j b) = 1 :=
    fun b => Subgroup.mem_comap.trans (hKC (j b))
  -- The two connecting maps.
  obtain ⟨α, hα⟩ := exists_hexagon_lift_of_range i hinj
    ((sigmaMinusOneHom (G := G) (A := B) σ).comp ((fixedSubgroup G C).comap j).subtype)
    (fun x => MonoidHom.mem_range.2 ((hker _).1 (by
      show j (sigmaMinusOneHom (G := G) (A := B) σ (x : B)) = 1
      rw [hjS]
      exact (hP₃ x).1 x.2)))
    (normKernelSubgroup G A)
    (fun x a ha => (hKA a).2 (hinj (by rw [map_one, hiN, ha]; exact hNS x)))
  obtain ⟨β, hβ⟩ := exists_hexagon_lift_of_range i hinj
    ((tateNormHom (G := G) (A := B)).comp ((normKernelSubgroup G C).comap j).subtype)
    (fun x => MonoidHom.mem_range.2 ((hker _).1 (by
      show j (tateNormHom (G := G) (A := B) (x : B)) = 1
      rw [hjN]
      exact (hP₆ x).1 x.2)))
    (fixedSubgroup G A)
    (fun x a ha => (hFA a).2 (hinj (by rw [map_one, hiS, ha]; exact hSN x)))
  -- The hexagon `H⁰(A) → H⁰(B) → H⁰(C) → H⁻¹(A) → H⁻¹(B) → H⁻¹(C) → H⁰(A)`.
  have key := card_hexagon_of_exact_iff
    (hexagonMk (fixedSubgroup G A) (tateNormSubgroup G A))
    (hexagonMk (fixedSubgroup G B) (tateNormSubgroup G B))
    ((hexagonMk (fixedSubgroup G C) (tateNormSubgroup G C)).comp jP₃)
    (hexagonMk (normKernelSubgroup G A) (augmentationSubgroup G A σ))
    (hexagonMk (normKernelSubgroup G B) (augmentationSubgroup G B σ))
    ((hexagonMk (normKernelSubgroup G C) (augmentationSubgroup G C σ)).comp jP₆)
    (hexagonMk_surjective _ _) (hexagonMk_surjective _ _)
    (by rw [MonoidHom.coe_comp]; exact (hexagonMk_surjective _ _).comp hsP₃)
    (hexagonMk_surjective _ _) (hexagonMk_surjective _ _)
    (by rw [MonoidHom.coe_comp]; exact (hexagonMk_surjective _ _).comp hsP₆)
    ((hexagonMk (fixedSubgroup G B) (tateNormSubgroup G B)).comp iF)
    ((hexagonMk (fixedSubgroup G C) (tateNormSubgroup G C)).comp jF)
    ((hexagonMk (normKernelSubgroup G A) (augmentationSubgroup G A σ)).comp α)
    ((hexagonMk (normKernelSubgroup G B) (augmentationSubgroup G B σ)).comp iK)
    ((hexagonMk (normKernelSubgroup G C) (augmentationSubgroup G C σ)).comp jK)
    ((hexagonMk (fixedSubgroup G A) (tateNormSubgroup G A)).comp β)
    (fun y => by
      simp only [MonoidHom.comp_apply, hexagonMk_eq_iff, hexagonMk_eq_one_iff, hiF, hjF]
      exact hexagon_exact_middle i j hker hinj hsurj _ _ _ _ hiS hjN hSN
        (fixedSubgroup G A) hFA y ((hFB y).1 y.2))
    (fun y => by
      simp only [MonoidHom.comp_apply, hexagonMk_eq_iff, hexagonMk_eq_one_iff, hjF, hjP₃]
      exact hexagon_exact_connecting i j hker hinj hsurj _ _ _ _ hiS hjN hSN
        (fixedSubgroup G B) hFB y (α y) (hα y))
    (fun y => by
      simp only [MonoidHom.comp_apply, hexagonMk_eq_iff, hexagonMk_eq_one_iff, hiK]
      exact hexagon_exact_after_connecting i j hker hinj _ _ _ hiS hjS
        ((fixedSubgroup G C).comap j) hP₃ (fun z => (α z : A)) hα y)
    (fun y => by
      simp only [MonoidHom.comp_apply, hexagonMk_eq_iff, hexagonMk_eq_one_iff, hiK, hjK]
      exact hexagon_exact_middle i j hker hinj hsurj _ _ _ _ hiN hjS hNS
        (normKernelSubgroup G A) hKA y ((hKB y).1 y.2))
    (fun y => by
      simp only [MonoidHom.comp_apply, hexagonMk_eq_iff, hexagonMk_eq_one_iff, hjK, hjP₆]
      exact hexagon_exact_connecting i j hker hinj hsurj _ _ _ _ hiN hjS hNS
        (normKernelSubgroup G B) hKB y (β y) (hβ y))
    (fun y => by
      simp only [MonoidHom.comp_apply, hexagonMk_eq_iff, hexagonMk_eq_one_iff, hiF]
      exact hexagon_exact_after_connecting i j hker hinj _ _ _ hiN hjN
        ((normKernelSubgroup G C).comap j) hP₆ (fun z => (β z : A)) hβ y)
  exact key

end Hexagon

/-- Herbrand-quotient theory Herbrand-quotient multiplicativity: Herbrand quotient multiplicativity
for a short exact sequence of multiplicative `G`-modules, proved from the
standard two-periodic Tate complex and mathlib's homology long exact
sequence. -/
theorem herbrandQuotient_exact_multiplicative
    {G A B C : Type}
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c) (σ : G)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    herbrandQuotient_exact_multiplicativeStatement (G := G) i j hi hj hker hinj hsurj σ
      hgen := by
  show herbrandQuotient (G := G) (A := B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := C) σ
  have hcard :=
    herbrand_exact_cardinality_identity_aux
      (G := G) (A := A) (B := B) (C := C)
      i j hi hj hker hinj hsurj σ hgen
  have hA :
      ((Nat.card (HerbrandHMinusOne G A σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr
      (Finite.card_pos (α := HerbrandHMinusOne G A σ)).ne'
  have hB :
      ((Nat.card (HerbrandHMinusOne G B σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr
      (Finite.card_pos (α := HerbrandHMinusOne G B σ)).ne'
  have hC :
      ((Nat.card (HerbrandHMinusOne G C σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr
      (Finite.card_pos (α := HerbrandHMinusOne G C σ)).ne'
  unfold herbrandQuotient
  field_simp [hA, hB, hC]
  have hcardQ :
      (Nat.card (HerbrandH0 G B) : ℚ) *
          Nat.card (HerbrandHMinusOne G A σ) *
          Nat.card (HerbrandHMinusOne G C σ) =
        Nat.card (HerbrandH0 G A) *
          Nat.card (HerbrandH0 G C) *
          Nat.card (HerbrandHMinusOne G B σ) := by
    exact_mod_cast hcard
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcardQ

end Herbrand
end ProfiniteCohomology

end
end Langlands.NYLL.CyclicCohomology
