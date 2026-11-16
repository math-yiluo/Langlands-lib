/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U005.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U010.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U016.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U066.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U068.Proofs

/-!
# NYLL M119.006: definedness of the middle Herbrand quotient

Modified by Worker 749, 16 November 2026: prove the published target
`herbrandQuotientDefined_middle_of_left_rightStatement` (M119.006) as the
theorem `herbrandQuotientDefined_middle_of_left_right` of
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean` at
fbd320cd8b1b06487c58227e92eb135794267709, with its source binders and the
published proposition as its type. Prefix the namespace with `Langlands.NYLL`.
The source proof passes to Tate cohomology through category-theoretic
comparison isomorphisms whose proofs are not in the Library; the port
replaces it by a new elementary proof written for this port (not the source
proof). The maps `H⁰(A) → H⁰(B) → H⁰(C)` and `H⁻¹(A) → H⁻¹(B) → H⁻¹(C)`
induced by `i` and `j` are exact at the middle term, and the middle term of an
exact sequence with finite outer terms is finite. The last step is the source
private theorem `finite_middle_of_exact` (M119.002) of the same file, kept
with its source statement and source proof and moved into a section with the
variable line `variable {G A B C : Type}`. In that section the port adds
private helper declarations: copies of private helpers of this port's proof
of M117.021 `herbrand_exact_cardinality_identity`, and the new
`finite_middle_of_exact_iff`. These use the published M113.005, M113.010,
M113.016, M113.066 and M113.068 proofs, which the module imports. The private
declarations precede the source variable lines, which the main theorem uses.
Replace the source imports by the published statement module and these
published proof modules, and omit the open of `CategoryTheory`, the universe
declaration and the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

section Exact

variable {G A B C : Type}

/-! ### Finiteness of the middle term of an exact sequence -/

/-- In an exact pair `X → Y → Z`, finiteness of `X` and `Z` forces
finiteness of `Y`. -/
private theorem finite_middle_of_exact
    {X Y Z : Type}
    [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : Y →* Z) (hexact : MonoidHom.range f = MonoidHom.ker g)
    [Finite X] [Finite Z] :
    Finite Y := by
  apply g.finite_iff_finite_ker_range.mpr
  constructor
  · let : Finite (MonoidHom.range f) :=
      Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    rw [← hexact]
    infer_instance
  · infer_instance

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

/-- The middle term `X₂` of `X₁ → X₂ → X₃` is finite when `X₁` and `X₃` are,
for the maps induced by `ψ₁ : P₁ →* X₂` and `ψ₂ : P₂ →* X₃` along surjections
`p₁ : P₁ →* X₁` and `p₂ : P₂ →* X₂`, given that `ψ₁` descends along `p₁` and an
element-level exactness criterion at `X₂`. -/
private theorem finite_middle_of_exact_iff {P₁ P₂ X₁ X₂ X₃ : Type} [Group P₁] [Group P₂]
    [Group X₁] [Group X₂] [Group X₃] [Finite X₁] [Finite X₃]
    (p₁ : P₁ →* X₁) (p₂ : P₂ →* X₂) (hp₁ : Function.Surjective p₁)
    (hp₂ : Function.Surjective p₂) (ψ₁ : P₁ →* X₂) (ψ₂ : P₂ →* X₃)
    (k₁ : p₁.ker ≤ ψ₁.ker)
    (H : ∀ y : P₂, (∃ z : P₁, ψ₁ z = p₂ y) ↔ ψ₂ y = 1) :
    Finite X₂ :=
  finite_middle_of_exact (hexagonLift p₁ hp₁ ψ₁ k₁)
    (hexagonLift p₂ hp₂ ψ₂ (hexagon_ker_le_ker ψ₁ p₂ ψ₂ H))
    (range_hexagonLift_eq_ker p₁ hp₁ ψ₁ k₁ p₂ hp₂ ψ₂
      (hexagon_ker_le_ker ψ₁ p₂ ψ₂ H) H)

/-! ### Quotients `Z / R` and restrictions -/

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

/-! ### Exactness at the middle term

The lemma below is stated for endomorphisms `u` and `v` of `A`, `B` and `C`
commuting with `i` and `j`; the proof uses it for `(u, v) = (N_G, σ - 1)` and
for `(u, v) = (σ - 1, N_G)`. -/

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

end Exact

variable {G A B C : Type}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

/-- Herbrand-quotient multiplicativity, finiteness transfer from the first and third terms to
the middle term. -/
theorem herbrandQuotientDefined_middle_of_left_right
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hC : HerbrandQuotientDefined G C σ) :
    herbrandQuotientDefined_middle_of_left_rightStatement (G := G) i j hi hj hker hinj hsurj σ
      hgen hA hC := by
  -- The four finiteness hypotheses, on the quotient groups.
  have : Finite (fixedSubgroup G A ⧸
      (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)) := hA.1
  have : Finite (fixedSubgroup G C ⧸
      (tateNormSubgroup G C).subgroupOf (fixedSubgroup G C)) := hC.1
  have : Finite (normKernelSubgroup G A ⧸
      (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)) := hA.2
  have : Finite (normKernelSubgroup G C ⧸
      (augmentationSubgroup G C σ).subgroupOf (normKernelSubgroup G C)) := hC.2
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
  -- Restrictions of `i` and `j`.
  obtain ⟨iF, hiF⟩ := exists_hexagon_restrict i (fixedSubgroup G A) (fixedSubgroup G B)
    (fun a ha => (hFB _).2 (by rw [← hiS, (hFA a).1 ha, map_one]))
  obtain ⟨jF, hjF⟩ := exists_hexagon_restrict j (fixedSubgroup G B) (fixedSubgroup G C)
    (fun b hb => (hFC _).2 (by rw [← hjS, (hFB b).1 hb, map_one]))
  obtain ⟨iK, hiK⟩ := exists_hexagon_restrict i (normKernelSubgroup G A)
    (normKernelSubgroup G B) (fun a ha => (hKB _).2 (by rw [← hiN, (hKA a).1 ha, map_one]))
  obtain ⟨jK, hjK⟩ := exists_hexagon_restrict j (normKernelSubgroup G B)
    (normKernelSubgroup G C) (fun b hb => (hKC _).2 (by rw [← hjN, (hKB b).1 hb, map_one]))
  -- `H⁰(A) → H⁰(B) → H⁰(C)` is exact at `H⁰(B)`.
  have hzero : Finite (fixedSubgroup G B ⧸
      (tateNormSubgroup G B).subgroupOf (fixedSubgroup G B)) :=
    finite_middle_of_exact_iff
      (hexagonMk (fixedSubgroup G A) (tateNormSubgroup G A))
      (hexagonMk (fixedSubgroup G B) (tateNormSubgroup G B))
      (hexagonMk_surjective _ _) (hexagonMk_surjective _ _)
      ((hexagonMk (fixedSubgroup G B) (tateNormSubgroup G B)).comp iF)
      ((hexagonMk (fixedSubgroup G C) (tateNormSubgroup G C)).comp jF)
      (fun z hz => by
        rw [MonoidHom.mem_ker, hexagonMk_eq_one_iff] at hz
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hexagonMk_eq_one_iff, hiF]
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hz
        exact MonoidHom.mem_range.2 ⟨i a, by rw [← hiN, ha]⟩)
      (fun y => by
        simp only [MonoidHom.comp_apply, hexagonMk_eq_iff, hexagonMk_eq_one_iff, hiF, hjF]
        exact hexagon_exact_middle i j hker hinj hsurj _ _ _ _ hiS hjN hSN
          (fixedSubgroup G A) hFA y ((hFB y).1 y.2))
  -- `H⁻¹(A) → H⁻¹(B) → H⁻¹(C)` is exact at `H⁻¹(B)`.
  have hminus : Finite (normKernelSubgroup G B ⧸
      (augmentationSubgroup G B σ).subgroupOf (normKernelSubgroup G B)) :=
    finite_middle_of_exact_iff
      (hexagonMk (normKernelSubgroup G A) (augmentationSubgroup G A σ))
      (hexagonMk (normKernelSubgroup G B) (augmentationSubgroup G B σ))
      (hexagonMk_surjective _ _) (hexagonMk_surjective _ _)
      ((hexagonMk (normKernelSubgroup G B) (augmentationSubgroup G B σ)).comp iK)
      ((hexagonMk (normKernelSubgroup G C) (augmentationSubgroup G C σ)).comp jK)
      (fun z hz => by
        rw [MonoidHom.mem_ker, hexagonMk_eq_one_iff] at hz
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hexagonMk_eq_one_iff, hiK]
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hz
        exact MonoidHom.mem_range.2 ⟨i a, by rw [← hiS, ha]⟩)
      (fun y => by
        simp only [MonoidHom.comp_apply, hexagonMk_eq_iff, hexagonMk_eq_one_iff, hiK, hjK]
        exact hexagon_exact_middle i j hker hinj hsurj _ _ _ _ hiN hjS hNS
          (normKernelSubgroup G A) hKA y ((hKB y).1 y.2))
  exact ⟨hzero, hminus⟩

end Herbrand
end ProfiniteCohomology

end
end Langlands.NYLL.CyclicCohomology
