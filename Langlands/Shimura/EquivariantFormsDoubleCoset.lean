import Mathlib.GroupTheory.DoubleCoset
import Langlands.Shimura.EquivariantForms
import Langlands.Representation.Induction.PermutationDual

/-!
# Forms restricted to double cosets

Let `ι : Γ →* G` be a group homomorphism, `K` a subgroup of `G` and `ρ` a representation of `K`.
A form of `Langlands.Shimura.EquivariantForms` (`f (ι γ * g) = f g`, `f (g * k) = ρ k⁻¹ (f g)`)
is determined by its values at representatives `y` of the double cosets `ι Γ \ G / K`, and its
value at `y` is invariant under the stabilizer `Δ_y = {k ∈ K | ι γ * y = y * k for some γ}`.
Restriction to the representatives identifies the forms with the families of `Δ_y`-invariant
vectors.

For a subgroup `N ≤ K` normal in `K`, the stabilizers all lie in `N` exactly when right
translation by `K` moves every class of `ι Γ \ G / N` unless the translating element lies in
`N`. Under this hypothesis the forms of level `N` with trivial coefficients are the functions on
`K ⧸ N` with values in the functions on `ι Γ \ G / K`, compatibly with the right translation
action of `K`, and hence the `R`-linear maps from the permutation module `R[K ⧸ N]` to these
functions.

This is a generic algebraic form of Harris's restriction to double cosets (Harris, *Galois
properties of cohomological automorphic forms on GL(n)*, 1999, (3.9)-(3.10) under the hypothesis
(3.6), and (4.6)-(4.7) under the hypothesis (4.5), followed by the duality between functions and
group rings before (4.8)); no group, level or coefficient system of Harris is specialized here.

## Main definitions

* `DoubleCosets ι K`: the double coset space `ι Γ \ G / K`.
* `doubleCosetStabilizer ι K y`: the subgroup `Δ_y` of `K`.
* `doubleCosetEquiv ι K ρ`: forms are the families `x ↦ v_x` of `Δ_{x.out}`-invariant vectors,
  `f ↦ (x ↦ f x.out)`.
* `doubleCosetStabilizer_le_iff`: the stabilizers lie in `N` iff right translation by `K` acts
  without fixed points modulo `N` on `ι Γ \ G / N`.
* `levelDoubleCosetEquiv ι hle hΔ`: the level action of `K` on the forms of level `N` with
  trivial coefficients is the representation on functions `K ⧸ N → (DoubleCosets ι K → R)`,
  `f ↦ ([k] ↦ x ↦ f (x.out * k⁻¹))`.
* `levelDoubleCosetHomEquiv ι hle hΔ`: the same with `Hom_R(R[K ⧸ N], DoubleCosets ι K → R)`.
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

universe t uR uΓ uG

variable {R : Type uR} [CommRing R] {Γ : Type uΓ} {G : Type uG} [Group Γ] [Group G]

section Stabilizer

variable (ι : Γ →* G) (K : Subgroup G)

/-- The double coset space `ι Γ \ G / K`. -/
abbrev DoubleCosets : Type uG :=
  DoubleCoset.Quotient (ι.range : Set G) (K : Set G)

/-- The stabilizer `Δ_y` of the class of `y` in `ι Γ \ G` under right translation by `K`: the
elements `k : K` with `ι γ * y = y * k` for some `γ : Γ`. -/
def doubleCosetStabilizer (y : G) : Subgroup K where
  carrier := {k | ∃ γ : Γ, ι γ * y = y * k}
  mul_mem' := by
    rintro a b ⟨γ, hγ⟩ ⟨δ, hδ⟩
    exact ⟨γ * δ, by rw [map_mul, mul_assoc, hδ, ← mul_assoc, hγ, Subgroup.coe_mul, mul_assoc]⟩
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro a ⟨γ, hγ⟩
    refine ⟨γ⁻¹, ?_⟩
    rw [map_inv, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, hγ, mul_inv_cancel_right]

variable {ι K}

lemma mem_doubleCosetStabilizer {y : G} {k : K} :
    k ∈ doubleCosetStabilizer ι K y ↔ ∃ γ : Γ, ι γ * y = y * k :=
  Iff.rfl

/-- Two decompositions `ι γ₁ * y * k₁ = ι γ₂ * y * k₂` differ by an element of the stabilizer:
`k₂ * k₁⁻¹ ∈ Δ_y`. -/
lemma mul_inv_mem_doubleCosetStabilizer {y : G} {γ₁ γ₂ : Γ} {k₁ k₂ : K}
    (h : ι γ₁ * y * k₁ = ι γ₂ * y * k₂) : k₂ * k₁⁻¹ ∈ doubleCosetStabilizer ι K y := by
  refine ⟨γ₂⁻¹ * γ₁, ?_⟩
  rw [map_mul, map_inv, mul_assoc, inv_mul_eq_iff_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    ← mul_assoc, ← mul_assoc, ← h, mul_inv_cancel_right]

/-- Every `g : G` is `ι γ * y * k` for the representative `y` of its double coset, some `γ : Γ`
and some `k : K`. -/
lemma exists_eq_mul_out_mul (g : G) :
    ∃ (γ : Γ) (k : K), g = ι γ * (DoubleCoset.mk ι.range K g).out * k := by
  obtain ⟨_, ⟨γ, rfl⟩, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul ι.range K g
  exact ⟨γ⁻¹, ⟨k, hk⟩⁻¹, by rw [he]; simp [mul_assoc]⟩

variable (ι K) in
/-- A chosen `k : K` with `g = ι γ * y * k` for the representative `y` of the double coset of
`g` and some `γ : Γ`. -/
def outFactor (g : G) : K :=
  (exists_eq_mul_out_mul (ι := ι) (K := K) g).choose_spec.choose

lemma exists_eq_mul_out_mul_outFactor (g : G) :
    ∃ γ : Γ, g = ι γ * (DoubleCoset.mk ι.range K g).out * outFactor ι K g :=
  ⟨_, (exists_eq_mul_out_mul (ι := ι) (K := K) g).choose_spec.choose_spec⟩

end Stabilizer

section Restriction

variable (ι : Γ →* G) (K : Subgroup G) {V : Type t} [AddCommGroup V] [Module R V]
  (ρ : Representation R K V)

variable {ι K ρ} in
/-- The value of a form at `ι γ * y * k` is `ρ k⁻¹` applied to its value at `y`. -/
lemma forms_apply_mul_mul (f : forms ι K ρ) (γ : Γ) (y : G) (k : K) :
    f.1 (ι γ * y * k) = ρ k⁻¹ (f.1 y) := by
  rw [f.2.2 (ι γ * y) k, f.2.1 γ y]

variable {ι K ρ} in
/-- The value of a form at `y` is invariant under the stabilizer `Δ_y`. -/
lemma apply_mem_invariants (f : forms ι K ρ) (y : G) :
    f.1 y ∈ Representation.invariants (ρ.comp (doubleCosetStabilizer ι K y).subtype) := by
  rw [Representation.mem_invariants]
  rintro ⟨k, γ, hγ⟩
  have h := f.2.2 y k
  rw [← hγ, f.2.1 γ y] at h
  change ρ k (f.1 y) = f.1 y
  conv_lhs => rw [h]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable {ι K ρ} in
/-- For a `Δ_y`-invariant vector `v`, two decompositions `ι γ₁ * y * k₁ = ι γ₂ * y * k₂` give
`ρ k₁⁻¹ v = ρ k₂⁻¹ v`. -/
lemma apply_inv_eq_of_mem_invariants {y : G} {v : V}
    (hv : v ∈ Representation.invariants (ρ.comp (doubleCosetStabilizer ι K y).subtype))
    {γ₁ γ₂ : Γ} {k₁ k₂ : K} (h : ι γ₁ * y * k₁ = ι γ₂ * y * k₂) :
    ρ k₁⁻¹ v = ρ k₂⁻¹ v := by
  have hm := (Representation.mem_invariants _ v).1 hv
    ⟨_, mul_inv_mem_doubleCosetStabilizer h⟩
  change ρ (k₂ * k₁⁻¹) v = v at hm
  conv_rhs => rw [← hm]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]

/-- The families of `Δ_y`-invariant vectors indexed by the double cosets, with `y` the chosen
representative `x.out` of `x`. -/
abbrev DoubleCosetFamilies : Type (max uG t) :=
  ∀ x : DoubleCosets ι K,
    Representation.invariants (ρ.comp (doubleCosetStabilizer ι K x.out).subtype)

/-- The function `g ↦ ρ k⁻¹ v_x` on `G`, where `x` is the double coset of `g` and
`g = ι γ * x.out * k`. -/
def doubleCosetLift (φ : DoubleCosetFamilies ι K ρ) (g : G) : V :=
  ρ (outFactor ι K g)⁻¹ (φ (DoubleCoset.mk ι.range K g)).1

variable {ι K ρ} in
lemma doubleCosetLift_eq (φ : DoubleCosetFamilies ι K ρ) {g : G} {x : DoubleCosets ι K}
    (hx : DoubleCoset.mk ι.range K g = x) {γ : Γ} {k : K} (h : g = ι γ * x.out * k) :
    doubleCosetLift ι K ρ φ g = ρ k⁻¹ (φ x).1 := by
  subst hx
  obtain ⟨γ', h'⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
  exact apply_inv_eq_of_mem_invariants (φ _).2 (h'.symm.trans h)

variable {ι K ρ} in
lemma doubleCosetLift_mem (φ : DoubleCosetFamilies ι K ρ) :
    doubleCosetLift ι K ρ φ ∈ forms ι K ρ := by
  refine ⟨fun γ₀ g => ?_, fun g k₀ => ?_⟩
  · obtain ⟨γ, h⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
    refine doubleCosetLift_eq φ
      (DoubleCoset.mk_mem_mul ⟨ι γ₀, MonoidHom.mem_range.2 ⟨γ₀, rfl⟩⟩ g) (γ := γ₀ * γ) ?_
    conv_lhs => rw [h]
    simp [mul_assoc]
  · obtain ⟨γ, h⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
    rw [doubleCosetLift_eq φ (DoubleCoset.mk_mul_mem k₀ g) (γ := γ)
      (k := outFactor ι K g * k₀)
      (by rw [Subgroup.coe_mul, ← mul_assoc]; exact congrArg (· * (k₀ : G)) h)]
    rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    rfl

/-- Restriction to the representatives of the double cosets: the forms for `ρ` are the families
of `Δ_y`-invariant vectors, `f ↦ (x ↦ f x.out)`. The inverse sends a family `v` to the form
`ι γ * x.out * k ↦ ρ k⁻¹ v_x`. -/
def doubleCosetEquiv : forms ι K ρ ≃ₗ[R] DoubleCosetFamilies ι K ρ where
  toFun f x := ⟨f.1 x.out, apply_mem_invariants f x.out⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun φ := ⟨doubleCosetLift ι K ρ φ, doubleCosetLift_mem φ⟩
  left_inv f := by
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨γ, h⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
    change ρ (outFactor ι K g)⁻¹ (f.1 (DoubleCoset.mk ι.range K g).out) = f.1 g
    conv_rhs => rw [h]
    rw [forms_apply_mul_mul]
  right_inv φ := by
    refine funext fun x => Subtype.ext ?_
    change doubleCosetLift ι K ρ φ x.out = (φ x).1
    rw [doubleCosetLift_eq φ (DoubleCoset.out_eq' x) (γ := 1) (k := 1) (by simp)]
    simp

@[simp]
lemma doubleCosetEquiv_apply_coe (f : forms ι K ρ) (x : DoubleCosets ι K) :
    (doubleCosetEquiv ι K ρ f x).1 = f.1 x.out :=
  rfl

/-- The form attached to a family `v` takes the value `ρ k⁻¹ v_x` at `ι γ * x.out * k`. -/
lemma doubleCosetEquiv_symm_apply_coe (φ : DoubleCosetFamilies ι K ρ) (x : DoubleCosets ι K)
    (γ : Γ) (k : K) :
    ((doubleCosetEquiv ι K ρ).symm φ).1 (ι γ * x.out * k) = ρ k⁻¹ (φ x).1 := by
  rw [forms_apply_mul_mul]
  exact congrArg (fun v => ρ k⁻¹ v.1) (congrFun ((doubleCosetEquiv ι K ρ).apply_symm_apply φ) x)

end Restriction

section Level

variable (ι : Γ →* G) {K N : Subgroup G} (hle : N ≤ K)

include hle in
/-- The stabilizers `Δ_g` all lie in `N ≤ K` exactly when right translation by `k : K` fixes
the class of some `g` in `ι Γ \ G / N` only for `k ∈ N`. For `K = K^ℓ × K_ℓ` and `N = K^ℓ` the
right-hand side is Harris's hypothesis (3.6), that `K_ℓ` acts without fixed points on
`GJ(ℚ)\GJ(𝔸)/K_∞ · K^ℓ`; it then also holds for every `N` between `K^ℓ` and `K`, such as
`K(n) = K^ℓ × K_ℓ(n)`. Harris's (4.5) is the analogous condition for `K_ℓ × C_p`. -/
lemma doubleCosetStabilizer_le_iff :
    (∀ g : G, doubleCosetStabilizer ι K g ≤ N.subgroupOf K) ↔
      ∀ (g : G) (k : K),
        DoubleCoset.mk ι.range N (g * k) = DoubleCoset.mk ι.range N g → k ∈ N.subgroupOf K := by
  constructor
  · intro hΔ g k he
    obtain ⟨_, ⟨γ, rfl⟩, n, hn, hg⟩ := DoubleCoset.eq.1 he
    have hm : k * ⟨n, hle hn⟩ ∈ doubleCosetStabilizer ι K g := ⟨γ⁻¹, by
      rw [map_inv, inv_mul_eq_iff_eq_mul]
      simpa [mul_assoc] using hg⟩
    have hn' : (⟨n, hle hn⟩ : K) ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.2 hn
    simpa using (N.subgroupOf K).mul_mem (hΔ g hm) ((N.subgroupOf K).inv_mem hn')
  · rintro hfree g k ⟨γ, hγ⟩
    apply hfree g k
    rw [← hγ]
    exact DoubleCoset.mk_mem_mul ⟨ι γ, MonoidHom.mem_range.2 ⟨γ, rfl⟩⟩ g

variable [(N.subgroupOf K).Normal]

omit [(N.subgroupOf K).Normal] in
variable {ι hle} in
/-- Forms with trivial coefficients are right invariant under the level. -/
lemma trivialForms_apply_mul
    (f : forms ι N ((Representation.trivial R K R).comp (Subgroup.inclusion hle))) (g : G)
    (n : N) : f.1 (g * n) = f.1 g :=
  f.2.2 g n

variable {ι hle} in
/-- For a form `f` of level `N` with trivial coefficients, `f (y * a⁻¹)` only depends on the
class of `a` in `K ⧸ N`. -/
lemma trivialForms_apply_mul_inv_eq
    (f : forms ι N ((Representation.trivial R K R).comp (Subgroup.inclusion hle))) (y : G)
    {a b : K} (h : a⁻¹ * b ∈ N.subgroupOf K) : f.1 (y * (a : G)⁻¹) = f.1 (y * (b : G)⁻¹) := by
  have hm : a * b⁻¹ ∈ N.subgroupOf K := by
    have := (inferInstance : (N.subgroupOf K).Normal).conj_mem _ h a
    simpa [mul_assoc] using (N.subgroupOf K).inv_mem this
  have := trivialForms_apply_mul f (y * (a : G)⁻¹) ⟨_, Subgroup.mem_subgroupOf.1 hm⟩
  rw [← this]
  simp [mul_assoc]

/-- The function `[k] ↦ x ↦ f (x.out * k⁻¹)` on `K ⧸ N` attached to a form `f` of level `N` with
trivial coefficients. -/
def levelDoubleCosetFun
    (f : forms ι N ((Representation.trivial R K R).comp (Subgroup.inclusion hle))) :
    K ⧸ N.subgroupOf K → DoubleCosets ι K → R :=
  fun q x => Quotient.liftOn' q (fun k : K => f.1 (x.out * (k : G)⁻¹)) fun _ _ h =>
    trivialForms_apply_mul_inv_eq f x.out (QuotientGroup.leftRel_apply.1 h)

@[simp]
lemma levelDoubleCosetFun_mk
    (f : forms ι N ((Representation.trivial R K R).comp (Subgroup.inclusion hle))) (k : K)
    (x : DoubleCosets ι K) :
    levelDoubleCosetFun ι hle f (k : K ⧸ N.subgroupOf K) x = f.1 (x.out * (k : G)⁻¹) :=
  rfl

/-- `levelDoubleCosetFun` as an `R`-linear map. -/
def levelDoubleCosetMap :
    forms ι N ((Representation.trivial R K R).comp (Subgroup.inclusion hle)) →ₗ[R]
      (K ⧸ N.subgroupOf K → DoubleCosets ι K → R) where
  toFun := levelDoubleCosetFun ι hle
  map_add' f f' := by
    refine funext fun q => funext fun x => ?_
    induction q using QuotientGroup.induction_on
    rfl
  map_smul' r f := by
    refine funext fun q => funext fun x => ?_
    induction q using QuotientGroup.induction_on
    rfl

variable (hΔ : ∀ g : G, doubleCosetStabilizer ι K g ≤ N.subgroupOf K)

/-- The function `g ↦ φ [k⁻¹] x` on `G`, where `x` is the double coset of `g` in `ι Γ \ G / K`
and `g = ι γ * x.out * k`. -/
def levelDoubleCosetLift (φ : K ⧸ N.subgroupOf K → DoubleCosets ι K → R) (g : G) : R :=
  φ ((outFactor ι K g)⁻¹ : K) (DoubleCoset.mk ι.range K g)

omit [CommRing R] [(N.subgroupOf K).Normal] in
include hΔ in
lemma levelDoubleCosetLift_eq (φ : K ⧸ N.subgroupOf K → DoubleCosets ι K → R) {g : G}
    {x : DoubleCosets ι K} (hx : DoubleCoset.mk ι.range K g = x) {γ : Γ} {k : K}
    (h : g = ι γ * x.out * k) :
    levelDoubleCosetLift ι φ g = φ (k⁻¹ : K) x := by
  subst hx
  obtain ⟨γ', h'⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
  have hm := hΔ _ (mul_inv_mem_doubleCosetStabilizer (h'.symm.trans h))
  have hm' : (outFactor ι K g)⁻¹⁻¹ * k⁻¹ ∈ N.subgroupOf K := by
    simpa [mul_inv_rev] using (N.subgroupOf K).inv_mem hm
  exact congrArg (fun q => φ q _) (QuotientGroup.eq.2 hm')

include hΔ in
lemma levelDoubleCosetLift_mem (φ : K ⧸ N.subgroupOf K → DoubleCosets ι K → R) :
    levelDoubleCosetLift ι φ ∈
      forms ι N ((Representation.trivial R K R).comp (Subgroup.inclusion hle)) := by
  refine ⟨fun γ₀ g => ?_, fun g n => ?_⟩
  · obtain ⟨γ, h⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
    refine levelDoubleCosetLift_eq ι hΔ φ
      (DoubleCoset.mk_mem_mul ⟨ι γ₀, MonoidHom.mem_range.2 ⟨γ₀, rfl⟩⟩ g) (γ := γ₀ * γ) ?_
    conv_lhs => rw [h]
    simp [mul_assoc]
  · obtain ⟨γ, h⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
    let n' : K := Subgroup.inclusion hle n
    change levelDoubleCosetLift ι φ (g * n') = levelDoubleCosetLift ι φ g
    rw [levelDoubleCosetLift_eq ι hΔ φ (DoubleCoset.mk_mul_mem n' g) (γ := γ)
      (k := outFactor ι K g * n')
      (by rw [Subgroup.coe_mul, ← mul_assoc]; exact congrArg (· * (n' : G)) h)]
    refine congrArg (fun q => φ q _) (QuotientGroup.eq.2 ?_)
    have hn : n' ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.2 n.2
    simpa [mul_assoc] using
      (inferInstance : (N.subgroupOf K).Normal).conj_mem _ hn (outFactor ι K g)

/-- When all stabilizers `Δ_g` lie in `N`, `levelDoubleCosetMap` is an isomorphism; the inverse
sends a function `φ` to the form `ι γ * x.out * k ↦ φ [k⁻¹] x`. -/
def levelDoubleCosetLinearEquiv :
    forms ι N ((Representation.trivial R K R).comp (Subgroup.inclusion hle)) ≃ₗ[R]
      (K ⧸ N.subgroupOf K → DoubleCosets ι K → R) where
  toLinearMap := levelDoubleCosetMap ι hle
  invFun φ := ⟨levelDoubleCosetLift ι φ, levelDoubleCosetLift_mem ι hle hΔ φ⟩
  left_inv f := by
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨γ, h⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
    change f.1 ((DoubleCoset.mk ι.range K g).out * ((outFactor ι K g)⁻¹ : K)⁻¹) = f.1 g
    conv_rhs => rw [h, mul_assoc, f.2.1 γ]
    simp
  right_inv φ := by
    refine funext fun q => funext fun x => ?_
    induction q using QuotientGroup.induction_on with | H k => ?_
    change levelDoubleCosetLift ι φ (x.out * ((k⁻¹ : K) : G)) = φ k x
    rw [levelDoubleCosetLift_eq ι hΔ φ
      ((DoubleCoset.mk_mul_mem k⁻¹ x.out).trans (DoubleCoset.out_eq' x)) (γ := 1) (k := k⁻¹)
      (by simp)]
    simp

/-- Harris's restriction to double cosets (3.10) and (4.7), generically: when all stabilizers
`Δ_g` lie in `N`, the level action of `K` on the forms of level `N` with trivial coefficients
(right translation) is the representation of `K` on functions
`K ⧸ N → (DoubleCosets ι K → R)`, `(k • φ) q = φ (k⁻¹ • q)`. A form `f` goes to
`[k] ↦ x ↦ f (x.out * k⁻¹)`, and a function `φ` to `ι γ * x.out * k ↦ φ [k⁻¹] x`. -/
def levelDoubleCosetEquiv :
    (levelAction ι (Representation.trivial R K R) hle).Equiv
      (Langlands.Induction.functionRepresentation
        (Representation.trivial R K (DoubleCosets ι K → R)) (K ⧸ N.subgroupOf K)) :=
  Representation.Equiv.mk (levelDoubleCosetLinearEquiv ι hle hΔ) fun k₀ => by
    refine LinearMap.ext fun f => funext fun q => funext fun x => ?_
    induction q using QuotientGroup.induction_on with | H k => ?_
    change f.1 (x.out * (k : G)⁻¹ * k₀) = f.1 (x.out * ((k₀⁻¹ * k : K) : G)⁻¹)
    simp [mul_assoc]

@[simp]
lemma levelDoubleCosetEquiv_apply_mk
    (f : forms ι N ((Representation.trivial R K R).comp (Subgroup.inclusion hle))) (k : K)
    (x : DoubleCosets ι K) :
    levelDoubleCosetEquiv ι hle hΔ f (k : K ⧸ N.subgroupOf K) x = f.1 (x.out * (k : G)⁻¹) :=
  rfl

/-- The form attached to a function `φ` takes the value `φ [k⁻¹] x` at `ι γ * x.out * k`. -/
lemma levelDoubleCosetEquiv_symm_apply_coe (φ : K ⧸ N.subgroupOf K → DoubleCosets ι K → R)
    (x : DoubleCosets ι K) (γ : Γ) (k : K) :
    ((levelDoubleCosetEquiv ι hle hΔ).symm φ).1 (ι γ * x.out * k) = φ (k⁻¹ : K) x :=
  levelDoubleCosetLift_eq ι hΔ φ
    ((DoubleCoset.mk_mul_mem k _).trans
      ((DoubleCoset.mk_mem_mul ⟨ι γ, MonoidHom.mem_range.2 ⟨γ, rfl⟩⟩ x.out).trans
        (DoubleCoset.out_eq' x))) rfl

/-- `levelDoubleCosetEquiv` composed with the duality between functions and group rings, as
after Harris's (4.7): the level action on the forms of level `N` with trivial coefficients is the
representation of `K` on `Hom_R(R[K ⧸ N], DoubleCosets ι K → R)`. -/
def levelDoubleCosetHomEquiv :
    (levelAction ι (Representation.trivial R K R) hle).Equiv
      ((Langlands.Induction.permutation R K (K ⧸ N.subgroupOf K) R).linHom
        (Representation.trivial R K (DoubleCosets ι K → R))) :=
  (levelDoubleCosetEquiv ι hle hΔ).trans (Langlands.Induction.permutationDualEquiv _ _).symm

end Level

end Langlands.Shimura.EquivariantForms
