import Langlands.Shimura.EquivariantFormsDoubleCoset

/-!
# Forms whose coefficients factor through a quotient of the level

Let `ι : Γ →* G` be a group homomorphism and `K' ≤ K` subgroups of `G`. Suppose `K` comes with
homomorphisms `fst : K →* A` and `snd : K →* B` and a homomorphism `inr : B →* K` with
`fst ∘ inr = 1` and `snd ∘ inr = id`, and that `K'` is the inverse image in `K` of a normal
subgroup `H` of `B` (a `LevelFactorization`). For a representation `ρ` of `A`, the forms of level
`K'` with coefficients `ρ ∘ fst` (`Langlands.Shimura.EquivariantForms.forms`) are then determined
by their values at the points `y * (inr b)⁻¹`, for the representatives `y` of `ι Γ \ G / K` and
`b : B`, provided every stabilizer `Δ_y` of the level `K` lies in the kernels of `fst` and `snd`.
The values are arbitrary: the forms are the functions `B ⧸ H → (ι Γ \ G / K → V)`, compatibly
with the level action of `K`, and hence the `R`-linear maps `R[(B ⧸ H) × ι Γ \ G / K] → V`.

This is a generic algebraic form of Harris's isomorphism (4.8) (Harris, *Galois properties of
cohomological automorphic forms on GL(n)*, 1999, p.311), where `K = K^{ℓ,p} × K_ℓ × C_p`,
`K' = K^{ℓ,p} × K_ℓ × H_p`, `A = K_ℓ`, `B = C_p` and `H = H_p`.

## Main definitions

* `LevelFactorization K K' A B H`: the data `fst`, `snd`, `inr` above.
* `LevelFactorization.factorLinearEquiv`: forms of level `K'` are the functions
  `B ⧸ H → DoubleCosets ι K → V`, `f ↦ ([b] ↦ x ↦ f (x.out * (inr b)⁻¹))`.
* `LevelFactorization.factorEquiv`: the same as an equivalence of representations of `K`, from
  the level action to functions on `B ⧸ H` with `K` acting through `snd`.
* `LevelFactorization.factorHomEquiv`: the same with `Hom_R(R[B ⧸ H], DoubleCosets ι K → V)`.
* `LevelFactorization.factorFinsuppEquiv`: forms of level `K'` are the `R`-linear maps
  `R[(B ⧸ H) × DoubleCosets ι K] → V`.
* `invariants_comp_eq`: invariants under `K` equal invariants under a subgroup that generates
  `K` together with a subgroup acting trivially.
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

universe t uR uΓ uG uA uB

variable {R : Type uR} [CommRing R] {Γ : Type uΓ} {G : Type uG} [Group Γ] [Group G]

/-- A factorization of a level `K` adapted to a subgroup `K' ≤ K`: homomorphisms `fst : K →* A`,
`snd : K →* B` and `inr : B →* K` with `fst ∘ inr = 1` and `snd ∘ inr = id`, such that `K'`
consists of the `k : K` with `snd k ∈ H`. In Harris's case `K = K^{ℓ,p} × K_ℓ × C_p`,
`K' = K^{ℓ,p} × K_ℓ × H_p`, `fst` and `snd` are the components at `ℓ` and `p`, and `inr`
embeds `C_p` with trivial other components. -/
structure LevelFactorization (K K' : Subgroup G) (A : Type uA) (B : Type uB) [Group A] [Group B]
    (H : Subgroup B) where
  /-- `K'` is contained in `K`. -/
  le : K' ≤ K
  /-- The `A`-component of an element of `K`. -/
  fst : K →* A
  /-- The `B`-component of an element of `K`. -/
  snd : K →* B
  /-- The embedding of `B` into `K`. -/
  inr : B →* K
  fst_inr (b : B) : fst (inr b) = 1
  snd_inr (b : B) : snd (inr b) = b
  mem_iff (k : K) : (k : G) ∈ K' ↔ snd k ∈ H

namespace LevelFactorization

attribute [simp] fst_inr snd_inr

variable {K K' : Subgroup G} {A : Type uA} {B : Type uB} [Group A] [Group B] {H : Subgroup B}
  (c : LevelFactorization K K' A B H)

/-- An element of `K` with trivial `B`-component lies in `K'`. -/
theorem mem_of_snd_eq_one {k : K} (hk : c.snd k = 1) : (k : G) ∈ K' :=
  (c.mem_iff k).2 (hk ▸ H.one_mem)

/-- `inr` takes values in `K'` on `H`. -/
theorem inr_mem {b : B} (hb : b ∈ H) : (c.inr b : G) ∈ K' :=
  (c.mem_iff _).2 (by rwa [c.snd_inr])

include c in
/-- `K'` is normal in `K` when `H` is normal in `B`. -/
theorem normal [hH : H.Normal] : (K'.subgroupOf K).Normal where
  conj_mem k hk g := by
    rw [Subgroup.mem_subgroupOf, c.mem_iff] at hk ⊢
    simpa using hH.conj_mem _ hk (c.snd g)

variable {V : Type t} [AddCommGroup V] [Module R V] (ρ : Representation R A V)

/-- The coefficients `k' ↦ ρ (fst k')` on `K'`. -/
abbrev rep : Representation R K' V :=
  (ρ.comp c.fst).comp (Subgroup.inclusion c.le)

variable {ι : Γ →* G} {ρ}

/-- For `k : K` lying in `K'`, a form of level `K'` satisfies `f (g * k) = ρ (fst k)⁻¹ (f g)`. -/
theorem forms_apply_mul_of_mem (f : forms ι K' (c.rep ρ)) (g : G) {k : K} (hk : (k : G) ∈ K') :
    f.1 (g * k) = ρ (c.fst k)⁻¹ (f.1 g) := by
  rw [← map_inv c.fst]
  exact f.2.2 g ⟨k, hk⟩

/-- A form of level `K'` at `g * k`, `k : K`: `f (g * k) = ρ (fst k)⁻¹ (f (g * inr (snd k)))`. -/
theorem forms_apply_mul (f : forms ι K' (c.rep ρ)) (g : G) (k : K) :
    f.1 (g * k) = ρ (c.fst k)⁻¹ (f.1 (g * c.inr (c.snd k))) := by
  have hmem : (((c.inr (c.snd k))⁻¹ * k : K) : G) ∈ K' := c.mem_of_snd_eq_one (by simp)
  have h := c.forms_apply_mul_of_mem f (g * c.inr (c.snd k)) hmem
  rw [show g * (c.inr (c.snd k) : G) * (((c.inr (c.snd k))⁻¹ * k : K) : G) = g * k by
    simp [mul_assoc]] at h
  rw [h]
  simp

/-- A form of level `K'` at `g * inr (b * h)` with `h ∈ H` takes the value at `g * inr b`. -/
theorem forms_apply_mul_inr_mul (f : forms ι K' (c.rep ρ)) (g : G) (b : B) {h : B} (hh : h ∈ H) :
    f.1 (g * c.inr (b * h)) = f.1 (g * c.inr b) := by
  rw [map_mul, Subgroup.coe_mul, ← mul_assoc, c.forms_apply_mul_of_mem f _ (c.inr_mem hh)]
  simp

section Restriction

variable [hH : H.Normal]

/-- For `a⁻¹ * b ∈ H`, `f (y * (inr a)⁻¹) = f (y * (inr b)⁻¹)`; this uses normality of `H`. -/
theorem forms_apply_mul_inr_inv (f : forms ι K' (c.rep ρ)) (y : G) {a b : B} (hab : a⁻¹ * b ∈ H) :
    f.1 (y * ((c.inr a : K) : G)⁻¹) = f.1 (y * ((c.inr b : K) : G)⁻¹) := by
  have h' : a⁻¹ = b⁻¹ * (b * a⁻¹) := by group
  have hm : b * a⁻¹ ∈ H := by simpa [mul_assoc] using hH.conj_mem _ hab b
  rw [← Subgroup.coe_inv, ← map_inv, h', c.forms_apply_mul_inr_mul f y _ hm, map_inv,
    Subgroup.coe_inv]

/-- Restriction to the points `y * (inr b)⁻¹`: `f ↦ ([b] ↦ x ↦ f (x.out * (inr b)⁻¹))`. -/
def factorRestrict (f : forms ι K' (c.rep ρ)) (q : B ⧸ H) (x : DoubleCosets ι K) : V :=
  Quotient.liftOn' q (fun b => f.1 (x.out * ((c.inr b : K) : G)⁻¹)) fun _ _ hab =>
    c.forms_apply_mul_inr_inv f x.out (QuotientGroup.leftRel_apply.1 hab)

@[simp]
theorem factorRestrict_mk (f : forms ι K' (c.rep ρ)) (b : B) (x : DoubleCosets ι K) :
    c.factorRestrict f (b : B ⧸ H) x = f.1 (x.out * ((c.inr b : K) : G)⁻¹) :=
  rfl

end Restriction

variable (ρ) in
/-- The function `g ↦ ρ (fst k)⁻¹ (φ [(snd k)⁻¹] x)` on `G`, where `x` is the double coset of `g`
modulo `K` and `g = ι γ * x.out * k`. -/
def factorLift (φ : B ⧸ H → DoubleCosets ι K → V) (g : G) : V :=
  ρ (c.fst (outFactor ι K g))⁻¹
    (φ (((c.snd (outFactor ι K g))⁻¹ : B) : B ⧸ H) (DoubleCoset.mk ι.range K g))

variable (hΔ : ∀ g : G, doubleCosetStabilizer ι K g ≤ c.fst.ker ⊓ c.snd.ker)
include hΔ

/-- If the stabilizers of `K` lie in the kernels of `fst` and `snd`, the value of `factorLift`
at `ι γ * x.out * k` is `ρ (fst k)⁻¹ (φ [(snd k)⁻¹] x)` for every such decomposition. -/
theorem factorLift_eq (φ : B ⧸ H → DoubleCosets ι K → V) {g : G} {x : DoubleCosets ι K}
    (hx : DoubleCoset.mk ι.range K g = x) {γ : Γ} {k : K} (h : g = ι γ * x.out * k) :
    c.factorLift ρ φ g = ρ (c.fst k)⁻¹ (φ (((c.snd k)⁻¹ : B) : B ⧸ H) x) := by
  subst hx
  obtain ⟨γ', h'⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
  have hm := Subgroup.mem_inf.1 (hΔ _ (mul_inv_mem_doubleCosetStabilizer (h'.symm.trans h)))
  have h1 : c.fst k = c.fst (outFactor ι K g) := by
    have := hm.1
    rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at this
  have h2 : c.snd k = c.snd (outFactor ι K g) := by
    have := hm.2
    rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at this
  rw [h1, h2]
  rfl

theorem factorLift_mem [hH : H.Normal] (φ : B ⧸ H → DoubleCosets ι K → V) :
    c.factorLift ρ φ ∈ forms ι K' (c.rep ρ) := by
  refine ⟨fun γ₀ g => ?_, fun g k₀ => ?_⟩
  · obtain ⟨γ, h⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
    refine c.factorLift_eq hΔ φ
      (DoubleCoset.mk_mem_mul ⟨ι γ₀, MonoidHom.mem_range.2 ⟨γ₀, rfl⟩⟩ g) (γ := γ₀ * γ) ?_
    conv_lhs => rw [h]
    simp [mul_assoc]
  · obtain ⟨γ, h⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
    set k : K := Subgroup.inclusion c.le k₀
    have hk : (k : G) ∈ K' := k₀.2
    refine (c.factorLift_eq hΔ φ (DoubleCoset.mk_mul_mem k g) (γ := γ)
      (k := outFactor ι K g * k)
      (by rw [Subgroup.coe_mul, ← mul_assoc]; exact congrArg (· * (k : G)) h)).trans ?_
    have hq : (((c.snd (outFactor ι K g * k))⁻¹ : B) : B ⧸ H) =
        (((c.snd (outFactor ι K g))⁻¹ : B) : B ⧸ H) := by
      rw [QuotientGroup.eq, inv_inv, map_mul]
      exact hH.conj_mem _ ((c.mem_iff k).1 hk) (c.snd (outFactor ι K g))
    rw [hq, map_mul c.fst, mul_inv_rev, map_mul ρ, Module.End.mul_apply]
    change _ = ρ (c.fst k⁻¹) (ρ (c.fst (outFactor ι K g))⁻¹
      (φ (((c.snd (outFactor ι K g))⁻¹ : B) : B ⧸ H) (DoubleCoset.mk ι.range K g)))
    rw [map_inv c.fst]

variable [H.Normal]

/-- Harris's (4.8) in generic form: if the stabilizers of `K` lie in the kernels of `fst` and
`snd`, the forms of level `K'` with coefficients `ρ ∘ fst` are the functions
`B ⧸ H → DoubleCosets ι K → V`, by `f ↦ ([b] ↦ x ↦ f (x.out * (inr b)⁻¹))`. The inverse sends
`φ` to the form `ι γ * x.out * k ↦ ρ (fst k)⁻¹ (φ [(snd k)⁻¹] x)`. -/
def factorLinearEquiv : forms ι K' (c.rep ρ) ≃ₗ[R] (B ⧸ H → DoubleCosets ι K → V) where
  toFun f := c.factorRestrict f
  map_add' f f' := by
    funext q x
    induction q using QuotientGroup.induction_on
    rfl
  map_smul' r f := by
    funext q x
    induction q using QuotientGroup.induction_on
    rfl
  invFun φ := ⟨c.factorLift ρ φ, c.factorLift_mem hΔ φ⟩
  left_inv f := by
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨γ, h⟩ := exists_eq_mul_out_mul_outFactor (ι := ι) (K := K) g
    change ρ (c.fst (outFactor ι K g))⁻¹ (c.factorRestrict f
      (((c.snd (outFactor ι K g))⁻¹ : B) : B ⧸ H) (DoubleCoset.mk ι.range K g)) = f.1 g
    conv_rhs => rw [h, mul_assoc, f.2.1, c.forms_apply_mul f]
    rw [factorRestrict_mk]
    simp
  right_inv φ := by
    funext q x
    induction q using QuotientGroup.induction_on with
    | H b =>
      change c.factorLift ρ φ (x.out * ((c.inr b : K) : G)⁻¹) = φ b x
      refine (c.factorLift_eq hΔ φ ((DoubleCoset.mk_mul_mem (c.inr b)⁻¹ x.out).trans
        (DoubleCoset.out_eq' x)) (γ := 1) (k := (c.inr b)⁻¹) (by simp)).trans ?_
      simp

@[simp]
theorem factorLinearEquiv_apply_mk (f : forms ι K' (c.rep ρ)) (b : B) (x : DoubleCosets ι K) :
    c.factorLinearEquiv hΔ f (b : B ⧸ H) x = f.1 (x.out * ((c.inr b : K) : G)⁻¹) :=
  rfl

/-- The form attached to `φ` takes the value `ρ (fst k)⁻¹ (φ [(snd k)⁻¹] x)` at
`ι γ * x.out * k`. -/
theorem factorLinearEquiv_symm_apply_coe (φ : B ⧸ H → DoubleCosets ι K → V)
    (x : DoubleCosets ι K) (γ : Γ) (k : K) :
    ((c.factorLinearEquiv (ρ := ρ) hΔ).symm φ).1 (ι γ * x.out * k) =
      ρ (c.fst k)⁻¹ (φ (((c.snd k)⁻¹ : B) : B ⧸ H) x) := by
  exact c.factorLift_eq hΔ φ ((DoubleCoset.mk_mul_mem k _).trans
    ((DoubleCoset.mk_mem_mul ⟨ι γ, MonoidHom.mem_range.2 ⟨γ, rfl⟩⟩ x.out).trans
      (DoubleCoset.out_eq' x))) rfl

variable [(K'.subgroupOf K).Normal]

/-- `factorLinearEquiv` as an equivalence of representations of `K`: the level action
`(k • f) g = ρ (fst k) (f (g * k))` corresponds to `(k • φ) q = φ ((snd k)⁻¹ • q)`. -/
def factorEquiv :
    Representation.Equiv (levelAction ι (ρ.comp c.fst) c.le)
      ((Langlands.Induction.functionRepresentation
        (Representation.trivial R B (DoubleCosets ι K → V)) (B ⧸ H)).comp c.snd) :=
  .mk (c.factorLinearEquiv hΔ) fun k => by
    refine LinearMap.ext fun f => funext fun q => funext fun x => ?_
    induction q using QuotientGroup.induction_on with
    | H b =>
      change ρ (c.fst k) (f.1 (x.out * ((c.inr b : K) : G)⁻¹ * k)) =
        f.1 (x.out * ((c.inr ((c.snd k)⁻¹ * b) : K) : G)⁻¹)
      rw [show x.out * ((c.inr b : K) : G)⁻¹ * k = x.out * (((c.inr b)⁻¹ * k : K) : G) by
        simp [mul_assoc], c.forms_apply_mul f]
      simp only [map_mul, map_inv, fst_inr, snd_inr, inv_one, one_mul]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      simp

@[simp]
theorem factorEquiv_apply_mk (f : forms ι K' (c.rep ρ)) (b : B) (x : DoubleCosets ι K) :
    c.factorEquiv hΔ f (b : B ⧸ H) x = f.1 (x.out * ((c.inr b : K) : G)⁻¹) :=
  rfl

/-- `factorEquiv` followed by the duality between functions and group rings (the published
`permutationDualEquiv`): the level action on forms of level `K'` is the representation on
`Hom_R(R[B ⧸ H], DoubleCosets ι K → V)`, with `K` acting through `snd`. -/
def factorHomEquiv :
    Representation.Equiv (levelAction ι (ρ.comp c.fst) c.le)
      (((Langlands.Induction.permutation R B (B ⧸ H) R).linHom
        (Representation.trivial R B (DoubleCosets ι K → V))).comp c.snd) :=
  (c.factorEquiv hΔ).trans
    (.mk (Langlands.Induction.permutationDualEquiv
        (Representation.trivial R B (DoubleCosets ι K → V)) (B ⧸ H)).symm.toLinearEquiv fun k =>
      (Langlands.Induction.permutationDualEquiv
        (Representation.trivial R B (DoubleCosets ι K → V))
        (B ⧸ H)).symm.toIntertwiningMap.isIntertwining' (c.snd k))

/-- The linear map attached to a form `f` sends the basis vector `[b]` to the function
`x ↦ f (x.out * (inr b)⁻¹)`. -/
theorem factorHomEquiv_apply_single (f : forms ι K' (c.rep ρ)) (b : B) :
    c.factorHomEquiv hΔ f (Finsupp.single (b : B ⧸ H) 1) =
      fun x => f.1 (x.out * ((c.inr b : K) : G)⁻¹) := by
  change ((Langlands.Induction.permutationDualEquiv
    (Representation.trivial R B (DoubleCosets ι K → V)) (B ⧸ H)).symm (c.factorEquiv hΔ f))
    (Finsupp.single (b : B ⧸ H) 1) = _
  rw [← Langlands.Induction.permutationDualEquiv_apply
    (Representation.trivial R B (DoubleCosets ι K → V)) (B ⧸ H),
    Representation.Equiv.apply_symm_apply]
  rfl

omit [(K'.subgroupOf K).Normal] in
/-- Harris's right-hand side of (4.8) literally: the forms of level `K'` are the `R`-linear maps
from the free module `R[(B ⧸ H) × DoubleCosets ι K]` (a copy of `R[B ⧸ H]` for each double
coset) to `V`. -/
def factorFinsuppEquiv :
    forms ι K' (c.rep ρ) ≃ₗ[R] (((B ⧸ H) × DoubleCosets ι K →₀ R) →ₗ[R] V) :=
  (c.factorLinearEquiv hΔ).trans
    ((LinearEquiv.curry R V (B ⧸ H) (DoubleCosets ι K)).symm.trans (Finsupp.llift V R R _))

omit [(K'.subgroupOf K).Normal] in
theorem factorFinsuppEquiv_apply_single (f : forms ι K' (c.rep ρ)) (b : B)
    (x : DoubleCosets ι K) :
    c.factorFinsuppEquiv hΔ f (Finsupp.single ((b : B ⧸ H), x) 1) =
      f.1 (x.out * ((c.inr b : K) : G)⁻¹) := by
  simp [factorFinsuppEquiv]

end LevelFactorization

section Invariants

variable {K : Type uG} {A : Type uA} [Group K] [Group A] {W : Type t} [AddCommGroup W]
  [Module R W]

/-- If `τ` is trivial on `N` and every element of `K` is `s a * n` with `n ∈ N`, the invariants
of `τ ∘ s` are the invariants of `τ`. -/
theorem invariants_comp_eq (τ : Representation R K W) (s : A →* K) (N : Subgroup K)
    [Representation.IsTrivial (τ.comp N.subtype)] (h : ∀ k : K, ∃ a : A, ∃ n ∈ N, k = s a * n) :
    Representation.invariants (τ.comp s) = Representation.invariants τ := by
  ext w
  simp only [Representation.mem_invariants, MonoidHom.coe_comp, Function.comp_apply]
  refine ⟨fun hw k => ?_, fun hw a => hw (s a)⟩
  obtain ⟨a, n, hn, rfl⟩ := h k
  have hτ : τ n w = w := by
    have := Representation.IsTrivial.out (ρ := τ.comp N.subtype) ⟨n, hn⟩
    exact congrArg (· w) this
  rw [map_mul, Module.End.mul_apply, hτ, hw a]

end Invariants

end Langlands.Shimura.EquivariantForms
