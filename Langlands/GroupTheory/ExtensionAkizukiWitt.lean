import Langlands.GroupTheory.ExtensionPushout
import Mathlib.GroupTheory.Transfer

/-! # The Akizuki–Witt factor-extension cocycle and inflation -/

noncomputable section

namespace Langlands

universe u v

namespace NormalizedTwoCocycle

variable {G : Type v} {A : Type v} [Group G] [CommGroup A] [MulDistribMulAction G A]

/-- The pointwise power of a normalized cocycle. -/
def npow (c : NormalizedTwoCocycle G A) (n : ℕ) : NormalizedTwoCocycle G A where
  toFun gh := c gh ^ n
  cocycle g h j := by
    change c (g * h, j) ^ n * c (g, h) ^ n = g • c (h, j) ^ n * c (g, h * j) ^ n
    rw [← mul_pow, c.cocycle g h j, mul_pow, smul_pow']
  normalized := by
    rw [c.normalized, one_pow]

@[simp] theorem npow_apply (c : NormalizedTwoCocycle G A) (n : ℕ) (gh : G × G) :
    c.npow n gh = c gh ^ n := rfl

/-- The class of a pointwise power is the corresponding multiple of the class. -/
theorem cohomologyClass_npow (c : NormalizedTwoCocycle G A) (n : ℕ) :
    cohomologyClass (c.npow n) = n • cohomologyClass c := by
  have h : toCocycle₂ (c.npow n) = n • toCocycle₂ c := by
    apply Subtype.ext
    funext gh
    change Additive.ofMul (c gh ^ n) = _
    rw [ofMul_pow]
    rfl
  change groupCohomology.H2π _ (toCocycle₂ (c.npow n)) = _
  rw [h, map_nsmul]
  rfl

variable {Q : Type v} {B : Type v} [Group Q] [CommGroup B] [MulDistribMulAction Q B]

/-- Inflation of a normalized cocycle along `π : G → Q` and an equivariant
coefficient map `ι : B → A`. -/
def inflate (π : G →* Q) (ι : B →* A) (hι : ∀ g b, ι (π g • b) = g • ι b)
    (c : NormalizedTwoCocycle Q B) : NormalizedTwoCocycle G A where
  toFun gh := ι (c (π gh.1, π gh.2))
  cocycle g h j := by
    have he := congrArg ι (c.cocycle (π g) (π h) (π j))
    simpa only [map_mul, hι] using he
  normalized := by
    change ι (c (π 1, π 1)) = 1
    rw [map_one, c.normalized, map_one]

@[simp] theorem inflate_apply (π : G →* Q) (ι : B →* A) (hι : ∀ g b, ι (π g • b) = g • ι b)
    (c : NormalizedTwoCocycle Q B) (g h : G) :
    inflate π ι hι c (g, h) = ι (c (π g, π h)) := rfl

/-- Inflation respects equality of classes. -/
theorem cohomologyClass_inflate_congr (π : G →* Q) (ι : B →* A)
    (hι : ∀ g b, ι (π g • b) = g • ι b) {c d : NormalizedTwoCocycle Q B}
    (hcd : cohomologyClass c = cohomologyClass d) :
    cohomologyClass (inflate π ι hι c) = cohomologyClass (inflate π ι hι d) := by
  obtain ⟨b, hb⟩ := exists_cochain_of_cohomologyClass_eq hcd
  apply cohomologyClass_eq_of_cochain _ _ (fun g => ι (b (π g)))
  intro g h
  have he := congrArg ι (hb (π g) (π h))
  rw [map_mul, map_mul, map_mul, hι] at he
  change ι (c (π g, π h)) * ι (b (π (g * h))) =
    ι (b (π g)) * (g • ι (b (π h))) * ι (d (π g, π h))
  rw [map_mul π]
  exact he

end NormalizedTwoCocycle

namespace GroupExtensionPushout

section Algebra

variable {G : Type v} {A : Type v} [Group G] [CommGroup A] [MulDistribMulAction G A]
  (H : Subgroup G) [H.Normal] [Fintype H]

omit [Fintype H] in
/-- For `x⁻¹ y ∈ H` and `h ∈ H`, also `x⁻¹ h y ∈ H`. -/
theorem conj_mul_mem (x y : G) (hxy : x⁻¹ * y ∈ H) (h : G) (hh : h ∈ H) :
    x⁻¹ * h * y ∈ H := by
  have hc := (inferInstance : H.Normal).conj_mem _ hh x⁻¹
  have e : x⁻¹ * h * y = (x⁻¹ * h * x⁻¹⁻¹) * (x⁻¹ * y) := by group
  rw [e]
  exact H.mul_mem hc hxy

omit [Fintype H] in
/-- For `x⁻¹ y ∈ H` and `h ∈ H`, also `x h y⁻¹ ∈ H`. -/
theorem conj_mul_inv_mem (x y : G) (hxy : x⁻¹ * y ∈ H) (h : G) (hh : h ∈ H) :
    x * h * y⁻¹ ∈ H := by
  have h1 : y⁻¹ * x ∈ H := by
    have := H.inv_mem hxy
    rwa [mul_inv_rev, inv_inv] at this
  have hc := (inferInstance : H.Normal).conj_mem _ (H.mul_mem hh h1) x
  have e : x * h * y⁻¹ = x * (h * (y⁻¹ * x)) * x⁻¹ := by group
  rw [e]
  exact hc

omit [Fintype H] in
/-- The bijection `h ↦ x⁻¹ h y` of `H`, for `x⁻¹ y ∈ H`. -/
def conjMulEquiv (x y : G) (hxy : x⁻¹ * y ∈ H) : H ≃ H where
  toFun h := ⟨x⁻¹ * h * y, conj_mul_mem H x y hxy h h.property⟩
  invFun h := ⟨x * h * y⁻¹, conj_mul_inv_mem H x y hxy h h.property⟩
  left_inv h := by
    apply Subtype.ext
    change x * (x⁻¹ * h * y) * y⁻¹ = h
    group
  right_inv h := by
    apply Subtype.ext
    change x⁻¹ * (x * h * y⁻¹) * y = h
    group

/-- Reindex a product over `H` along `h ↦ x⁻¹ h y`, for `x⁻¹ y ∈ H`. -/
theorem prod_mul_right_eq_prod_mul_left {M : Type*} [CommMonoid M] (x y : G)
    (hxy : x⁻¹ * y ∈ H) (F : G → M) :
    ∏ h : H, F ((h : G) * y) = ∏ h : H, F (x * h) := by
  refine Fintype.prod_equiv (conjMulEquiv H x y hxy) _ _ ?_
  intro h
  change F (h * y) = F (x * (x⁻¹ * h * y))
  congr 1
  group

/-- Reindex a product over `H` by right multiplication by an element of `H`. -/
theorem prod_mul_right_mem {M : Type*} [CommMonoid M] (γ : G) (hγ : γ ∈ H) (F : G → M) :
    ∏ h : H, F ((h : G) * γ) = ∏ h : H, F h := by
  simpa only [one_mul] using
    prod_mul_right_eq_prod_mul_left H 1 γ (by simpa only [inv_one, one_mul] using hγ) F

variable (a : NormalizedTwoCocycle G A) (rep : G → G)

/-- The cochain `σ ↦ (∏_h a(h, rep σ)) / ∏_h a(σ, h)` of the Akizuki–Witt identity. -/
def akizukiWittCochain (σ : G) : A :=
  (∏ h : H, a ((h : G), rep σ)) / ∏ h : H, a (σ, (h : G))

/-- The cocycle identity of Artin–Tate XIII §3, Theorem 6, for the
inflated Akizuki–Witt cocycle. -/
theorem akizukiWitt_identity (hrep : ∀ σ, σ⁻¹ * rep σ ∈ H) (σ τ : G) :
    (∏ h : H, (h : G) • (a (rep σ, rep τ) * (a (rep σ * rep τ * (rep (σ * τ))⁻¹,
        rep (σ * τ)))⁻¹) * a ((h : G), rep σ * rep τ * (rep (σ * τ))⁻¹)) *
      akizukiWittCochain H a rep (σ * τ) =
    akizukiWittCochain H a rep σ * (σ • akizukiWittCochain H a rep τ) *
      a (σ, τ) ^ Fintype.card H := by
  set s := rep σ with hs
  set t := rep τ with ht
  set w := rep (σ * τ) with hw
  set γ := s * t * w⁻¹ with hγdef
  have hγw : γ * w = s * t := by rw [hγdef]; group
  have hγ : γ ∈ H := by
    have h1 := hrep σ
    have h2 := hrep τ
    have h3 := hrep (σ * τ)
    rw [← hs] at h1
    rw [← ht] at h2
    rw [← hw] at h3
    have e : γ = (σ * (σ⁻¹ * s) * σ⁻¹) * (σ * τ * (τ⁻¹ * t) * (σ * τ)⁻¹) *
        ((σ * τ) * ((σ * τ)⁻¹ * w)⁻¹ * (σ * τ)⁻¹) := by
      rw [hγdef]; group
    rw [e]
    exact H.mul_mem (H.mul_mem ((inferInstance : H.Normal).conj_mem _ h1 σ)
      ((inferInstance : H.Normal).conj_mem _ h2 (σ * τ)))
      ((inferInstance : H.Normal).conj_mem _ (H.inv_mem h3) (σ * τ))
  -- Step 1: each factor.
  have step1 : ∀ h : G, h • (a (s, t) * (a (γ, w))⁻¹) * a (h, γ) =
      a (h, s) * a (h * s, t) * (a (h * γ, w))⁻¹ := by
    intro h
    have c1 := a.cocycle h s t
    have c2 := a.cocycle h γ w
    rw [hγw] at c2
    rw [smul_mul', smul_inv']
    have e1 : h • a (s, t) = a (h * s, t) * a (h, s) * (a (h, s * t))⁻¹ := by
      rw [c1, mul_inv_cancel_right]
    have e2 : h • a (γ, w) = a (h * γ, w) * a (h, γ) * (a (h, s * t))⁻¹ := by
      rw [c2, mul_inv_cancel_right]
    rw [e1, e2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  -- Step 2: reindex the three products.
  have step2 : ∀ h : G, a (σ * h, t) =
      σ • a (h, t) * a (σ, h * t) * (a (σ, h))⁻¹ := by
    intro h
    have c3 := a.cocycle σ h t
    rw [← c3, mul_inv_cancel_right]
  have step3 : ∀ h : G, a (σ, τ * h) =
      a (σ * τ, h) * a (σ, τ) * (σ • a (τ, h))⁻¹ := by
    intro h
    have c4 := a.cocycle σ τ h
    rw [c4, mul_comm (σ • a (τ, h)), mul_assoc, mul_inv_cancel, mul_one]
  have hP : ∏ h : H, (h : G) • (a (s, t) * (a (γ, w))⁻¹) * a ((h : G), γ) =
      (∏ h : H, a ((h : G), s)) *
        ((∏ h : H, σ • a ((h : G), t)) *
          ((∏ h : H, a (σ * τ, (h : G))) * a (σ, τ) ^ Fintype.card H /
            ∏ h : H, σ • a (τ, (h : G))) /
          ∏ h : H, a (σ, (h : G))) /
        ∏ h : H, a ((h : G), w) := by
    have r0 : ∏ h : H, (h : G) • (a (s, t) * (a (γ, w))⁻¹) * a ((h : G), γ) =
        ∏ h : H, a ((h : G), s) * a ((h : G) * s, t) * (a ((h : G) * γ, w))⁻¹ :=
      Finset.prod_congr rfl (fun h _ => step1 h)
    have r1 : ∏ h : H, a ((h : G) * γ, w) = ∏ h : H, a ((h : G), w) :=
      prod_mul_right_mem H γ hγ (fun g => a (g, w))
    have r2 : ∏ h : H, a ((h : G) * s, t) = ∏ h : H, a (σ * h, t) :=
      prod_mul_right_eq_prod_mul_left H σ s (hrep σ) (fun g => a (g, t))
    have r3 : ∏ h : H, a (σ * h, t) =
        ∏ h : H, σ • a ((h : G), t) * a (σ, (h : G) * t) * (a (σ, (h : G)))⁻¹ :=
      Finset.prod_congr rfl (fun h _ => step2 h)
    have r4 : ∏ h : H, a (σ, (h : G) * t) = ∏ h : H, a (σ, τ * h) :=
      prod_mul_right_eq_prod_mul_left H τ t (hrep τ) (fun g => a (σ, g))
    have r5 : ∏ h : H, a (σ, τ * h) =
        ∏ h : H, a (σ * τ, (h : G)) * a (σ, τ) * (σ • a (τ, (h : G)))⁻¹ :=
      Finset.prod_congr rfl (fun h _ => step3 h)
    rw [r0, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, r1, r2,
      r3, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, r4, r5,
      Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      Finset.prod_const, Finset.card_univ]
    simp only [div_eq_mul_inv]
  rw [hP]
  unfold akizukiWittCochain
  rw [smul_div', Finset.smul_prod', Finset.smul_prod']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

end Algebra

section Pushout

variable {W : Type u} {G : Type v} {A : Type v} [Group W] [Group G] [CommGroup A]
  [MulDistribMulAction G A]
  {Q : Type v} {B : Type v} [Group Q] [CommGroup B] [MulDistribMulAction Q B]
  {q : W →* G} (π : G →* Q)

/-- A normalized section of `π ∘ q` built from normalized sections of `q` and `π`. -/
def Section.lift (t : Section q) (σ : Section π) : Section (π.comp q) where
  toFun ρ := t (σ ρ)
  right_inv ρ := by simp
  normalized := by simp

@[simp] theorem Section.lift_apply (t : Section q) (σ : Section π) (ρ : Q) :
    t.lift π σ ρ = t (σ ρ) := rfl

/-- The kernel element `t(h) x t(h q(x))⁻¹` of the coset-product transfer from
`(π ∘ q)⁻¹(1)` to `q⁻¹(1)`, for `h` in the kernel of `π`. -/
def transferKernel (t : Section q) (x : (π.comp q).ker) (h : π.ker) : q.ker :=
  ⟨t h * x * (t (h * q x))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, Section.map_apply, Section.map_apply,
      mul_inv_cancel]⟩

@[simp] theorem transferKernel_coe (t : Section q) (x : (π.comp q).ker) (h : π.ker) :
    (transferKernel π t x h : W) = t h * x * (t (h * q x))⁻¹ := rfl

/-- The transfer kernel element of a factor-set element, in kernel coordinates
(Artin–Tate XIII §3, the computation before Theorem 5). -/
theorem transferKernel_factorKernel (t : Section q) (σ : Section π) (ρ ρ' : Q)
    (h : π.ker) :
    transferKernel π t ((t.lift π σ).factorKernel ρ ρ') h =
      conjugateKernel q (t h) (t.factorKernel (σ ρ) (σ ρ') *
          (t.factorKernel (σ ρ * σ ρ' * (σ (ρ * ρ'))⁻¹) (σ (ρ * ρ')))⁻¹) *
        t.factorKernel h (σ ρ * σ ρ' * (σ (ρ * ρ'))⁻¹) := by
  apply Subtype.ext
  have hq : q (((t.lift π σ).factorKernel ρ ρ' : (π.comp q).ker) : W) =
      σ ρ * σ ρ' * (σ (ρ * ρ'))⁻¹ := by
    change q (t (σ ρ) * t (σ ρ') * (t (σ (ρ * ρ')))⁻¹) = _
    rw [map_mul, map_mul, map_inv, Section.map_apply, Section.map_apply, Section.map_apply]
  have hγ : σ ρ * σ ρ' * (σ (ρ * ρ'))⁻¹ * σ (ρ * ρ') = σ ρ * σ ρ' := by group
  rw [transferKernel_coe, hq]
  change t h * (t (σ ρ) * t (σ ρ') * (t (σ (ρ * ρ')))⁻¹) *
      (t (h * (σ ρ * σ ρ' * (σ (ρ * ρ'))⁻¹)))⁻¹ =
    t h * ((t (σ ρ) * t (σ ρ') * (t (σ ρ * σ ρ'))⁻¹) *
        (t (σ ρ * σ ρ' * (σ (ρ * ρ'))⁻¹) * t (σ (ρ * ρ')) *
          (t (σ ρ * σ ρ' * (σ (ρ * ρ'))⁻¹ * σ (ρ * ρ')))⁻¹)⁻¹) * (t h)⁻¹ *
      (t h * t (σ ρ * σ ρ' * (σ (ρ * ρ'))⁻¹) *
        (t (h * (σ ρ * σ ρ' * (σ (ρ * ρ'))⁻¹)))⁻¹)
  rw [hγ]
  group

variable (t : Section q) (r : q.ker →* A)
  (hr : ∀ (x : W) (n : q.ker), r (conjugateKernel q x n) = q x • r n)

/-- The transfer kernel values of the factor set, written with the cocycle of `t`
(Artin–Tate XIII §3, Theorem 5). -/
theorem kernelMap_transferKernel_factorKernel (σ : Section π) (ρ ρ' : Q) (h : π.ker) :
    r (transferKernel π t ((t.lift π σ).factorKernel ρ ρ') h) =
      (h : G) • (t.cocycle r hr (σ ρ, σ ρ') *
          (t.cocycle r hr (σ ρ * σ ρ' * (σ (ρ * ρ'))⁻¹, σ (ρ * ρ')))⁻¹) *
        t.cocycle r hr ((h : G), σ ρ * σ ρ' * (σ (ρ * ρ'))⁻¹) := by
  rw [transferKernel_factorKernel, map_mul, hr, Section.map_apply, map_mul, map_inv]
  rfl

/-- **Akizuki–Witt inflation.** Let the kernel map `r'` of `π ∘ q` be the
coset-product transfer of `r`, followed by an equivariant map `ι`. Then inflating
the factor-extension class along `π` and `ι` gives `[ker π : 1]` times the class of
`q` (Artin–Tate XIII §3, Theorems 5 and 6). -/
theorem cohomologyClass_inflate_pushout [Fintype π.ker] (hπ : Function.Surjective π)
    (ι : B →* A) (hι : ∀ g b, ι (π g • b) = g • ι b)
    (s : Section (π.comp q)) (r' : (π.comp q).ker →* B)
    (hr' : ∀ (x : W) (n : (π.comp q).ker),
      r' (conjugateKernel (π.comp q) x n) = (π.comp q) x • r' n)
    (hV : ∀ x : (π.comp q).ker, ι (r' x) = ∏ h : π.ker, r (transferKernel π t x h)) :
    NormalizedTwoCocycle.cohomologyClass
        (NormalizedTwoCocycle.inflate π ι hι (s.cocycle r' hr')) =
      Fintype.card π.ker • NormalizedTwoCocycle.cohomologyClass (t.cocycle r hr) := by
  let σ := Section.ofSurjective hπ
  rw [NormalizedTwoCocycle.cohomologyClass_inflate_congr π ι hι
      (s.cohomologyClass_eq r' hr' (t.lift π σ)),
    ← NormalizedTwoCocycle.cohomologyClass_npow]
  have hrep : ∀ x : G, x⁻¹ * σ (π x) ∈ π.ker := by
    intro x
    rw [MonoidHom.mem_ker, map_mul, map_inv, Section.map_apply, inv_mul_cancel]
  apply NormalizedTwoCocycle.cohomologyClass_eq_of_cochain _ _
    (akizukiWittCochain π.ker (t.cocycle r hr) (fun x => σ (π x)))
  intro g g'
  have hid := akizukiWitt_identity π.ker (t.cocycle r hr) (fun x => σ (π x)) hrep g g'
  simp only [map_mul] at hid
  change ι (r' ((t.lift π σ).factorKernel (π g) (π g'))) * _ = _
  rw [hV, NormalizedTwoCocycle.npow_apply]
  simp only [kernelMap_transferKernel_factorKernel π t r hr σ]
  exact hid

end Pushout

section Transfer

variable {N : Type*} [Group N] {K : Subgroup N} {M : Type*} [CommGroup M]
  {P : Type*} [Group P] [Fintype P]

/-- Mathlib's coset-product transfer to the kernel `K` of `p : N → P`, computed
with an arbitrary section `tp` of `p`:
`transfer ϕ x = ∏_h ϕ(tp(h) x tp(h p(x))⁻¹)`. -/
theorem transfer_eq_prod_section [K.FiniteIndex] (ϕ : K →* M) (p : N →* P)
    (hpK : p.ker = K) (tp : P → N) (htp : ∀ h, p (tp h) = h) (x : N) :
    ϕ.transfer x = ∏ h : P, ϕ ⟨tp h * x * (tp (h * p x))⁻¹, by
      rw [← hpK, MonoidHom.mem_ker, map_mul, map_mul, map_inv, htp, htp, mul_inv_cancel]⟩ := by
  classical
  have hmk : ∀ a b : N, (a : N ⧸ K) = b ↔ p a = p b := by
    intro a b
    rw [QuotientGroup.eq, ← hpK, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
  let f : N ⧸ K → N := fun c => (tp (p (Quotient.out c))⁻¹)⁻¹
  have hpf : ∀ c, p (f c) = p (Quotient.out c) := by
    intro c
    change p (tp (p (Quotient.out c))⁻¹)⁻¹ = _
    rw [map_inv, htp, inv_inv]
  have hf : ∀ c : N ⧸ K, ((f c : N) : N ⧸ K) = c := by
    intro c
    conv_rhs => rw [← QuotientGroup.out_eq' c]
    exact (hmk _ _).2 (hpf c)
  let T : K.LeftTransversal := ⟨Set.range f, Subgroup.isComplement_range_left hf⟩
  have hT : ∀ c, (T.2.leftQuotientEquiv c : N) = f c :=
    Subgroup.IsComplement.leftQuotientEquiv_apply hf
  have hsurj : Function.Surjective p := fun h => ⟨tp h, htp h⟩
  let e : N ⧸ K ≃ P :=
    { toFun := fun c => (p (Quotient.out c))⁻¹
      invFun := fun h => ((tp h⁻¹ : N) : N ⧸ K)
      left_inv := fun c => by
        change ((tp (p (Quotient.out c))⁻¹⁻¹ : N) : N ⧸ K) = c
        conv_rhs => rw [← QuotientGroup.out_eq' c]
        rw [inv_inv]
        exact (hmk _ _).2 (htp _)
      right_inv := fun h => by
        change (p (Quotient.out ((tp h⁻¹ : N) : N ⧸ K)))⁻¹ = h
        have := (hmk (Quotient.out ((tp h⁻¹ : N) : N ⧸ K)) (tp h⁻¹)).1
          (QuotientGroup.out_eq' _)
        rw [this, htp, inv_inv] }
  let := K.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_def ϕ T x]
  unfold Subgroup.leftTransversals.diff
  refine Fintype.prod_equiv e _ _ ?_
  intro c
  congr 1
  apply Subtype.ext
  change (T.2.leftQuotientEquiv c : N)⁻¹ * ((x • T).2.leftQuotientEquiv c : N) = _
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, hT, hT, smul_eq_mul]
  have hc : p (Quotient.out (x⁻¹ • c)) = (p x)⁻¹ * p (Quotient.out c) := by
    have h1 : ((x⁻¹ * Quotient.out c : N) : N ⧸ K) = x⁻¹ • c := by
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rfl
    have := (hmk _ _).1 ((QuotientGroup.out_eq' (x⁻¹ • c)).trans h1.symm)
    rw [this, map_mul, map_inv]
  change (tp (p (Quotient.out c))⁻¹)⁻¹⁻¹ * (x * (tp (p (Quotient.out (x⁻¹ • c)))⁻¹)⁻¹) =
    tp (p (Quotient.out c))⁻¹ * x * (tp ((p (Quotient.out c))⁻¹ * p x))⁻¹
  rw [hc, mul_inv_rev, inv_inv, inv_inv, mul_assoc]

end Transfer

end GroupExtensionPushout

end Langlands
