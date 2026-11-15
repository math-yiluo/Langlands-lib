import Mathlib

/-! # Lifting field maps in characteristic `p` along square-zero extensions

A field `K` of characteristic `p > 0` is formally smooth over `𝔽_p`. We prove the consequence
used in Stacks, Smoothing Ring Maps, Lemma 16.11.1 (07FG): ring maps `K → B ⧸ J` with `J² = 0`
and `p = 0` in `B` lift to `B`. -/

namespace Langlands.CommutativeAlgebra.Popescu.ArtinianFlat

open Polynomial IntermediateField

section Lifts

variable {E K B : Type*} [Field E] [Field K] [Algebra E K] [CommRing B] [Algebra E B]
  {J : Ideal B} {g : K →ₐ[E] B ⧸ J}

variable (J g) in
/-- Partial lifts of `g : K → B ⧸ J` to `B`, defined on intermediate fields of `K / E`. -/
structure SqLift where
  /-- The domain of the partial lift. -/
  carrier : IntermediateField E K
  /-- The partial lift. -/
  emb : carrier →ₐ[E] B
  /-- It lifts `g`. -/
  comm : ∀ x : carrier, Ideal.Quotient.mk J (emb x) = g x

namespace SqLift

instance : PartialOrder (SqLift J g) where
  le L₁ L₂ := ∃ h : L₁.carrier ≤ L₂.carrier, ∀ x, L₂.emb (inclusion h x) = L₁.emb x
  le_refl L := ⟨le_rfl, fun _ ↦ rfl⟩
  le_trans L₁ L₂ L₃ := by
    rintro ⟨h₁₂, h₁₂'⟩ ⟨h₂₃, h₂₃'⟩
    refine ⟨h₁₂.trans h₂₃, fun _ ↦ ?_⟩
    rw [← inclusion_inclusion h₁₂ h₂₃, h₂₃', h₁₂']
  le_antisymm := by
    rintro ⟨L₁, e₁, c₁⟩ ⟨L₂, e₂, c₂⟩ ⟨h₁₂, h₁₂'⟩ ⟨h₂₁, h₂₁'⟩
    obtain rfl : L₁ = L₂ := h₁₂.antisymm h₂₁
    obtain rfl : e₁ = e₂ := AlgHom.ext h₂₁'
    rfl

noncomputable instance : OrderBot (SqLift J g) where
  bot := ⟨⊥, (Algebra.ofId E B).comp (botEquiv E K), fun x ↦ by
    obtain ⟨x, rfl⟩ := (botEquiv E K).symm.surjective x
    simp only [botEquiv_symm, AlgHom.commutes, Ideal.Quotient.mk_algebraMap]
    exact (g.commutes x).symm⟩
  bot_le L := ⟨bot_le, fun x ↦ by
    obtain ⟨x, rfl⟩ := (botEquiv E K).symm.surjective x
    simp_rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact L.emb.commutes x⟩

noncomputable instance : Nonempty (SqLift J g) := ⟨⊥⟩

section Chain

variable (c : Set (SqLift J g)) (hc : IsChain (· ≤ ·) c)

theorem directed_carrier (hc : IsChain (· ≤ ·) c) : Directed (· ≤ ·) (fun i : c ↦ i.1.carrier) :=
  hc.directedOn.directed_val.mono_comp _ fun _ _ h ↦ h.1

/-- The union of a nonempty chain of partial lifts. -/
noncomputable def union [Nonempty c] : SqLift J g :=
  let t (i : c) := i.val.carrier
  have dir : Directed (· ≤ ·) t := directed_carrier c hc
  have dir' : Directed (· ≤ ·) (fun i ↦ (t i).toSubalgebra) := dir
  have hf : ∀ (i j : c) (h : (t i).toSubalgebra ≤ (t j).toSubalgebra),
      i.val.emb = j.val.emb.comp (Subalgebra.inclusion h) := fun i j h ↦
    AlgHom.ext fun x ↦ (hc.total i.2 j.2).elim (fun hij ↦ (hij.snd x).symm) fun hji ↦ by
      rw [AlgHom.comp_apply, ← inclusion]
      rw [← hji.snd (inclusion h x), inclusion_inclusion, inclusion_self, AlgHom.id_apply x]
  { carrier := iSup t
    emb := (Subalgebra.iSupLift (toSubalgebra <| t ·) dir' (·.val.emb) hf _ le_rfl).comp
      (Subalgebra.equivOfEq _ _ <| toSubalgebra_iSup_of_directed dir)
    comm := fun x ↦ by
      have hx := x.2
      rw [← SetLike.mem_coe, coe_iSup_of_directed dir, Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      have h1 := Subalgebra.iSupLift_of_mem (fun i ↦ (t i).toSubalgebra) (dir := dir')
        (f := fun i ↦ i.val.emb) (hf := hf) (hT := le_rfl)
        (Subalgebra.equivOfEq _ _ (toSubalgebra_iSup_of_directed dir) x) hi
      exact (congrArg (Ideal.Quotient.mk J) h1).trans (i.1.comm ⟨x, hi⟩) }

set_option backward.isDefEq.respectTransparency false in
theorem le_union [Nonempty c] ⦃σ : SqLift J g⦄ (hσ : σ ∈ c) : σ ≤ union c hc :=
  let t (i : c) := i.val.carrier
  ⟨le_iSup t ⟨σ, hσ⟩, fun x ↦ by
    dsimp only [union, AlgHom.comp_apply]
    exact Subalgebra.iSupLift_inclusion (K := (toSubalgebra <| t ·))
      (i := ⟨σ, hσ⟩) x (le_iSup (toSubalgebra <| t ·) ⟨σ, hσ⟩)⟩

end Chain

/-- A partial lift extends to `carrier⟮s⟯` once `s` has a lift `y` which is a root of the
minimal polynomial of `s` over the carrier. -/
theorem exists_ge_of_adjoin (x : SqLift J g) {s : K} (h1 : IsIntegral x.carrier s) (y : B)
    (hy : (minpoly x.carrier s).eval₂ (x.emb : x.carrier →+* B) y = 0)
    (hyg : Ideal.Quotient.mk J y = g s) : ∃ z : SqLift J g, x ≤ z ∧ s ∈ z.carrier := by
  letI : Algebra x.carrier B := (x.emb : x.carrier →+* B).toAlgebra
  haveI : IsScalarTower E x.carrier B :=
    IsScalarTower.of_algebraMap_eq fun e ↦ (x.emb.commutes e).symm
  let pb := adjoin.powerBasis h1
  have hy' : aeval y (minpoly x.carrier pb.gen) = 0 := by
    rw [adjoin.powerBasis_gen, minpoly_gen, aeval_def]
    exact hy
  let φ : x.carrier⟮s⟯ →ₐ[x.carrier] B := pb.lift y hy'
  let ψ₂ : x.carrier⟮s⟯ →ₐ[x.carrier] B ⧸ J :=
    { toRingHom := (g : K →+* B ⧸ J).comp (algebraMap x.carrier⟮s⟯ K)
      commutes' := fun c ↦ (x.comm c).symm }
  have hφψ : (Ideal.Quotient.mkₐ x.carrier J).comp φ = ψ₂ := by
    refine pb.algHom_ext ?_
    rw [AlgHom.comp_apply, PowerBasis.lift_gen]
    exact hyg
  refine ⟨⟨x.carrier⟮s⟯.restrictScalars E, φ.restrictScalars E, fun w ↦ ?_⟩,
    ⟨fun z hz ↦ IntermediateField.algebraMap_mem x.carrier⟮s⟯ ⟨z, hz⟩, φ.commutes⟩,
    mem_adjoin_simple_self x.carrier s⟩
  exact AlgHom.congr_fun hφψ w

end SqLift

end Lifts

section Frobenius

variable {K B : Type*} [Field K] [CommRing B] {p : ℕ} [hp : Fact p.Prime] [CharP K p] [CharP B p]
  {J : Ideal B}

theorem pow_eq_pow_of_sub_mem (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = 0) {a b : B} (h : a - b ∈ J) :
    a ^ p = b ^ p := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  have hab : a = b + (a - b) := by ring
  have hi : (a - b) ^ p = 0 := by
    rw [hq, pow_succ, pow_succ, mul_assoc, hJ _ h _ h, mul_zero]
  rw [hab, add_pow_char, hi, add_zero]

variable (p) in
/-- `x ↦ (lift of g x) ^ p`: a ring map `K → B` lifting `g ∘ Frobenius`. -/
noncomputable def frobLift (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = 0) (g : K →+* B ⧸ J) : K →+* B :=
  let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := J))
  have hs (y : B ⧸ J) : Ideal.Quotient.mk J (s y) = y :=
    Function.surjInv_eq Ideal.Quotient.mk_surjective y
  have key (x : K) (a : B) (ha : Ideal.Quotient.mk J a = g x) : s (g x) ^ p = a ^ p :=
    pow_eq_pow_of_sub_mem hJ (Ideal.Quotient.eq.mp (by rw [hs, ha]))
  { toFun := fun x ↦ s (g x) ^ p
    map_one' := by
      rw [key 1 1 (by rw [map_one, map_one]), one_pow]
    map_mul' := fun x y ↦ by
      rw [key (x * y) (s (g x) * s (g y)) (by rw [map_mul, hs, hs, map_mul]), mul_pow]
    map_zero' := by
      rw [key 0 0 (by rw [map_zero, map_zero]), zero_pow hp.out.ne_zero]
    map_add' := fun x y ↦ by
      rw [key (x + y) (s (g x) + s (g y)) (by rw [map_add, hs, hs, map_add]), add_pow_char] }

omit [CharP K p] in
theorem frobLift_apply (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = 0) (g : K →+* B ⧸ J) (x : K) (a : B)
    (ha : Ideal.Quotient.mk J a = g x) : frobLift p hJ g x = a ^ p := by
  have hs : Ideal.Quotient.mk J
      (Function.surjInv (Ideal.Quotient.mk_surjective (I := J)) (g x)) = g x :=
    Function.surjInv_eq Ideal.Quotient.mk_surjective _
  exact pow_eq_pow_of_sub_mem hJ (Ideal.Quotient.eq.mp (by rw [hs, ha]))

theorem mk_frobLift (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = 0) (g : K →+* B ⧸ J) (x : K) :
    Ideal.Quotient.mk J (frobLift p hJ g x) = g (x ^ p) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (g x)
  rw [frobLift_apply hJ g x a ha, map_pow, ha, map_pow]

variable (p) in
/-- Frobenius as an isomorphism of `K` onto the subfield `K ^ p`. -/
noncomputable def frobEquiv : K ≃+* (frobenius K p).fieldRange :=
  RingEquiv.ofBijective (frobenius K p).rangeRestrictField
    ⟨fun _ _ h ↦ (frobenius K p).injective (congrArg Subtype.val h),
      fun ⟨_, x, hx⟩ ↦ ⟨x, Subtype.ext hx⟩⟩

theorem coe_frobEquiv (x : K) : ((frobEquiv p x : (frobenius K p).fieldRange) : K) = x ^ p := rfl

/-- Lifting along a square-zero ideal in characteristic `p`, quotient form. -/
theorem exists_lift_of_sq_zero_aux (p : ℕ) [hp : Fact p.Prime] [CharP K p] [CharP B p]
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = 0) (g : K →+* B ⧸ J) :
    ∃ f : K →+* B, (Ideal.Quotient.mk J).comp f = g := by
  let E := (frobenius K p).fieldRange
  let ρ : E →+* B := (frobLift p hJ g).comp (frobEquiv p).symm.toRingHom
  letI : Algebra E B := ρ.toAlgebra
  have hρ (x : K) : algebraMap E B (frobEquiv p x) = frobLift p hJ g x := by
    show frobLift p hJ g ((frobEquiv p).symm (frobEquiv p x)) = _
    rw [RingEquiv.symm_apply_apply]
  let gE : K →ₐ[E] B ⧸ J :=
    { toRingHom := g
      commutes' := fun e ↦ by
        obtain ⟨x, rfl⟩ := (frobEquiv p).surjective e
        show g ((frobEquiv p x : E) : K) = Ideal.Quotient.mk J (algebraMap E B (frobEquiv p x))
        rw [hρ, mk_frobLift, coe_frobEquiv] }
  obtain ⟨φ, hφ⟩ := zorn_le_nonempty (α := SqLift J gE) fun c hc hne ↦ by
    haveI : Nonempty c := hne.to_subtype
    exact ⟨SqLift.union c hc, fun σ hσ ↦ SqLift.le_union c hc hσ⟩
  have htop : φ.carrier = ⊤ := by
    by_contra hne
    obtain ⟨α, -, hα⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
    let c : φ.carrier := algebraMap E φ.carrier (frobEquiv p α)
    have hc : (c : K) = α ^ p := coe_frobEquiv α
    have hirr : Irreducible (X ^ p - C c) := by
      refine X_pow_sub_C_irreducible_of_prime hp.out fun b hb ↦ hα ?_
      have hb' : (b : K) ^ p = α ^ p := by
        have := congrArg (fun w : φ.carrier ↦ (w : K)) hb
        simpa [hc] using this
      have : (b : K) = α := frobenius_inj K p hb'
      exact this ▸ b.2
    have hmon : (X ^ p - C c).Monic := monic_X_pow_sub_C c hp.out.ne_zero
    have hroot : aeval α (X ^ p - C c) = 0 := by
      rw [map_sub, map_pow, aeval_X, aeval_C, IntermediateField.algebraMap_apply, hc, sub_self]
    have hint : IsIntegral φ.carrier α := ⟨_, hmon, hroot⟩
    have hmin : minpoly φ.carrier α = X ^ p - C c :=
      (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (g α)
    obtain ⟨z, hz, hαz⟩ := φ.exists_ge_of_adjoin hint y (by
      rw [hmin, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero]
      show y ^ p = φ.emb (algebraMap E φ.carrier (frobEquiv p α))
      rw [φ.emb.commutes, hρ, frobLift_apply hJ g α y hy]) hy
    exact hα ((hφ hz).1 hαz)
  let e : φ.carrier ≃ₐ[E] K := (equivOfEq htop).trans topEquiv
  refine ⟨(φ.emb.comp e.symm.toAlgHom).toRingHom, RingHom.ext fun x ↦ ?_⟩
  have h1 := φ.comm (e.symm x)
  have h2 : ((e.symm x : φ.carrier) : K) = x := e.apply_symm_apply x
  rw [h2] at h1
  exact h1

/-- Lifting along a surjection with square-zero kernel, for fields of characteristic `p`. -/
theorem exists_lift_of_sq_zero (p : ℕ) [Fact p.Prime] [CharP K p] [CharP B p] {B' : Type*} [CommRing B'] (f : B →+* B')
    (hf : Function.Surjective f) (hsq : ∀ a b, f a = 0 → f b = 0 → a * b = 0)
    (g : K →+* B') : ∃ G : K →+* B, f.comp G = g := by
  let e := RingHom.quotientKerEquivOfSurjective hf
  obtain ⟨G, hG⟩ := exists_lift_of_sq_zero_aux p (J := RingHom.ker f)
    (fun a ha b hb ↦ hsq a b ha hb) (e.symm.toRingHom.comp g)
  refine ⟨G, RingHom.ext fun x ↦ ?_⟩
  have := congrArg e (RingHom.congr_fun hG x)
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply] at this
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk] at this
  exact this

end Frobenius

end Langlands.CommutativeAlgebra.Popescu.ArtinianFlat
