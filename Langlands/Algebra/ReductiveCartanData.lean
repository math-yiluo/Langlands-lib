import Langlands.Algebra.WeylCompleteReducibility
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # A Cartan subalgebra through an integral grading element of a reductive Lie algebra -/

noncomputable section

universe v

set_option autoImplicit false

namespace Langlands.Algebra.ReductiveCartanData

open LieAlgebra LieModule Module

variable {g : Type v} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]

section Complement

variable (hred : radical ℂ g = center ℂ g)

include hred in
/-- The centre of a reductive Lie algebra has a complementary ideal. -/
theorem exists_isCompl_center : ∃ s : LieIdeal ℂ g, IsCompl (center ℂ g) s := by
  have : HasCentralRadical ℂ g := ⟨hred⟩
  refine WeylCompleteReducibility.exists_isCompl (M := g) (fun z hz => ?_) (center ℂ g)
  have h0 : toEnd ℂ g g z = 0 := by
    ext y
    have h := (mem_maxTrivSubmodule ℂ g g z).mp hz y
    change ⁅z, y⁆ = 0
    rw [← lie_skew, h, neg_zero]
  rw [h0]
  exact Module.End.isSemisimple_zero

variable {s : LieIdeal ℂ g} (hs : IsCompl (center ℂ g) s)

omit [FiniteDimensional ℂ g] in
include hs in
theorem isCompl_toSubmodule : IsCompl (center ℂ g : Submodule ℂ g) (s : Submodule ℂ g) := by
  rwa [← LieSubmodule.isCompl_toSubmodule] at hs

include hred hs in
/-- The Killing form of `g` vanishes on `x ∈ s` only when `x = 0`. -/
theorem eq_zero_of_killingForm (x : g) (hx : x ∈ s) (h : ∀ y ∈ s, killingForm ℂ g x y = 0) :
    x = 0 := by
  have hc : ∀ c ∈ center ℂ g, killingForm ℂ g x c = 0 := by
    intro c hc
    have := WeylCompleteReducibility.center_le_killingCompl_top (k := ℂ) (L := g) hc
    rw [LieIdeal.mem_killingCompl] at this
    exact this x (LieSubmodule.mem_top x)
  have hall : x ∈ LieIdeal.killingCompl ℂ g ⊤ := by
    rw [LieIdeal.mem_killingCompl]
    intro y _
    obtain ⟨c, hc', t, ht', rfl⟩ := Submodule.mem_sup.mp
      ((isCompl_toSubmodule hs).sup_eq_top ▸ Submodule.mem_top : y ∈ _)
    rw [LieModule.traceForm_comm, map_add, hc c hc', h t ht', add_zero]
  have hxc : x ∈ center ℂ g := hred ▸ killingCompl_top_le_radical ℂ g hall
  have hd := (isCompl_toSubmodule hs).disjoint
  exact (Submodule.disjoint_def.mp hd) x hxc hx

include hred hs in
/-- The complement of the centre has nondegenerate Killing form. -/
theorem isKilling_complement : IsKilling ℂ s := by
  refine ⟨?_⟩
  rw [eq_bot_iff]
  intro x hx
  rw [LieIdeal.mem_killingCompl] at hx
  rw [LieSubmodule.mem_bot]
  have h := eq_zero_of_killingForm hred hs x.1 x.2 fun y hy => by
    have := hx ⟨y, hy⟩ (LieSubmodule.mem_top _)
    rw [LieIdeal.killingForm_eq] at this
    have h' : killingForm ℂ g y x = 0 := this
    rw [LieModule.traceForm_comm]
    exact h'
  exact Subtype.ext h

end Complement

section Eigenbasis

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- An endomorphism diagonal in some basis kills every vector killed by one of its powers. -/
theorem apply_eq_zero_of_pow_apply_eq_zero {ι : Type*} (b : Basis ι K V) (f : V →ₗ[K] V)
    (μ : ι → K) (hf : ∀ a, f (b a) = μ a • b a) (y : V) (n : ℕ) (h : (f ^ n) y = 0) :
    f y = 0 := by
  have hcoord (m : ℕ) (x : V) (a : ι) : b.repr ((f ^ m) x) a = μ a ^ m * b.repr x a := by
    induction m generalizing x with
    | zero => simp
    | succ m ih =>
      have h1 : b.coord a ∘ₗ f = μ a • b.coord a := by
        refine b.ext fun c => ?_
        simp only [LinearMap.comp_apply, hf, map_smul, LinearMap.smul_apply,
          Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]
        by_cases hc : c = a
        · rw [hc]
        · simp [hc]
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ]
      have := LinearMap.congr_fun h1 x
      simp only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.smul_apply,
        smul_eq_mul] at this
      rw [this]
      ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero, Module.End.one_apply] at h
    rw [h, map_zero]
  apply b.repr.injective
  ext a
  have h2 := hcoord n y a
  rw [h, map_zero, Finsupp.zero_apply] at h2
  have h3 := hcoord 1 y a
  rw [pow_one] at h3
  rw [h3, map_zero, Finsupp.zero_apply, pow_one]
  rcases mul_eq_zero.mp h2.symm with h4 | h4
  · rw [pow_eq_zero_iff hn.ne'] at h4
    rw [h4, zero_mul]
  · rw [h4, mul_zero]

end Eigenbasis

section CartanThrough

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

/-- An element whose adjoint action kills every vector killed by a power of it lies in a
Cartan subalgebra: a Cartan subalgebra of its centralizer is one of `L`. -/
theorem exists_isCartanSubalgebra_mem (x₀ : L)
    (hker : ∀ y : L, ∀ n : ℕ, ((ad ℂ L x₀) ^ n) y = 0 → ⁅x₀, y⁆ = 0) :
    ∃ 𝔥 : LieSubalgebra ℂ L, 𝔥.IsCartanSubalgebra ∧ x₀ ∈ 𝔥 := by
  let C := LieSubalgebra.engel ℂ x₀
  have hC (y : L) : y ∈ C ↔ ⁅x₀, y⁆ = 0 := by
    rw [LieSubalgebra.mem_engel_iff]
    constructor
    · rintro ⟨n, hn⟩; exact hker y n hn
    · intro h; exact ⟨1, by simpa using h⟩
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℂ C
  let 𝔥C := LieSubalgebra.engel ℂ x
  let 𝔥 := 𝔥C.map C.incl
  have hinj : Function.Injective C.incl := Subtype.val_injective
  have hx₀C : x₀ ∈ C := (hC x₀).mpr (lie_self x₀)
  have hx₀ : x₀ ∈ 𝔥 := by
    refine ⟨⟨x₀, hx₀C⟩, ?_, rfl⟩
    show (⟨x₀, hx₀C⟩ : C) ∈ 𝔥C
    rw [LieSubalgebra.mem_engel_iff]
    refine ⟨1, ?_⟩
    have hxx : ⁅(x : L), x₀⁆ = 0 := by rw [← lie_skew, (hC x).mp x.2, neg_zero]
    simp only [pow_one, LieAlgebra.ad_apply]
    exact Subtype.ext hxx
  refine ⟨𝔥, ⟨?_, ?_⟩, hx₀⟩
  · have e := LieSubalgebra.equivMapOfInjective (f := C.incl) (K := 𝔥C) hinj
    exact e.nilpotent_iff_equiv_nilpotent.mp hx.nilpotent
  · refine le_antisymm ?_ (LieSubalgebra.le_normalizer 𝔥)
    intro y hy
    rw [LieSubalgebra.mem_normalizer_iff] at hy
    have h1 : ⁅y, x₀⁆ ∈ C := by
      obtain ⟨w, -, hw⟩ := hy x₀ hx₀
      rw [← hw]
      exact w.2
    have hyC : y ∈ C := by
      rw [hC]
      apply hker y 2
      rw [pow_two, Module.End.mul_apply, LieAlgebra.ad_apply, LieAlgebra.ad_apply,
        ← lie_skew x₀ y, lie_neg, (hC _).mp h1, neg_zero]
    have hyN : (⟨y, hyC⟩ : C) ∈ 𝔥C.normalizer := by
      rw [LieSubalgebra.mem_normalizer_iff]
      intro z hz
      obtain ⟨w, hw, hwz⟩ := hy z.1 ⟨z, hz, rfl⟩
      have : w = ⁅(⟨y, hyC⟩ : C), z⁆ := Subtype.ext hwz
      rw [← this]
      exact hw
    rw [hx.self_normalizing] at hyN
    exact ⟨⟨y, hyC⟩, hyN, rfl⟩

end CartanThrough

section Main

omit [FiniteDimensional ℂ g] in
theorem lie_center_left {c : g} (hc : c ∈ center ℂ g) (y : g) : ⁅c, y⁆ = 0 := by
  rw [← lie_skew, (mem_maxTrivSubmodule ℂ g g c).mp hc y, neg_zero]

variable (hred : radical ℂ g = center ℂ g) (H : g)
  (hspan : Submodule.span ℂ {Y : g | ∃ k : ℤ, ⁅H, Y⁆ = (k : ℂ) • Y} = ⊤)

omit [FiniteDimensional ℂ g] in
include hspan in
theorem ad_eq_zero_of_pow (y : g) (n : ℕ) (h : ((ad ℂ g H) ^ n) y = 0) : ⁅H, y⁆ = 0 := by
  obtain ⟨t, htS, htspan, hli⟩ :=
    exists_linearIndependent ℂ {Y : g | ∃ k : ℤ, ⁅H, Y⁆ = (k : ℂ) • Y}
  let b : Module.Basis t ℂ g := Module.Basis.mk hli (by rw [Subtype.range_coe, htspan, hspan])
  have hb (a : t) : b a = a := Module.Basis.mk_apply _ _ _
  choose d hd using fun a : t => htS a.2
  exact apply_eq_zero_of_pow_apply_eq_zero b (ad ℂ g H) (fun a => (d a : ℂ))
    (fun a => by rw [hb, ad_apply]; exact hd a) y n h

include hred hspan in
/-- **Cartan data.** A reductive complex Lie algebra with an integral grading element `H` has an
abelian subspace `𝔥 ∋ H` and a basis of common eigenvectors of `ad 𝔥` with linear weights, such
that a basis vector of weight zero lies in `𝔥`; it also has a nondegenerate symmetric invariant
form that is nondegenerate on the centre. -/
theorem exists_cartanData :
    ∃ (𝔥 : Submodule ℂ g) (I : Type v) (_ : Fintype I) (b : Module.Basis I ℂ g)
      (wt : I → 𝔥 →ₗ[ℂ] ℂ) (B : LinearMap.BilinForm ℂ g),
      H ∈ 𝔥 ∧ (∀ x ∈ 𝔥, ∀ y ∈ 𝔥, ⁅x, y⁆ = 0) ∧
      (∀ i (h : 𝔥), ⁅(h : g), b i⁆ = wt i h • b i) ∧
      (∀ i, wt i = 0 → b i ∈ 𝔥) ∧
      B.Nondegenerate ∧ B.IsSymm ∧ (∀ x y z, B ⁅x, y⁆ z = B x ⁅y, z⁆) ∧
      (∀ c ∈ center ℂ g, (∀ c' ∈ center ℂ g, B c c' = 0) → c = 0) := by
  classical
  obtain ⟨s, hs⟩ := exists_isCompl_center hred
  have : IsKilling ℂ s := isKilling_complement hred hs
  have hsub := isCompl_toSubmodule hs
  have hcb (x y : s) : ((⁅x, y⁆ : s) : g) = ⁅(x : g), (y : g)⁆ :=
    (s : LieSubalgebra ℂ g).coe_bracket x y
  have hdecomp (v : g) : ∃ c ∈ center ℂ g, ∃ w ∈ s, c + w = v :=
    Submodule.mem_sup.mp (hsub.sup_eq_top ▸ Submodule.mem_top : v ∈ _)
  obtain ⟨Hz, hHz, Hs, hHs, hH⟩ := hdecomp H
  let Hs' : s := ⟨Hs, hHs⟩
  have hHs_lie (w : g) : ⁅Hs, w⁆ = ⁅H, w⁆ := by
    rw [← hH, add_lie, lie_center_left hHz, zero_add]
  have hpow (n : ℕ) (y : s) : ((((ad ℂ s Hs') ^ n) y : s) : g) = ((ad ℂ g H) ^ n) (y : g) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih, ad_apply,
        ad_apply, hcb, hHs_lie]
  have hker (y : s) (n : ℕ) (h : ((ad ℂ s Hs') ^ n) y = 0) : ⁅Hs', y⁆ = 0 := by
    have h' := hpow n y
    rw [h, LieSubmodule.coe_zero] at h'
    apply Subtype.ext
    rw [hcb, LieSubmodule.coe_zero, hHs_lie]
    exact ad_eq_zero_of_pow H hspan y n h'.symm
  obtain ⟨𝔥S, hCartan, hHs𝔥⟩ := exists_isCartanSubalgebra_mem Hs' hker
  have := hCartan
  let ι : s →ₗ[ℂ] g := (s : Submodule ℂ g).subtype
  let 𝔥 : Submodule ℂ g := (center ℂ g : Submodule ℂ g) ⊔ (𝔥S : Submodule ℂ s).map ι
  have hmem𝔥 (h : g) : h ∈ 𝔥 ↔ ∃ c ∈ center ℂ g, ∃ t ∈ 𝔥S, c + (t : g) = h := by
    constructor
    · intro hh
      obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.mp hh
      obtain ⟨t, ht, rfl⟩ := hw
      exact ⟨c, hc, t, ht, rfl⟩
    · rintro ⟨c, hc, t, ht, rfl⟩
      exact Submodule.add_mem_sup hc ⟨t, ht, rfl⟩
  have hH𝔥 : H ∈ 𝔥 := (hmem𝔥 H).mpr ⟨Hz, hHz, Hs', hHs𝔥, hH⟩
  have h𝔥S_ab (t t' : s) (ht : t ∈ 𝔥S) (ht' : t' ∈ 𝔥S) : ⁅t, t'⁆ = 0 := by
    have := trivial_lie_zero 𝔥S 𝔥S (⟨t, ht⟩ : 𝔥S) ⟨t', ht'⟩
    exact congrArg Subtype.val this
  have hab : ∀ x ∈ 𝔥, ∀ y ∈ 𝔥, ⁅x, y⁆ = 0 := by
    intro x hx y hy
    obtain ⟨c, hc, t, ht, rfl⟩ := (hmem𝔥 x).mp hx
    obtain ⟨c', hc', t', ht', rfl⟩ := (hmem𝔥 y).mp hy
    rw [add_lie, lie_center_left hc, zero_add, lie_add, ← lie_skew, lie_center_left hc',
      neg_zero, zero_add, ← hcb, h𝔥S_ab t t' ht ht', LieSubmodule.coe_zero]
  -- common eigenvectors of `ad 𝔥` span `g`
  let E : Set g := {v | ∀ h ∈ 𝔥, ∃ μ : ℂ, ⁅h, v⁆ = μ • v}
  have hcE (c : g) (hc : c ∈ center ℂ g) : c ∈ E := fun h _ =>
    ⟨0, by rw [← lie_skew, lie_center_left hc, neg_zero, zero_smul]⟩
  have hrootE (χ : 𝔥S → ℂ) (w : s) (hw : w ∈ genWeightSpace s χ) : (w : g) ∈ E := by
    intro h hh
    obtain ⟨c, hc, t, ht, rfl⟩ := (hmem𝔥 h).mp hh
    refine ⟨χ ⟨t, ht⟩, ?_⟩
    have h1 := LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace (H := 𝔥S) hw ⟨t, ht⟩
    rw [LieSubalgebra.coe_bracket_of_module] at h1
    rw [add_lie, lie_center_left hc, zero_add, ← hcb]
    change ((⁅t, w⁆ : s) : g) = _
    rw [h1]
    rfl
  have hspanE : Submodule.span ℂ E = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, hc, w, hw, rfl⟩ := hdecomp v
    refine Submodule.add_mem _ (Submodule.subset_span (hcE c hc)) ?_
    have hw' : (⟨w, hw⟩ : s) ∈ (⨆ χ : 𝔥S → ℂ, genWeightSpace s χ : LieSubmodule ℂ 𝔥S s) := by
      rw [LieModule.iSup_genWeightSpace_eq_top]
      exact LieSubmodule.mem_top _
    rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.iSup_toSubmodule] at hw'
    exact Submodule.iSup_induction (motive := fun x : s => (x : g) ∈ Submodule.span ℂ E) _ hw'
      (fun χ x hx => Submodule.subset_span (hrootE χ x hx)) (by simp)
      (fun x y hx hy => by rw [Submodule.coe_add]; exact Submodule.add_mem _ hx hy)
  obtain ⟨T, hTE, hTspan, hli⟩ := exists_linearIndependent ℂ E
  have : Fintype T := hli.setFinite.fintype
  let b : Module.Basis T ℂ g := Module.Basis.mk hli (by rw [Subtype.range_coe, hTspan, hspanE])
  have hb (i : T) : b i = i := Module.Basis.mk_apply _ _ _
  let wt : T → 𝔥 →ₗ[ℂ] ℂ := fun i =>
    { toFun := fun h => b.repr ⁅(h : g), b i⁆ i
      map_add' := fun x y => by simp [add_lie]
      map_smul' := fun c x => by simp [smul_lie] }
  have heig (i : T) (h : 𝔥) : ⁅(h : g), b i⁆ = wt i h • b i := by
    obtain ⟨μ, hμ⟩ := hTE i.2 h h.2
    have hμ' : ⁅(h : g), b i⁆ = μ • b i := by rw [hb]; exact hμ
    have hw : wt i h = μ := by
      change b.repr ⁅(h : g), b i⁆ i = μ
      rw [hμ', map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    rw [hw, hμ']
  have hzero (i : T) (hi : wt i = 0) : b i ∈ 𝔥 := by
    have hcomm (h : g) (hh : h ∈ 𝔥) : ⁅h, b i⁆ = 0 := by
      rw [heig i ⟨h, hh⟩, hi, LinearMap.zero_apply, zero_smul]
    obtain ⟨c, hc, w, hw, hcw⟩ := hdecomp (b i)
    let w' : s := ⟨w, hw⟩
    have hw0 : w' ∈ rootSpace 𝔥S 0 := by
      rw [LieModule.mem_genWeightSpace]
      intro x
      refine ⟨1, ?_⟩
      simp only [Pi.zero_apply, zero_smul, sub_zero, pow_one, LieModule.toEnd_apply_apply]
      apply Subtype.ext
      rw [LieSubalgebra.coe_bracket_of_module, hcb]
      have := hcomm ((x : s) : g) ((hmem𝔥 _).mpr ⟨0, (center ℂ g).zero_mem, x, x.2, zero_add _⟩)
      rw [← hcw, lie_add, ← lie_skew, lie_center_left hc, neg_zero, zero_add] at this
      simpa using this
    rw [rootSpace_zero_eq] at hw0
    rw [← hcw]
    exact (hmem𝔥 _).mpr ⟨c, hc, w', hw0, rfl⟩
  -- the invariant form: the Killing form plus a dot product on the centre coordinates
  let Z : Submodule ℂ g := (center ℂ g : Submodule ℂ g)
  let πz : g →ₗ[ℂ] Z := Submodule.projectionOnto Z _ hsub
  let bz := Module.finBasis ℂ Z
  let f : Fin (Module.finrank ℂ Z) → g →ₗ[ℂ] ℂ := fun a => (bz.coord a).comp πz
  let β : LinearMap.BilinForm ℂ g := ∑ a, (f a).smulRight (f a)
  have hβ (x y : g) : β x y = ∑ a, f a x * f a y := by
    simp [β, LinearMap.smulRight_apply, LinearMap.sum_apply]
  let B : LinearMap.BilinForm ℂ g := killingForm ℂ g + β
  have hB (x y : g) : B x y = killingForm ℂ g x y + ∑ a, f a x * f a y := by
    simp [B, hβ]
  have hlie_s (x y : g) : ⁅x, y⁆ ∈ s := by
    obtain ⟨c, hc, w, hw, rfl⟩ := hdecomp y
    rw [lie_add, ← lie_skew, lie_center_left hc, neg_zero, zero_add]
    exact s.lie_mem hw
  have hfs (a : Fin (Module.finrank ℂ Z)) (x : g) (hx : x ∈ s) : f a x = 0 := by
    change bz.coord a (πz x) = 0
    rw [show πz x = 0 from Submodule.projectionOnto_apply_of_mem_right hsub hx, map_zero]
  have hfc (a : Fin (Module.finrank ℂ Z)) (c : g) (hc : c ∈ center ℂ g) :
      f a c = bz.coord a ⟨c, hc⟩ := by
    change bz.coord a (πz c) = bz.coord a ⟨c, hc⟩
    rw [show πz c = ⟨c, hc⟩ from Submodule.projectionOnto_apply_of_mem_left hsub hc]
  have hκc (x c : g) (hc : c ∈ center ℂ g) : killingForm ℂ g x c = 0 := by
    have := WeylCompleteReducibility.center_le_killingCompl_top (k := ℂ) (L := g) hc
    rw [LieIdeal.mem_killingCompl] at this
    exact this x (LieSubmodule.mem_top x)
  have hsymm : ∀ x y, B x y = B y x := by
    intro x y
    rw [hB, hB, LieModule.traceForm_comm]
    congr 1
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hinv : ∀ x y z, B ⁅x, y⁆ z = B x ⁅y, z⁆ := by
    intro x y z
    rw [hB, hB, LieModule.traceForm_apply_lie_apply]
    congr 1
    rw [Finset.sum_eq_zero fun a _ => by rw [hfs a _ (hlie_s x y), zero_mul],
      Finset.sum_eq_zero fun a _ => by rw [hfs a _ (hlie_s y z), mul_zero]]
  have hcoord (x : g) (a : Fin (Module.finrank ℂ Z)) : B x (bz a : g) = f a x := by
    rw [hB, hκc x _ (bz a).2, zero_add, Finset.sum_eq_single a]
    · rw [hfc a _ (bz a).2]
      simp
    · intro a' _ ha'
      rw [hfc a' _ (bz a).2]
      simp [ha'.symm]
    · simp
  have hsep : ∀ x : g, (∀ y : g, B x y = 0) → x = 0 := by
    intro x hx
    have hπ : πz x = 0 := by
      apply bz.repr.injective
      ext a
      have := hx (bz a)
      rw [hcoord] at this
      simpa [f] using this
    have hxs : x ∈ s := (Submodule.projectionOnto_apply_eq_zero_iff hsub).mp hπ
    refine eq_zero_of_killingForm hred hs x hxs fun y hy => ?_
    have := hx y
    rw [hB, Finset.sum_eq_zero fun a _ => by rw [hfs a _ hxs, zero_mul], add_zero] at this
    exact this
  refine ⟨𝔥, T, inferInstance, b, wt, B, hH𝔥, hab, heig, hzero, ?_, ⟨hsymm⟩, hinv, ?_⟩
  · refine ⟨hsep, fun y hy => hsep y fun x => ?_⟩
    rw [hsymm]
    exact hy x
  · intro c hc hc'
    have hπ : πz c = 0 := by
      apply bz.repr.injective
      ext a
      have := hc' (bz a) (bz a).2
      rw [hcoord] at this
      simpa [f] using this
    have hcs : c ∈ s := (Submodule.projectionOnto_apply_eq_zero_iff hsub).mp hπ
    exact (Submodule.disjoint_def.mp hsub.disjoint) c hc hcs

end Main

end Langlands.Algebra.ReductiveCartanData
