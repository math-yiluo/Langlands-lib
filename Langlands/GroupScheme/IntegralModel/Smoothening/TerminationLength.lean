import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # Lengths of torsion submodules over a domain

Length bookkeeping for the termination of the smoothening sequence. -/

noncomputable section

open Module Submodule

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {R : Type*} [CommRing R]

section General

variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

theorem length_mono {N₁ N₂ : Submodule R M} (h : N₁ ≤ N₂) :
    Module.length R N₁ ≤ Module.length R N₂ :=
  Module.length_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

theorem length_map_of_injective (f : M →ₗ[R] M') (hf : Function.Injective f)
    (N : Submodule R M) : Module.length R (N.map f) = Module.length R N :=
  (Submodule.equivMapOfInjective f hf N).symm.length_eq

/-- Splitting the length of a submodule along a linear map. -/
theorem length_eq_inf_ker_add_map (f : M →ₗ[R] M') (N : Submodule R M) :
    Module.length R N =
      Module.length R (N ⊓ LinearMap.ker f : Submodule R M) + Module.length R (N.map f) := by
  refine Module.length_eq_add_of_exact (Submodule.inclusion inf_le_left) (f.submoduleMap N)
    (Submodule.inclusion_injective _) (LinearMap.submoduleMap_surjective f N) ?_
  intro y
  constructor
  · intro hy
    have hy' : f y = 0 := by
      have := congrArg Subtype.val hy
      simpa using this
    exact ⟨⟨y, y.2, hy'⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    ext
    simpa using x.2.2

end General

section Domain

variable [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The defect of a module: the length of its torsion submodule. -/
def defect (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R (torsion R M)

/-- The length of the `a`-torsion. -/
def torsionByLength (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (a : R) : ℕ∞ :=
  Module.length R (torsionBy R M a)

theorem torsionBy_le_torsion {a : R} (ha : a ≠ 0) : torsionBy R M a ≤ torsion R M := by
  intro x hx
  rw [mem_torsion_iff]
  exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, (mem_torsionBy_iff a x).mp hx⟩

theorem torsionByLength_le_defect {a : R} (ha : a ≠ 0) :
    torsionByLength R M a ≤ defect R M :=
  length_mono (torsionBy_le_torsion ha)

theorem torsion_inf_ker_lsmul {a : R} (ha : a ≠ 0) :
    (torsion R M ⊓ LinearMap.ker (LinearMap.lsmul R M a) : Submodule R M) = torsionBy R M a := by
  apply le_antisymm
  · intro x hx
    exact (mem_torsionBy_iff a x).mpr (by simpa using hx.2)
  · intro x hx
    exact ⟨torsionBy_le_torsion ha hx, by simpa using (mem_torsionBy_iff a x).mp hx⟩

omit [IsDomain R] in
/-- Torsion is preserved and reflected by a surjection whose kernel is torsion. -/
theorem map_torsion_eq_of_ker_le {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (hker : LinearMap.ker f ≤ torsion R M) :
    (torsion R M).map f = torsion R N := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := (mem_torsion_iff x).mp hx
    rw [Submonoid.smul_def] at ha
    exact (mem_torsion_iff _).mpr ⟨a, by rw [Submonoid.smul_def, ← map_smul, ha, map_zero]⟩
  · intro y hy
    obtain ⟨a, ha⟩ := (mem_torsion_iff y).mp hy
    obtain ⟨x, rfl⟩ := hf y
    rw [Submonoid.smul_def] at ha
    have hax : (a : R) • x ∈ torsion R M := hker (by simp [ha])
    obtain ⟨b, hb⟩ := (mem_torsion_iff _).mp hax
    refine ⟨x, (mem_torsion_iff x).mpr ⟨b * a, ?_⟩, rfl⟩
    rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def]
    exact hb

omit [IsDomain R] in
/-- Length of torsion along a surjection with torsion kernel. -/
theorem defect_eq_add_of_surjective {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (hker : LinearMap.ker f ≤ torsion R M) :
    defect R M = Module.length R (LinearMap.ker f) + defect R N := by
  unfold defect
  rw [length_eq_inf_ker_add_map f (torsion R M), inf_eq_right.mpr hker,
    map_torsion_eq_of_ker_le f hf hker]

omit [IsDomain R] in
/-- If a submodule `W` of `V` is contained in `a • V` and is killed by `a`, then `V` has at
least twice the length of `W`. -/
theorem two_mul_length_le {V W : Submodule R M} (a : R)
    (hW : W ≤ V.map (LinearMap.lsmul R M a)) (hWa : W ≤ torsionBy R M a) :
    2 * Module.length R W ≤ Module.length R V := by
  have hVW : V.map (LinearMap.lsmul R M a) ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    exact V.smul_mem a hv
  rw [length_eq_inf_ker_add_map (LinearMap.lsmul R M a) V, two_mul]
  gcongr
  · apply length_mono
    intro w hw
    exact ⟨hVW (hW hw), by simpa using (mem_torsionBy_iff a w).mp (hWa hw)⟩
  · exact length_mono hW

end Domain

section Pushout

variable [IsDomain R] {T U : Type*} [AddCommGroup T] [Module R T] [AddCommGroup U] [Module R U]

/-- The data of an extension of `T` by formal quotients `z k / ϖ`. -/
structure DivisionExtension (ϖ : R) (T U : Type*) [AddCommGroup T] [Module R T]
    [AddCommGroup U] [Module R U] (c : ℕ) (z : Fin c → T) where
  ι : T →ₗ[R] U
  injective : Function.Injective ι
  ζ : Fin c → U
  smul_ζ : ∀ k, ϖ • ζ k = ι (z k)
  span : ∀ u : U, ∃ (t : T) (a : Fin c → R), u = ι t + ∑ k, a k • ζ k

variable {ϖ : R} {c : ℕ} {z : Fin c → T}

/-- The elements `z k` are linearly independent modulo `ϖ`. -/
def IndepModulo (ϖ : R) (z : Fin c → T) : Prop :=
  ∀ a : Fin c → R, (∑ k, a k • z k) ∈ (⊤ : Submodule R T).map (LinearMap.lsmul R T ϖ) →
    ∀ k, ϖ ∣ a k

namespace DivisionExtension

variable (E : DivisionExtension ϖ T U c z)

omit [IsDomain R] in
theorem torsionBy_eq (hz : IndepModulo ϖ z) :
    torsionBy R U ϖ = (torsionBy R T ϖ).map E.ι := by
  apply le_antisymm
  · intro u hu
    obtain ⟨t, a, rfl⟩ := E.span u
    have h0 : ϖ • (E.ι t + ∑ k, a k • E.ζ k) = 0 := (mem_torsionBy_iff ϖ _).mp hu
    have h1 : E.ι (ϖ • t + ∑ k, a k • z k) = 0 := by
      rw [map_add, map_smul, map_sum]
      simp_rw [map_smul, ← E.smul_ζ, smul_comm (a _) ϖ, ← Finset.smul_sum, ← smul_add]
      exact h0
    have h2 : ϖ • t + ∑ k, a k • z k = 0 := E.injective (by rw [h1, map_zero])
    have hmem : (∑ k, a k • z k) ∈ (⊤ : Submodule R T).map (LinearMap.lsmul R T ϖ) :=
      ⟨-t, trivial, by simp [eq_neg_of_add_eq_zero_right h2]⟩
    choose b hb using hz a hmem
    refine ⟨t + ∑ k, b k • z k, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_torsionBy_iff, smul_add, Finset.smul_sum]
      simp_rw [smul_smul, ← hb]
      exact h2
    · rw [map_add, map_sum]
      simp_rw [map_smul, ← E.smul_ζ, smul_smul, mul_comm (b _) ϖ, ← hb]
  · rintro _ ⟨t, ht, rfl⟩
    rw [mem_torsionBy_iff, ← map_smul, (mem_torsionBy_iff ϖ t).mp ht, map_zero]

omit [IsDomain R] in
theorem smul_eq_ι (t : T) (a : Fin c → R) :
    ϖ • (E.ι t + ∑ k, a k • E.ζ k) = E.ι (ϖ • t + ∑ k, a k • z k) := by
  rw [map_add, map_smul, map_sum, smul_add, Finset.smul_sum]
  simp_rw [map_smul, ← E.smul_ζ, smul_comm ϖ (a _)]

omit [IsDomain R] in
theorem map_lsmul_torsion_le :
    (torsion R U).map (LinearMap.lsmul R U ϖ) ≤ (torsion R T).map E.ι := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨t, a, rfl⟩ := E.span u
  have heq : (LinearMap.lsmul R U ϖ) (E.ι t + ∑ k, a k • E.ζ k) =
      E.ι (ϖ • t + ∑ k, a k • z k) := by
    rw [LinearMap.lsmul_apply, map_add, map_smul, map_sum, smul_add, Finset.smul_sum]
    simp_rw [map_smul, ← E.smul_ζ, smul_comm ϖ (a _)]
  rw [heq]
  refine ⟨_, ?_, rfl⟩
  obtain ⟨s, hs⟩ := (mem_torsion_iff _).mp hu
  rw [Submonoid.smul_def] at hs
  refine (mem_torsion_iff _).mpr ⟨s, E.injective ?_⟩
  rw [Submonoid.smul_def, map_smul, ← heq, map_zero, LinearMap.lsmul_apply, smul_comm, hs,
    smul_zero]

include E in
/-- The torsion of the extension has length at most that of `T` plus the `ϖ`-torsion. -/
theorem defect_le (hϖ : ϖ ≠ 0) (hz : IndepModulo ϖ z) :
    defect R U ≤ torsionByLength R T ϖ + defect R T := by
  unfold defect torsionByLength
  rw [length_eq_inf_ker_add_map (LinearMap.lsmul R U ϖ) (torsion R U), torsion_inf_ker_lsmul hϖ,
    E.torsionBy_eq hz, length_map_of_injective _ E.injective]
  gcongr
  exact (length_mono (E.map_lsmul_torsion_le)).trans
    (length_map_of_injective _ E.injective _).le

/-- **Defect drop.** Let `U` be obtained from `T` by adjoining `z k / ϖ` for elements `z k`
independent modulo `ϖ`, and let `f : U → N` be a surjection whose kernel `V` is torsion and
contains, after multiplication by `ϖ`, the `ϖ`-torsion of `T`. Then the defect of `N` plus the
length of the `ϖ`-torsion of `T` is at most the defect of `T`. -/
theorem defect_add_le {N : Type*} [AddCommGroup N] [Module R N] (hϖ : ϖ ≠ 0)
    (hz : IndepModulo ϖ z) (f : U →ₗ[R] N) (hf : Function.Surjective f)
    (hker : LinearMap.ker f ≤ torsion R U)
    (hdiv : ∀ t ∈ torsionBy R T ϖ, ∃ v ∈ LinearMap.ker f, ϖ • v = E.ι t) :
    defect R N + torsionByLength R T ϖ ≤ defect R T := by
  have hU := E.defect_le hϖ hz
  rw [defect_eq_add_of_surjective f hf hker] at hU
  have hW : (torsionBy R T ϖ).map E.ι ≤ (LinearMap.ker f).map (LinearMap.lsmul R U ϖ) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨v, hv, hvt⟩ := hdiv t ht
    exact ⟨v, hv, by rw [LinearMap.lsmul_apply, hvt]⟩
  have hW' : (torsionBy R T ϖ).map E.ι ≤ torsionBy R U ϖ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_torsionBy_iff, ← map_smul, (mem_torsionBy_iff ϖ t).mp ht, map_zero]
  have h2 := two_mul_length_le ϖ hW hW'
  rw [length_map_of_injective _ E.injective] at h2
  change 2 * torsionByLength R T ϖ ≤ _ at h2
  by_cases htop : torsionByLength R T ϖ = ⊤
  · have : defect R T = ⊤ := top_le_iff.mp (htop ▸ torsionByLength_le_defect hϖ)
    rw [this]
    exact le_top
  · have key : defect R N + torsionByLength R T ϖ + torsionByLength R T ϖ ≤
        defect R T + torsionByLength R T ϖ := by
      calc defect R N + torsionByLength R T ϖ + torsionByLength R T ϖ
          = defect R N + 2 * torsionByLength R T ϖ := by rw [two_mul, add_assoc]
        _ ≤ defect R N + Module.length R (LinearMap.ker f) := by gcongr
        _ ≤ torsionByLength R T ϖ + defect R T := by rw [add_comm]; exact hU
        _ = defect R T + torsionByLength R T ϖ := add_comm _ _
    exact (ENat.add_le_add_iff_right htop).mp key

end DivisionExtension

/-- The pushout adjoining formal quotients `z k / ϖ` to `T`. -/
def pushoutRel (ϖ : R) (z : Fin c → T) : Submodule R (T × (Fin c → R)) :=
  Submodule.span R (Set.range fun k => (z k, -(ϖ • Pi.single k (1 : R))))

/-- The module obtained from `T` by adjoining formal quotients `z k / ϖ`. -/
abbrev Pushout (ϖ : R) (z : Fin c → T) := (T × (Fin c → R)) ⧸ pushoutRel ϖ z

/-- The pushout is a division extension. -/
def pushout (hϖ : ϖ ≠ 0) (z : Fin c → T) : DivisionExtension ϖ T (Pushout ϖ z) c z where
  ι := (pushoutRel ϖ z).mkQ ∘ₗ LinearMap.inl R T (Fin c → R)
  injective := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have hmem : ((t, 0) : T × (Fin c → R)) ∈ pushoutRel ϖ z := by
      simpa [Submodule.Quotient.mk_eq_zero] using ht
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hmem
    have h2 : ∑ k, r k • (-(ϖ • Pi.single k (1 : R))) = 0 := by
      have := congrArg Prod.snd hr
      simpa [Prod.snd_sum] using this
    have hr0 : r = 0 := by
      funext k
      have := congrFun h2 k
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.single_apply,
        mul_ite, mul_one, mul_zero, neg_ite, neg_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, Pi.zero_apply] at this
      have : r k * ϖ = 0 := by linear_combination -this
      simpa [hϖ] using this
    have h1 := congrArg Prod.fst hr
    simp [hr0] at h1
    exact h1.symm
  ζ k := Submodule.Quotient.mk (0, Pi.single k 1)
  smul_ζ k := by
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
      ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    have : (ϖ • ((0 : T), (Pi.single k (1 : R) : Fin c → R)) - LinearMap.inl R T (Fin c → R) (z k))
        = -((z k, -(ϖ • Pi.single k (1 : R))) : T × (Fin c → R)) := by
      ext <;> simp
    rw [this]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  span u := by
    obtain ⟨⟨t, a⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    refine ⟨t, a, ?_⟩
    change (pushoutRel ϖ z).mkQ (t, a) = (pushoutRel ϖ z).mkQ (t, 0) +
      ∑ k, a k • (pushoutRel ϖ z).mkQ (0, Pi.single k 1)
    simp_rw [← map_smul, ← map_sum, ← map_add]
    congr 1
    ext
    · simp [Prod.fst_sum]
    · rw [Prod.snd_add, Prod.snd_sum, Pi.add_apply, Finset.sum_apply]
      simp [Pi.single_apply]

end Pushout

section DVR

variable [IsDomain R] [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Over a discrete valuation ring, a module with nonzero torsion has nonzero `ϖ`-torsion. -/
theorem torsionByLength_ne_zero {ϖ : R} (hϖ : Irreducible ϖ) (h : defect R M ≠ 0) :
    torsionByLength R M ϖ ≠ 0 := by
  unfold defect at h
  unfold torsionByLength
  rw [Ne, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial] at h ⊢
  obtain ⟨⟨x, hx⟩, hx0⟩ := exists_ne (0 : torsion R M)
  have hx0' : x ≠ 0 := fun h' => hx0 (Subtype.ext h')
  obtain ⟨a, ha⟩ := (mem_torsion_iff x).mp hx
  have ha0 : (a : R) ≠ 0 := nonZeroDivisors.coe_ne_zero a
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  have hex : ∃ m : ℕ, ϖ ^ m • x = 0 := by
    refine ⟨n, ?_⟩
    have : (a : R) • x = 0 := by rw [← Submonoid.smul_def]; exact ha
    rw [hu, mul_smul, ← Units.smul_def] at this
    exact (smul_eq_zero_iff_eq u).mp this
  classical
  let m := Nat.find hex
  have hm : ϖ ^ m • x = 0 := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_smul] at hm
    exact hx0' hm
  have hmin : ϖ ^ (m - 1) • x ≠ 0 := Nat.find_min hex (by omega)
  refine ⟨⟨⟨ϖ ^ (m - 1) • x, ?_⟩, 0, ?_⟩⟩
  · rw [mem_torsionBy_iff, smul_smul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]
    exact hm
  · intro h'
    exact hmin (congrArg Subtype.val h')

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem length_sup_le (N₁ N₂ : Submodule R M) :
    Module.length R (N₁ ⊔ N₂ : Submodule R M) ≤ Module.length R N₁ + Module.length R N₂ := by
  rw [← Module.length_prod]
  refine Module.length_le_of_surjective
    (LinearMap.coprod (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_right)) ?_
  rintro ⟨y, hy⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
  exact ⟨(⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩), rfl⟩

theorem length_span_singleton_ne_top {x : M} (hx : x ∈ torsion R M) :
    Module.length R (R ∙ x) ≠ ⊤ := by
  obtain ⟨a, ha⟩ := (mem_torsion_iff x).mp hx
  have hfin := isFiniteLength_quotient_span_singleton R a.2
  rw [← Module.length_ne_top_iff] at hfin
  refine ne_top_of_le_ne_top hfin ?_
  have hle : Ideal.span {(a : R)} ≤ LinearMap.ker (LinearMap.toSpanSingleton R M x) := by
    rw [Ideal.span_le]
    rintro _ rfl
    simpa [← Submonoid.smul_def] using ha
  let g := (Ideal.span {(a : R)}).liftQ (LinearMap.toSpanSingleton R M x) hle
  have hrange : LinearMap.range g = R ∙ x := by
    rw [Submodule.range_liftQ, LinearMap.span_singleton_eq_range]
  rw [← hrange]
  exact Module.length_le_of_surjective g.rangeRestrict g.surjective_rangeRestrict

/-- A finitely generated module over a discrete valuation ring has finite defect. -/
theorem defect_ne_top [Module.Finite R M] : defect R M ≠ ⊤ := by
  unfold defect
  have hfg : (torsion R M).FG := IsNoetherian.noetherian _
  suffices ∀ N : Submodule R M, N.FG → N ≤ torsion R M → Module.length R N ≠ ⊤ from
    this _ hfg le_rfl
  intro N hN
  refine Submodule.fg_induction (motive := fun N _ => N ≤ torsion R M → Module.length R N ≠ ⊤)
    ?_ ?_ N hN
  · intro x hx
    exact length_span_singleton_ne_top (hx (Submodule.mem_span_singleton_self x))
  · intro N₁ N₂ _ _ h₁ h₂ h
    refine ne_top_of_le_ne_top ?_ (length_sup_le N₁ N₂)
    exact WithTop.add_ne_top.mpr ⟨h₁ (le_sup_left.trans h), h₂ (le_sup_right.trans h)⟩

end DVR

/-- A sequence of defects that drops by a positive amount while it is nonzero reaches zero. -/
theorem exists_eq_zero_of_drop (δ ν : ℕ → ℕ∞) (h0 : δ 0 ≠ ⊤)
    (hstep : ∀ n, δ (n + 1) + ν n ≤ δ n) (hpos : ∀ n, δ n ≠ 0 → ν n ≠ 0) :
    ∃ n, δ n = 0 := by
  by_contra hne
  push Not at hne
  have key : ∀ n : ℕ, δ n + n ≤ δ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : 1 ≤ ν n := Order.one_le_iff_ne_zero.mpr (hpos n (hne n))
      calc δ (n + 1) + ((n + 1 : ℕ) : ℕ∞) = δ (n + 1) + 1 + n := by
            push_cast; ring
        _ ≤ δ (n + 1) + ν n + n := by gcongr
        _ ≤ δ n + n := by gcongr; exact hstep n
        _ ≤ δ 0 := ih
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp h0
  have := key (N + 1)
  rw [← hN] at this
  have : ((N + 1 : ℕ) : ℕ∞) ≤ N := le_trans le_add_self this
  norm_cast at this
  omega

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
