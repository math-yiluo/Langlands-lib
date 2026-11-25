import Langlands.Cohomology.Profinite.Shapiro
import Mathlib.Algebra.Order.Star.Basic

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]

variable (k G) in

def finiteDiscreteRep (P : ℕ → Prop) : ObjectProperty (Rep.{u} k G) :=
  fun A => IsSmoothRep A ∧ Finite A ∧ P (Nat.card A)

variable (k G) in

def grothendieckRelations (P : ℕ → Prop) :
    AddSubgroup (FreeAbelianGroup (finiteDiscreteRep k G P).FullSubcategory) :=
  AddSubgroup.closure {x | ∃ (S : ShortComplex (Rep.{u} k G)) (h₁ : finiteDiscreteRep k G P S.X₁)
    (h₂ : finiteDiscreteRep k G P S.X₂) (h₃ : finiteDiscreteRep k G P S.X₃), S.ShortExact ∧
      x = FreeAbelianGroup.of ⟨S.X₂, h₂⟩ - FreeAbelianGroup.of ⟨S.X₁, h₁⟩ -
        FreeAbelianGroup.of ⟨S.X₃, h₃⟩}

variable (k G) in

def GrothendieckGroup (P : ℕ → Prop) : Type (u + 1) :=
  FreeAbelianGroup (finiteDiscreteRep k G P).FullSubcategory ⧸ grothendieckRelations k G P

instance (P : ℕ → Prop) : AddCommGroup (GrothendieckGroup k G P) :=
  inferInstanceAs (AddCommGroup (_ ⧸ grothendieckRelations k G P))

def GrothendieckGroup.mk {P : ℕ → Prop} (A : Rep.{u} k G) (hA : finiteDiscreteRep k G P A) :
    GrothendieckGroup k G P :=
  QuotientAddGroup.mk (s := grothendieckRelations k G P) (FreeAbelianGroup.of ⟨A, hA⟩)

variable [IsTopologicalGroup G]

variable (k G) in

def HasFiniteCohomology (P : ℕ → Prop) : Prop :=
  ∀ (A : Rep.{u} k G) [IsSmoothRep A], Finite A → P (Nat.card A) →
    (∀ q : ℕ, Finite (cohomology A q)) ∧ ∀ q : ℕ, 3 ≤ q → Subsingleton (cohomology A q)

noncomputable def eulerCharacteristic (A : Rep.{u} k G) [IsSmoothRep A] : ℚ :=
  ∏ q ∈ Finset.range 3, (Nat.card (cohomology A q) : ℚ) ^ ((-1 : ℤ) ^ q)

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

section Counting

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

theorem card_eq_card_ker_mul_card_range (f : M →ₗ[R] N) :
    Nat.card M = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  have h1 := AddSubgroup.card_mul_index f.toAddMonoidHom.ker
  rw [AddSubgroup.index_ker] at h1
  exact h1.symm

end Counting

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem eulerCharacteristic_eq (A : Rep.{u} k G) [IsSmoothRep A] :
    eulerCharacteristic A = (Nat.card (cohomology A 0) : ℚ) * Nat.card (cohomology A 2) /
      Nat.card (cohomology A 1) := by
  simp [eulerCharacteristic, Finset.prod_range_succ, div_eq_mul_inv]
  ring

section ShortExact

theorem card_range_eq_card_ker_of_exact {T : ShortComplex (ModuleCat k)} (hT : T.Exact) :
    Nat.card (LinearMap.range T.f.hom) = Nat.card (LinearMap.ker T.g.hom) := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hT
  rw [hT]

variable {S : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃]

theorem eulerCharacteristic_shortExact_of_finite (hS : S.ShortExact)
    [Finite (cohomology S.X₁ 1)] [Finite (cohomology S.X₂ 1)] [Finite (cohomology S.X₃ 1)]
    [Subsingleton (cohomology S.X₁ 3)] :
    eulerCharacteristic S.X₂ = eulerCharacteristic S.X₁ * eulerCharacteristic S.X₃ := by
  have hk := fun {X Y : ModuleCat k} (φ : X ⟶ Y) => card_eq_card_ker_mul_card_range φ.hom
  have e2 : ∀ i, Nat.card (LinearMap.range (coeffMap S.f i).hom) =
      Nat.card (LinearMap.ker (coeffMap S.g i).hom) := fun i =>
    card_range_eq_card_ker_of_exact (cohomology_exact₂ hS i)
  have e30 : Nat.card (LinearMap.range (coeffMap S.g 0).hom) =
      Nat.card (LinearMap.ker (δ hS 0 1 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 0 1 rfl)
  have e31 : Nat.card (LinearMap.range (coeffMap S.g 1).hom) =
      Nat.card (LinearMap.ker (δ hS 1 2 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 1 2 rfl)
  have e32 : Nat.card (LinearMap.range (coeffMap S.g 2).hom) =
      Nat.card (LinearMap.ker (δ hS 2 3 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 2 3 rfl)
  have e10 : Nat.card (LinearMap.range (δ hS 0 1 rfl).hom) =
      Nat.card (LinearMap.ker (coeffMap S.f 1).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 0 1 rfl)
  have e11 : Nat.card (LinearMap.range (δ hS 1 2 rfl).hom) =
      Nat.card (LinearMap.ker (coeffMap S.f 2).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 1 2 rfl)
  have h0 : Nat.card (LinearMap.ker (coeffMap S.f 0).hom) = 1 := by
    have := hS.mono_f
    have hm : Mono (coeffMap S.f 0) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (coeffCochainsMap S.f) 0
        (fun i => by simp)
    rw [LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 hm)]
    simp
  have htop : Nat.card (LinearMap.range (δ hS 2 3 rfl).hom) = 1 :=
    Nat.card_of_subsingleton (0 : LinearMap.range (δ hS 2 3 rfl).hom)
  have hA1 : Nat.card (cohomology S.X₁ 1) ≠ 0 := Nat.card_pos.ne'
  have hB1 : Nat.card (cohomology S.X₂ 1) ≠ 0 := Nat.card_pos.ne'
  have hC1 : Nat.card (cohomology S.X₃ 1) ≠ 0 := Nat.card_pos.ne'
  rw [hk (coeffMap S.f 1), ← e10] at hA1
  rw [hk (coeffMap S.g 1), ← e2 1] at hB1
  rw [hk (δ hS 1 2 rfl), ← e31] at hC1
  rw [eulerCharacteristic_eq, eulerCharacteristic_eq, eulerCharacteristic_eq,
    hk (coeffMap S.f 0), hk (coeffMap S.f 1), hk (coeffMap S.f 2),
    hk (coeffMap S.g 0), hk (coeffMap S.g 1), hk (coeffMap S.g 2),
    hk (δ hS 0 1 rfl), hk (δ hS 1 2 rfl), hk (δ hS 2 3 rfl),
    h0, htop, ← e2 0, ← e2 1, ← e2 2, ← e30, ← e31, ← e32, ← e10, ← e11]
  simp only [mul_ne_zero_iff] at hA1 hB1 hC1
  obtain ⟨hz0, hx1⟩ := hA1
  obtain ⟨-, hy1⟩ := hB1
  obtain ⟨-, hz1⟩ := hC1
  push_cast
  field_simp

end ShortExact

section Hypothesis

variable {P : ℕ → Prop}

theorem eulerCharacteristic_pos (hG : HasFiniteCohomology k G P) (A : Rep.{u} k G) [IsSmoothRep A]
    [Finite A] (hA : P (Nat.card A)) : 0 < eulerCharacteristic A := by
  obtain ⟨hfin, -⟩ := hG A ‹_› hA
  have h0 := hfin 0
  have h1 := hfin 1
  have h2 := hfin 2
  rw [eulerCharacteristic_eq]
  have p0 : (0 : ℚ) < Nat.card (cohomology A 0) := by exact_mod_cast Nat.card_pos
  have p1 : (0 : ℚ) < Nat.card (cohomology A 1) := by exact_mod_cast Nat.card_pos
  have p2 : (0 : ℚ) < Nat.card (cohomology A 2) := by exact_mod_cast Nat.card_pos
  positivity

variable {S : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃]

theorem eulerCharacteristic_shortExact_of_mem (hG : HasFiniteCohomology k G P) (hS : S.ShortExact)
    [Finite S.X₁] [Finite S.X₂] [Finite S.X₃] (h₁ : P (Nat.card S.X₁))
    (h₂ : P (Nat.card S.X₂)) (h₃ : P (Nat.card S.X₃)) :
    eulerCharacteristic S.X₂ = eulerCharacteristic S.X₁ * eulerCharacteristic S.X₃ := by
  obtain ⟨f₁, z₁⟩ := hG S.X₁ ‹_› h₁
  have := f₁ 1
  have := z₁ 3 le_rfl
  have := (hG S.X₂ ‹_› h₂).1 1
  have := (hG S.X₃ ‹_› h₃).1 1
  exact eulerCharacteristic_shortExact_of_finite hS

theorem eulerCharacteristic_shortExact (hP : ∀ m n, m ∣ n → P n → P m) (hG : HasFiniteCohomology k G P)
    (hS : S.ShortExact) [Finite S.X₂] (h₂ : P (Nat.card S.X₂)) :
    eulerCharacteristic S.X₂ = eulerCharacteristic S.X₁ * eulerCharacteristic S.X₃ := by
  have hinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have : Finite S.X₁ := Finite.of_injective _ hinj
  have : Finite S.X₃ := Finite.of_surjective _ hsurj
  have h₁ : P (Nat.card S.X₁) :=
    hP _ _ (AddSubgroup.card_dvd_of_injective S.f.hom.toLinearMap.toAddMonoidHom hinj) h₂
  have h₃ : P (Nat.card S.X₃) := by
    refine hP _ _ ⟨Nat.card (LinearMap.ker S.g.hom.toLinearMap), ?_⟩ h₂
    rw [card_eq_card_ker_mul_card_range S.g.hom.toLinearMap,
      LinearMap.range_eq_top.2 hsurj, mul_comm]
    congr 1
    exact Nat.card_congr (Submodule.topEquiv).toEquiv
  exact eulerCharacteristic_shortExact_of_mem hG hS h₁ h₂ h₃

noncomputable def eulerCharacteristicUnit (hG : HasFiniteCohomology k G P)
    (A : (finiteDiscreteRep k G P).FullSubcategory) : ℚˣ :=
  haveI := A.property.1
  haveI := A.property.2.1
  Units.mk0 (eulerCharacteristic A.obj) (eulerCharacteristic_pos hG A.obj A.property.2.2).ne'

theorem coe_eulerCharacteristicUnit (hG : HasFiniteCohomology k G P)
    (A : (finiteDiscreteRep k G P).FullSubcategory) :
    haveI := A.property.1
    (eulerCharacteristicUnit hG A : ℚ) = eulerCharacteristic A.obj :=
  rfl

noncomputable def eulerCharacteristicHom (hG : HasFiniteCohomology k G P) :
    GrothendieckGroup k G P →+ Additive ℚˣ :=
  QuotientAddGroup.lift (grothendieckRelations k G P)
    (FreeAbelianGroup.lift fun A => Additive.ofMul (eulerCharacteristicUnit hG A)) (by
      rw [grothendieckRelations, AddSubgroup.closure_le]
      rintro x ⟨S, h₁, h₂, h₃, hS, rfl⟩
      have := h₁.1
      have := h₂.1
      have := h₃.1
      have := h₁.2.1
      have := h₂.2.1
      have := h₃.2.1
      have key := eulerCharacteristic_shortExact_of_mem hG hS h₁.2.2 h₂.2.2 h₃.2.2
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
      rw [sub_sub, sub_eq_zero, ← ofMul_mul]
      congr 1
      ext
      simp only [Units.val_mul, coe_eulerCharacteristicUnit]
      exact key)

end Hypothesis

section Shapiro

variable [CompactSpace G] (U : OpenSubgroup G)

theorem eulerCharacteristic_coind (B : Rep.{u} k (U : Subgroup G)) [IsSmoothRep B] :
    eulerCharacteristic (Rep.coind (U : Subgroup G).subtype B) = eulerCharacteristic B := by
  simp only [eulerCharacteristic]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [Nat.card_congr (shapiroIso U B q).toLinearEquiv.toEquiv]

theorem eulerCharacteristic_res_eq_eulerCharacteristic_coind (A : Rep.{u} k G) [IsSmoothRep A] :
    eulerCharacteristic (Rep.res (U : Subgroup G).subtype A) =
      eulerCharacteristic (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) :=
  (eulerCharacteristic_coind U _).symm

noncomputable def coindValues (B : Rep.{u} k (U : Subgroup G)) :
    Rep.coind (U : Subgroup G).subtype B →+ (G ⧸ (U : Subgroup G) → B) :=
  AddMonoidHom.mk' (fun f c => f.1 (Quotient.out c)⁻¹) fun _ _ => rfl

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem coindValues_injective (B : Rep.{u} k (U : Subgroup G)) :
    Function.Injective (coindValues U B) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U : Subgroup G) x⁻¹
  have hx : x = (U : Subgroup G).subtype u * (Quotient.out
      (QuotientGroup.mk x⁻¹ : G ⧸ (U : Subgroup G)))⁻¹ := by
    rw [show (Quotient.out (QuotientGroup.mk x⁻¹ : G ⧸ (U : Subgroup G))) = x⁻¹ * u from hu]
    simp
  have h := congrFun hfg (QuotientGroup.mk x⁻¹)
  simp only [coindValues, AddMonoidHom.mk'_apply] at h
  rw [hx, f.2 u, g.2 u, h]

instance finite_coind (B : Rep.{u} k (U : Subgroup G)) [Finite B] :
    Finite (Rep.coind (U : Subgroup G).subtype B) :=
  Finite.of_injective _ (coindValues_injective U B)

theorem card_coind_dvd (B : Rep.{u} k (U : Subgroup G)) [Finite B] :
    Nat.card (Rep.coind (U : Subgroup G).subtype B) ∣ Nat.card B ^ (U : Subgroup G).index := by
  have h := AddSubgroup.card_dvd_of_injective (coindValues U B) (coindValues_injective U B)
  rwa [Nat.card_fun] at h

end Shapiro

end Langlands.ProfiniteCohomology

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

section Coind

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- A function on `G/U` is the restriction of a unique element of the coinduced module. -/
theorem coindValues_surjective (B : Rep.{u} k (U : Subgroup G)) :
    Function.Surjective (coindValues U B) := by
  intro φ
  have hx : ∀ x : G, ∃ h : (U : Subgroup G),
      Quotient.out (QuotientGroup.mk x⁻¹ : G ⧸ (U : Subgroup G)) = x⁻¹ * h :=
    fun x => QuotientGroup.mk_out_eq_mul _ x⁻¹
  choose v hv using hx
  refine ⟨⟨fun x => B.ρ (v x) (φ (QuotientGroup.mk x⁻¹)), fun h x => ?_⟩, ?_⟩
  · have hq : (QuotientGroup.mk ((U : Subgroup G).subtype h * x)⁻¹ : G ⧸ (U : Subgroup G)) =
        QuotientGroup.mk x⁻¹ := by
      rw [mul_inv_rev]
      exact QuotientGroup.mk_mul_of_mem _ (inv_mem h.2)
    have hvx : v ((U : Subgroup G).subtype h * x) = h * v x := by
      have h1 := hv ((U : Subgroup G).subtype h * x)
      rw [hq, hv x, mul_inv_rev, mul_assoc] at h1
      apply Subtype.ext
      have h2 := mul_left_cancel h1
      rw [Subgroup.coe_mul]
      simp only [Subgroup.subtype_apply] at h2 ⊢
      rw [h2, mul_inv_cancel_left]
    change B.ρ (v ((U : Subgroup G).subtype h * x)) (φ (QuotientGroup.mk
      ((U : Subgroup G).subtype h * x)⁻¹)) = B.ρ h (B.ρ (v x) (φ (QuotientGroup.mk x⁻¹)))
    rw [hq, hvx, map_mul, Module.End.mul_apply]
  · funext c
    change B.ρ (v (Quotient.out c)⁻¹) (φ (QuotientGroup.mk (Quotient.out c)⁻¹⁻¹)) = φ c
    have h1 := hv (Quotient.out c)⁻¹
    simp only [inv_inv, QuotientGroup.out_eq'] at h1 ⊢
    have h2 : v (Quotient.out c)⁻¹ = 1 := by
      apply Subtype.ext
      simpa using h1.symm
    rw [h2, map_one, Module.End.one_apply]

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The order of a coinduced module: `|Coind_U^G B| = |B|^[G:U]`. -/
theorem card_coind (B : Rep.{u} k (U : Subgroup G)) [Finite B] [Finite (G ⧸ (U : Subgroup G))] :
    Nat.card (Rep.coind (U : Subgroup G).subtype B) = Nat.card B ^ (U : Subgroup G).index := by
  rw [Nat.card_congr (Equiv.ofBijective _ ⟨coindValues_injective U B,
    coindValues_surjective U B⟩), Nat.card_fun]
  rfl

end Coind

end Langlands.ProfiniteCohomology

end
