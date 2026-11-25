import Langlands.Cohomology.Profinite.Dimension.Basic
import Langlands.Cohomology.Profinite.Duality.DualModule
import Langlands.GaloisCohomology.Field.FiniteLevel
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology
open Polynomial

section Defs

variable (K : Type*) [Field K] (n : ℕ)

def unitsPow : Subgroup Kˣ := (powMonoidHom n : Kˣ →* Kˣ).range

abbrev UnitsModPow : Type _ := Kˣ ⧸ unitsPow K n

variable {K n} in
lemma mem_unitsPow {a : Kˣ} : a ∈ unitsPow K n ↔ ∃ b : Kˣ, b ^ n = a := by
  simp [unitsPow]

lemma UnitsModPow.pow_eq_one (x : UnitsModPow K n) : x ^ n = 1 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact mem_unitsPow.mpr ⟨a, rfl⟩

variable (L : Type*) [Field L] [Algebra K L]

def unitsPowIn : Subgroup Kˣ := (unitsPow L n).comap (Units.map (algebraMap K L : K →* L))

variable {K n L} in
lemma mem_unitsPowIn {a : Kˣ} : a ∈ unitsPowIn K n L ↔ ∃ α : L, α ^ n = algebraMap K L a := by
  simp only [unitsPowIn, Subgroup.mem_comap, mem_unitsPow]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa [Units.ext_iff] using congrArg Units.val hb⟩
  · rintro ⟨α, hα⟩
    by_cases h0 : α = 0
    · have hn : n = 0 := by
        by_contra hn
        rw [h0, zero_pow hn] at hα
        exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm
      subst hn
      refine ⟨1, ?_⟩
      ext
      simpa using hα
    · exact ⟨Units.mk0 α h0, by ext; simpa using hα⟩

lemma unitsPow_le_unitsPowIn : unitsPow K n ≤ unitsPowIn K n L := by
  intro a ha
  obtain ⟨b, rfl⟩ := mem_unitsPow.mp ha
  exact mem_unitsPowIn.mpr ⟨algebraMap K L b, by simp⟩

def kummerGroup : Subgroup (UnitsModPow K n) :=
  (unitsPowIn K n L).map (QuotientGroup.mk' (unitsPow K n))

variable {K n L} in
lemma mk_mem_kummerGroup {a : Kˣ} :
    (a : UnitsModPow K n) ∈ kummerGroup K n L ↔ ∃ α : L, α ^ n = algebraMap K L a := by
  rw [← mem_unitsPowIn]
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp hba)
    have : a = b * c ^ n := by rw [hc]; group
    rw [this]
    exact mul_mem hb (unitsPow_le_unitsPowIn K n L (mem_unitsPow.mpr ⟨c, rfl⟩))
  · intro ha
    exact ⟨a, ha, rfl⟩

noncomputable def toKummerGroup : unitsPowIn K n L →* kummerGroup K n L :=
  ((QuotientGroup.mk' (unitsPow K n)).comp (unitsPowIn K n L).subtype).codRestrict _
    (fun a => Subgroup.mem_map_of_mem _ a.2)

lemma toKummerGroup_surjective : Function.Surjective (toKummerGroup K n L) := by
  rintro ⟨x, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

lemma ker_toKummerGroup :
    (toKummerGroup K n L).ker = (unitsPow K n).subgroupOf (unitsPowIn K n L) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff (N := unitsPow K n)]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

noncomputable def kummerGroupEquiv :
    (unitsPowIn K n L ⧸ (unitsPow K n).subgroupOf (unitsPowIn K n L)) ≃* kummerGroup K n L :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toKummerGroup K n L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toKummerGroup_surjective K n L))

end Defs

section RootsOfUnity

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
variable {L : Type*} [Field L] [Algebra K L]

lemma exists_algebraMap_eq_of_pow_eq_one {x : L} (hx : x ^ n = 1) :
    ∃ ζ : rootsOfUnity n K, algebraMap K L ((ζ : Kˣ) : K) = x := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  obtain ⟨i, -, hi⟩ := (hζ.map_of_injective (algebraMap K L).injective).eq_pow_of_pow_eq_one hx
  refine ⟨⟨(hζ.isUnit (NeZero.ne n)).unit ^ i, ?_⟩, ?_⟩
  · rw [mem_rootsOfUnity', Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← pow_mul, mul_comm,
      pow_mul, hζ.pow_eq_one, one_pow]
  · simpa using hi

lemma algHom_apply_eq_self_of_pow_eq_one {x : L} (hx : x ^ n = 1) (σ : L →ₐ[K] L) :
    σ x = x := by
  obtain ⟨ζ, rfl⟩ := exists_algebraMap_eq_of_pow_eq_one (K := K) hx
  exact σ.commutes _

omit [HasEnoughRootsOfUnity K n] in
lemma ne_zero_of_pow_eq_algebraMap {a : Kˣ} {α : L} (hα : α ^ n = algebraMap K L a) : α ≠ 0 := by
  rintro rfl
  rw [zero_pow (NeZero.ne n)] at hα
  exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm

end RootsOfUnity

section Pairing

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]

lemma exists_kummer_value (σ : Gal(L/K)) (x : kummerGroup K n L) :
    ∃ ζ : rootsOfUnity n K, ∀ a : Kˣ, (a : UnitsModPow K n) = x →
      ∀ α : L, α ^ n = algebraMap K L a → σ α = algebraMap K L ((ζ : Kˣ) : K) * α := by
  obtain ⟨x, a₀, ha₀, rfl⟩ := x
  obtain ⟨α₀, hα₀⟩ := mem_unitsPowIn.mp ha₀
  have hα₀0 : α₀ ≠ 0 := ne_zero_of_pow_eq_algebraMap hα₀
  have hσ : (σ α₀ / α₀) ^ n = 1 := by
    rw [div_pow, ← map_pow, hα₀, AlgEquiv.commutes, div_self]
    exact (map_ne_zero (algebraMap K L)).mpr a₀.ne_zero
  obtain ⟨ζ, hζ⟩ := exists_algebraMap_eq_of_pow_eq_one (K := K) hσ
  refine ⟨ζ, fun a ha α hα => ?_⟩

  obtain ⟨c, hc⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp ha)
  set γ := algebraMap K L (c : K) with hγ
  have hγ0 : γ ≠ 0 := (map_ne_zero (algebraMap K L)).mpr c.ne_zero
  have ha0 : algebraMap K L (a : K) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr a.ne_zero
  have ha' : algebraMap K L (a₀ : K) = algebraMap K L (a : K) * γ ^ n := by
    have h1 : (c : K) ^ n = (a : K)⁻¹ * (a₀ : K) := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
        using congrArg Units.val hc
    have h2 : (a₀ : K) = (a : K) * (c : K) ^ n := by
      rw [h1, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]
    rw [h2, map_mul, map_pow]
  have hη : (α * γ / α₀) ^ n = 1 := by
    rw [div_pow, mul_pow, hα, hα₀, ha']
    exact div_self (mul_ne_zero ha0 (pow_ne_zero _ hγ0))
  have hfix : σ (α * γ / α₀) = α * γ / α₀ :=
    algHom_apply_eq_self_of_pow_eq_one (K := K) hη (σ : L →ₐ[K] L)
  have hσγ : σ γ = γ := σ.commutes _
  have hσα₀ : σ α₀ = algebraMap K L ((ζ : Kˣ) : K) * α₀ := by
    rw [hζ, div_mul_cancel₀ _ hα₀0]
  have hσα₀0 : σ α₀ ≠ 0 := (map_ne_zero σ).mpr hα₀0
  have key : σ α * γ / σ α₀ = α * γ / α₀ := by
    rw [← hfix, map_div₀, map_mul, hσγ]
  calc σ α = (σ α * γ / σ α₀) * (σ α₀ / γ) := by field_simp
    _ = (α * γ / α₀) * (algebraMap K L ((ζ : Kˣ) : K) * α₀ / γ) := by rw [key, hσα₀]
    _ = algebraMap K L ((ζ : Kˣ) : K) * α := by field_simp

noncomputable def kummerPairing (σ : Gal(L/K)) (x : kummerGroup K n L) : rootsOfUnity n K :=
  (exists_kummer_value K n L σ x).choose

variable {K n L}

lemma kummerPairing_spec (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a) :
    σ α = algebraMap K L ((kummerPairing K n L σ x : Kˣ) : K) * α :=
  (exists_kummer_value K n L σ x).choose_spec a ha α hα

lemma kummerPairing_eq_of_apply (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a)
    (ζ : rootsOfUnity n K) (h : σ α = algebraMap K L ((ζ : Kˣ) : K) * α) :
    kummerPairing K n L σ x = ζ := by
  have h' := kummerPairing_spec σ x ha hα
  rw [h] at h'
  have := mul_right_cancel₀ (ne_zero_of_pow_eq_algebraMap hα) h'
  ext
  exact ((algebraMap K L).injective this).symm

lemma kummerPairing_eq_one_iff (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a) :
    kummerPairing K n L σ x = 1 ↔ σ α = α := by
  constructor
  · intro h
    rw [kummerPairing_spec σ x ha hα, h]
    simp
  · intro h
    exact kummerPairing_eq_of_apply σ x ha hα 1 (by rw [h]; simp)

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma exists_rep (x : kummerGroup K n L) :
    ∃ a : Kˣ, (a : UnitsModPow K n) = x ∧ ∃ α : L, α ^ n = algebraMap K L a := by
  obtain ⟨x, a, ha, rfl⟩ := x
  exact ⟨a, rfl, mem_unitsPowIn.mp ha⟩

lemma kummerPairing_mul_left (σ τ : Gal(L/K)) (x : kummerGroup K n L) :
    kummerPairing K n L (σ * τ) x = kummerPairing K n L σ x * kummerPairing K n L τ x := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  apply kummerPairing_eq_of_apply (σ * τ) x ha hα
  rw [AlgEquiv.mul_apply, kummerPairing_spec τ x ha hα, map_mul, AlgEquiv.commutes,
    kummerPairing_spec σ x ha hα]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  ring

lemma kummerPairing_mul_right (σ : Gal(L/K)) (x y : kummerGroup K n L) :
    kummerPairing K n L σ (x * y) = kummerPairing K n L σ x * kummerPairing K n L σ y := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  obtain ⟨b, hb, β, hβ⟩ := exists_rep y
  have hab : ((a * b : Kˣ) : UnitsModPow K n) =
      ((x * y : kummerGroup K n L) : UnitsModPow K n) := by
    rw [QuotientGroup.mk_mul, ha, hb]
    rfl
  have hαβ : (α * β) ^ n = algebraMap K L ((a * b : Kˣ) : K) := by
    rw [mul_pow, hα, hβ, Units.val_mul, map_mul]
  apply kummerPairing_eq_of_apply σ (x * y) hab hαβ
  rw [map_mul, kummerPairing_spec σ x ha hα, kummerPairing_spec σ y hb hβ]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  ring

lemma kummerPairing_one_left (x : kummerGroup K n L) : kummerPairing K n L 1 x = 1 := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  exact (kummerPairing_eq_one_iff 1 x ha hα).mpr rfl

lemma kummerPairing_one_right (σ : Gal(L/K)) : kummerPairing K n L σ 1 = 1 := by
  have h := kummerPairing_mul_right σ (1 : kummerGroup K n L) 1
  rw [mul_one] at h
  exact (mul_eq_left.mp h.symm)

variable (K n L)

noncomputable def kummerPairingLeft : Gal(L/K) →* (kummerGroup K n L →* rootsOfUnity n K) where
  toFun σ :=
    { toFun := kummerPairing K n L σ
      map_one' := kummerPairing_one_right σ
      map_mul' := kummerPairing_mul_right σ }
  map_one' := by ext x : 1; exact kummerPairing_one_left x
  map_mul' σ τ := by ext x : 1; exact kummerPairing_mul_left σ τ x

noncomputable def kummerPairingRight : kummerGroup K n L →* (Gal(L/K) →* rootsOfUnity n K) where
  toFun x :=
    { toFun := fun σ => kummerPairing K n L σ x
      map_one' := kummerPairing_one_left x
      map_mul' := fun σ τ => kummerPairing_mul_left σ τ x }
  map_one' := by ext σ : 1; exact kummerPairing_one_right σ
  map_mul' x y := by ext σ : 1; exact kummerPairing_mul_right σ x y

@[simp] lemma kummerPairingLeft_apply (σ : Gal(L/K)) (x : kummerGroup K n L) :
    kummerPairingLeft K n L σ x = kummerPairing K n L σ x := rfl

@[simp] lemma kummerPairingRight_apply (x : kummerGroup K n L) (σ : Gal(L/K)) :
    kummerPairingRight K n L x σ = kummerPairing K n L σ x := rfl

end Pairing

section Field

variable (K : Type*) [Field K] (n : ℕ)

def kummerField (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup (UnitsModPow K n)) :
    IntermediateField K Ω :=
  IntermediateField.adjoin K
    {α : Ω | ∃ a : Kˣ, (a : UnitsModPow K n) ∈ Δ ∧ α ^ n = algebraMap K Ω a}

end Field

end Langlands.GaloisCohomology
namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology
open CategoryTheory CategoryTheory.Limits

universe u

section General

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem shortComplex_exact_of_forall_exists (S : ShortComplex (Rep.{u} k G))
    (h : ∀ x₂ : S.X₂, S.g.hom x₂ = 0 → ∃ x₁ : S.X₁, S.f.hom x₁ = x₂) : S.Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
    ShortComplex.moduleCat_exact_iff]
  exact h

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem nsmul_id_hom_apply (A : Rep.{u} k G) (m : ℕ) (x : A) : (m • 𝟙 A).hom x = m • x := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, Rep.add_hom, Representation.IntertwiningMap.coe_add,
      Pi.add_apply, ih, succ_nsmul]; rfl

theorem cohomologyMap_zero_zeroIso_inv {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    (f : A ⟶ B) (v : A.ρ.invariants) :
    (coeffMap f 0).hom ((zeroIso A).inv.hom v) =
      (zeroIso B).inv.hom (((Rep.invariantsFunctor k G).map f).hom v) := by
  have h := congrArg (fun φ => φ.hom ((zeroIso A).inv.hom v))
    (cohomologyMap_zero_comp_zeroIso_hom f)
  change (zeroIso B).hom.hom ((coeffMap f 0).hom ((zeroIso A).inv.hom v)) =
    ((Rep.invariantsFunctor k G).map f).hom ((zeroIso A).hom.hom ((zeroIso A).inv.hom v)) at h
  rw [zeroIso_hom_inv_apply] at h
  rw [← h, zeroIso_inv_hom_apply]

section LongExact

variable {S : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃] (hS : S.ShortExact)

theorem exists_δ_zeroIso_inv_eq (h1 : Subsingleton (cohomology S.X₂ 1)) (x : cohomology S.X₁ 1) :
    ∃ v : S.X₃.ρ.invariants, (δ hS 0 1 rfl).hom ((zeroIso S.X₃).inv.hom v) = x := by
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS 0 1 rfl) x
    (h1.elim _ _)
  exact ⟨(zeroIso S.X₃).hom.hom y,
    (congrArg (δ hS 0 1 rfl).hom (zeroIso_inv_hom_apply S.X₃ y)).trans hy⟩

theorem δ_zeroIso_inv_eq_zero_iff (v : S.X₃.ρ.invariants) :
    (δ hS 0 1 rfl).hom ((zeroIso S.X₃).inv.hom v) = 0 ↔
      ∃ w : S.X₂.ρ.invariants, ((Rep.invariantsFunctor k G).map S.g).hom w = v := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hS 0 1 rfl) _ h
    refine ⟨(zeroIso S.X₂).hom.hom z, ?_⟩
    have e := congrArg (fun φ => φ.hom z) (cohomologyMap_zero_comp_zeroIso_hom S.g)
    change (zeroIso S.X₃).hom.hom ((coeffMap S.g 0).hom z) =
      ((Rep.invariantsFunctor k G).map S.g).hom ((zeroIso S.X₂).hom.hom z) at e
    rw [← e]
    exact (congrArg (zeroIso S.X₃).hom.hom hz).trans (zeroIso_hom_inv_apply S.X₃ v)
  · rintro ⟨w, rfl⟩
    rw [← cohomologyMap_zero_zeroIso_inv]
    exact congrArg (fun φ => φ.hom ((zeroIso S.X₂).inv.hom w)) (comp_δ hS 0 1 rfl)

include hS in

theorem cohomologyMap_f_injective_of_subsingleton (i : ℕ)
    (h : Subsingleton (cohomology S.X₃ i)) : Function.Injective (coeffMap S.f (i + 1)).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS i (i + 1) rfl) x
    hx
  rw [← hy, Subsingleton.elim y 0]
  exact map_zero _

include hS in

theorem exists_cohomologyMap_f_eq (i : ℕ) (y : cohomology S.X₂ i)
    (hy : (coeffMap S.g i).hom y = 0) : ∃ x, (coeffMap S.f i).hom x = y :=
  (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS i) y hy

theorem cohomologyMap_g_cohomologyMap_f_apply (i : ℕ) (x : cohomology S.X₁ i) :
    (coeffMap S.g i).hom ((coeffMap S.f i).hom x) = 0 :=
  congrArg (fun φ => φ.hom x) (map_f_comp_g (S := S) i)

end LongExact

end General

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

section H0Units

def unitsToInvariants : Additive Kˣ →+ (unitsModule K L).ρ.invariants where
  toFun a := ⟨Additive.ofMul (Units.map (algebraMap K L : K →* L) (Additive.toMul a)), fun σ =>
    Additive.toMul.injective (Units.ext (σ.commutes _))⟩
  map_zero' := Subtype.ext (Additive.toMul.injective (Units.ext (map_one _)))
  map_add' _ _ := Subtype.ext (Additive.toMul.injective (Units.ext (map_mul _ _ _)))

@[simp]
theorem coe_unitsToInvariants_apply (a : Additive Kˣ) :
    ((Additive.toMul (α := Lˣ) (unitsToInvariants K L a).1 : Lˣ) : L) =
      algebraMap K L (Additive.toMul a : Kˣ) :=
  rfl

theorem unitsToInvariants_injective : Function.Injective (unitsToInvariants K L) := by
  intro a b h
  apply Additive.toMul.injective
  apply Units.ext
  exact (algebraMap K L).injective (congrArg (fun v : (unitsModule K L).ρ.invariants =>
    ((Additive.toMul (α := Lˣ) v.1 : Lˣ) : L)) h)

theorem unitsToInvariants_surjective [IsGalois K L] :
    Function.Surjective (unitsToInvariants K L) := by
  intro v
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    ((Additive.toMul (α := Lˣ) v.1 : Lˣ) : L)).2 fun σ =>
      congrArg (fun w : Additive Lˣ => ((Additive.toMul w : Lˣ) : L)) (v.2 σ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Additive.toMul (α := Lˣ) v.1).ne_zero ha.symm
  exact ⟨Additive.ofMul (Units.mk0 a ha0),
    Subtype.ext (Additive.toMul.injective (Units.ext ha))⟩

noncomputable def unitsInvariantsEquiv [IsGalois K L] :
    Additive Kˣ ≃+ (unitsModule K L).ρ.invariants :=
  AddEquiv.ofBijective (unitsToInvariants K L)
    ⟨unitsToInvariants_injective K L, unitsToInvariants_surjective K L⟩

@[simp]
theorem unitsInvariantsEquiv_apply [IsGalois K L] (a : Additive Kˣ) :
    unitsInvariantsEquiv K L a = unitsToInvariants K L a :=
  rfl

theorem invariantsFunctor_map_nsmul_unitsToInvariants (n : ℕ) (a : Additive Kˣ) :
    ((Rep.invariantsFunctor (ULift.{u} ℤ) Gal(L/K)).map (n • 𝟙 (unitsModule K L))).hom
        (unitsToInvariants K L a) = unitsToInvariants K L (n • a) := by
  apply Subtype.ext
  change (n • 𝟙 (unitsModule K L)).hom (unitsToInvariants K L a).1 = _
  rw [nsmul_id_hom_apply, map_nsmul]
  rfl

end H0Units

section Sequence

variable (n : ℕ)

noncomputable def kummerSequence : ShortComplex (Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :=
  ShortComplex.mk (rootsOfUnityToUnits K L n) (n • 𝟙 (unitsModule K L)) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change n • Additive.ofMul
      (((Additive.toMul (α := rootsOfUnity n L) x : rootsOfUnity n L) : Lˣ)) = (0 : Additive Lˣ)
    rw [← ofMul_pow, (mem_rootsOfUnity n _).1 (Additive.toMul (α := rootsOfUnity n L) x).2,
      ofMul_one])

variable {K L}

theorem kummerSequence_exact : (kummerSequence K L n).Exact := by
  refine shortComplex_exact_of_forall_exists _ fun x hx => ?_
  have hx' : n • (x : Additive Lˣ) = 0 := (nsmul_id_hom_apply (unitsModule K L) n x).symm.trans hx
  have h : (Additive.toMul (α := Lˣ) x) ^ n = 1 := congrArg Additive.toMul hx'
  exact ⟨(Additive.ofMul (⟨Additive.toMul (α := Lˣ) x, (mem_rootsOfUnity n _).2 h⟩ :
    rootsOfUnity n L) : Additive (rootsOfUnity n L)), rfl⟩

theorem rootsOfUnityToUnits_injective :
    Function.Injective (rootsOfUnityToUnits K L n).hom := fun _ _ h =>
  Additive.toMul.injective (Subtype.ext (congrArg (Additive.toMul (α := Lˣ)) h))

theorem nsmul_id_unitsModule_surjective [IsSepClosed L] (hn : (n : L) ≠ 0) :
    Function.Surjective (n • 𝟙 (unitsModule K L)).hom := by
  have : NeZero (n : L) := ⟨hn⟩
  intro y
  obtain ⟨z, hz⟩ := IsSepClosed.exists_pow_nat_eq ((Additive.toMul (α := Lˣ) y : Lˣ) : L) n
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0] at hz
    exact (Additive.toMul (α := Lˣ) y).ne_zero hz.symm
  refine ⟨(Additive.ofMul (Units.mk0 z hz0) : Additive Lˣ), ?_⟩
  refine (nsmul_id_hom_apply (unitsModule K L) n _).trans ?_
  apply Additive.toMul.injective
  apply Units.ext
  change ((Units.mk0 z hz0 ^ n : Lˣ) : L) = _
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact hz

theorem kummerSequence_shortExact_of_ne_zero [IsSepClosed L] (hn : (n : L) ≠ 0) :
    (kummerSequence K L n).ShortExact where
  exact := kummerSequence_exact n
  mono_f := (Rep.mono_iff_injective _).2 (rootsOfUnityToUnits_injective n)
  epi_g := (Rep.epi_iff_surjective _).2 (nsmul_id_unitsModule_surjective n hn)

theorem kummerSequence_shortExact [IsSepClosure K L] (hn : (n : K) ≠ 0) :
    (kummerSequence K L n).ShortExact := by
  have : IsSepClosed L := IsSepClosure.sep_closed K
  refine kummerSequence_shortExact_of_ne_zero n ?_
  rw [← map_natCast (algebraMap K L)]
  exact (map_ne_zero (algebraMap K L)).2 hn

variable [Algebra.IsIntegral K L]

instance isSmoothRep_kummerSequence_X₁ : IsSmoothRep (kummerSequence K L n).X₁ :=
  inferInstanceAs (IsSmoothRep (rootsOfUnityModule K L n))

instance isSmoothRep_kummerSequence_X₂ : IsSmoothRep (kummerSequence K L n).X₂ :=
  inferInstanceAs (IsSmoothRep (unitsModule K L))

instance isSmoothRep_kummerSequence_X₃ : IsSmoothRep (kummerSequence K L n).X₃ :=
  inferInstanceAs (IsSmoothRep (unitsModule K L))

end Sequence

section H1

variable {K L} [IsSepClosure K L] {n : ℕ} (hn : (n : K) ≠ 0)

noncomputable def kummerH1Hom : Additive Kˣ →+ cohomology (rootsOfUnityModule K L n) 1 :=
  ((δ (kummerSequence_shortExact n hn) 0 1 rfl).hom.toAddMonoidHom.comp
    (zeroIso (kummerSequence K L n).X₃).inv.hom.toAddMonoidHom).comp (unitsToInvariants K L)

include hn in
theorem kummerH1Hom_surjective : Function.Surjective (kummerH1Hom (L := L) hn) := by
  intro x
  obtain ⟨v, hv⟩ := exists_δ_zeroIso_inv_eq (kummerSequence_shortExact (L := L) n hn)
    (subsingleton_cohomology_one_unitsModule (K := K) (L := L)) x
  obtain ⟨a, ha⟩ := unitsToInvariants_surjective K L v
  exact ⟨a, (congrArg (fun w => (δ (kummerSequence_shortExact (L := L) n hn) 0 1 rfl).hom
    ((zeroIso (kummerSequence K L n).X₃).inv.hom w)) ha).trans hv⟩

include hn in
theorem kummerH1Hom_eq_zero_iff (a : Additive Kˣ) :
    kummerH1Hom (L := L) hn a = 0 ↔ Additive.toMul a ∈ unitsPow K n := by
  refine (δ_zeroIso_inv_eq_zero_iff (kummerSequence_shortExact (L := L) n hn)
    (unitsToInvariants K L a)).trans ?_
  rw [mem_unitsPow]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, hb⟩ := unitsToInvariants_surjective K L w
    have h : unitsToInvariants K L (n • b) = unitsToInvariants K L a :=
      (invariantsFunctor_map_nsmul_unitsToInvariants K L n b).symm.trans
        ((congrArg (fun w => ((Rep.invariantsFunctor (ULift.{u} ℤ) Gal(L/K)).map
          (n • 𝟙 (unitsModule K L))).hom w) hb).trans hw)
    exact ⟨Additive.toMul b, congrArg Additive.toMul (unitsToInvariants_injective K L h)⟩
  · rintro ⟨b, hb⟩
    refine ⟨unitsToInvariants K L (Additive.ofMul b), ?_⟩
    refine (invariantsFunctor_map_nsmul_unitsToInvariants K L n _).trans ?_
    congr 1

noncomputable def kummerH1QuotHom : UnitsModPow K n →* Multiplicative
    (cohomology (rootsOfUnityModule K L n) 1) :=
  QuotientGroup.lift (unitsPow K n) (kummerH1Hom (L := L) hn).toMultiplicativeRight fun a ha =>
    (MonoidHom.mem_ker).2 (congrArg Multiplicative.ofAdd
      ((kummerH1Hom_eq_zero_iff hn (Additive.ofMul a)).2 ha))

include hn in
theorem kummerH1QuotHom_bijective : Function.Bijective (kummerH1QuotHom (L := L) hn) := by
  constructor
  · refine (injective_iff_map_eq_one _).2 fun q hq => ?_
    induction q using QuotientGroup.induction_on with
    | H a =>
      have h : kummerH1Hom (L := L) hn (Additive.ofMul a) = 0 := congrArg Multiplicative.toAdd hq
      exact (QuotientGroup.eq_one_iff a).2 ((kummerH1Hom_eq_zero_iff hn _).1 h)
  · intro y
    obtain ⟨a, ha⟩ := kummerH1Hom_surjective (L := L) hn (Multiplicative.toAdd y)
    exact ⟨(Additive.toMul a : Kˣ), congrArg Multiplicative.ofAdd ha⟩

noncomputable def kummerEquiv :
    cohomology (rootsOfUnityModule K L n) 1 ≃+ Additive (UnitsModPow K n) :=
  (MulEquiv.toAdditiveLeft (MulEquiv.ofBijective _ (kummerH1QuotHom_bijective (L := L) hn))).symm

end H1

section H2

variable {K L} [IsGalois K L]

noncomputable def galoisBrauerGroupTorsion (n : ℕ) : AddSubgroup (galoisBrauerGroup K L) :=
  (nsmulAddMonoidHom (α := galoisBrauerGroup K L) n).ker

theorem cohomologyMap_kummerSequence_g_apply (n i : ℕ) (y : cohomology (unitsModule K L) i) :
    (coeffMap (kummerSequence K L n).g i).hom y = n • y :=
  cohomologyMap_nsmul_id_apply (unitsModule K L) n i y

variable [IsSepClosure K L] {n : ℕ} (hn : (n : K) ≠ 0)

noncomputable def kummerH2Hom :
    cohomology (rootsOfUnityModule K L n) 2 →+ galoisBrauerGroupTorsion (K := K) (L := L) n :=
  AddMonoidHom.codRestrict (coeffMap (kummerSequence K L n).f 2).hom.toAddMonoidHom _
    fun x => (cohomologyMap_kummerSequence_g_apply n 2 _).symm.trans
      (cohomologyMap_g_cohomologyMap_f_apply 2 x)

include hn in
theorem kummerH2Hom_bijective : Function.Bijective (kummerH2Hom (K := K) (L := L) (n := n)) := by
  have hS := kummerSequence_shortExact (L := L) n hn
  constructor
  · intro x y h
    exact cohomologyMap_f_injective_of_subsingleton hS 1
      (subsingleton_cohomology_one_unitsModule (K := K) (L := L)) (congrArg Subtype.val h)
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := exists_cohomologyMap_f_eq hS 2 y
      ((cohomologyMap_kummerSequence_g_apply n 2 y).trans hy)
    exact ⟨x, Subtype.ext hx⟩

noncomputable def kummerH2Equiv :
    cohomology (rootsOfUnityModule K L n) 2 ≃+ galoisBrauerGroupTorsion (K := K) (L := L) n :=
  AddEquiv.ofBijective _ (kummerH2Hom_bijective hn)

end H2

end Langlands.GaloisCohomology